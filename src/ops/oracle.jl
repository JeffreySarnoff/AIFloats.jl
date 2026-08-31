# the ω-semantics catalog: rigorous evaluation of every operation's defined
# result. Never on the hot path.
#
# Three result kinds reach _finish (ops/scalar.jl):
#   - an exact carrier value (Float64/Float128/BigFloat)   → project directly
#   - Enclosure(f)  with f(prec) -> (lo, hi) directed MPFR → project_interval
# Special-value rows are written out explicitly even where the substrate
# coincides: the rows are the spec, not an optimization.
#
# Two switchable performance layers sit over the rigorous MPFR ladder, each
# pinned equal to the ladder-only path by test/test-fastpaths.jl:
#   FAST_ARITH     — Group A: direct exactness PROOFS on Float128 (twosum128 /
#                    fma residual) before escalating to exact BigFloat, and the
#                    wide-spread `Sticky` escape past _STICKY_MIN binades;
#   FAST_ENCLOSURE — Group B/quotients: an eager Float64 estimate (faithful
#                    libm, envelope 2^-45) then a Float128 estimate (envelope
#                    2^-90), each accepted only when the two-sided sticky
#                    projection of its envelope agrees on one code point.
# Disabling either costs speed, never correctness.
const FAST_ARITH = Ref(true)
const FAST_ENCLOSURE = Ref(true)

"""
    Enclosure(f[, fq, yd])

A deferred enclosure of a true value. `f(prec)` returns directed MPFR
endpoints `(lo, hi)` with the true value in `[lo, hi]` — the rigorous ladder.
`fq` (or `nothing`) is a zero-argument Float128 estimator with
`|truth − fq()| ≤ |fq()|·2^-90`; `yd` (NaN when absent) a faithful Float64
estimate with `|truth − yd| ≤ |yd|·2^-45`. Both are structurally Float64-tier:
built only for Float64 operands. Not exported.
"""
struct Enclosure{F, G}
    f::F
    fq::G
    yd::Float64
end
Enclosure(f) = Enclosure(f, nothing, NaN)
const _F128_RELEXP = -90            # envelope exponent: E = |y|·2^-90
const _F64_RELEXP  = -45            # Float64 envelope: E = |y|·2^-45 (≥ 2^7 over faithful libm)
const _F64_MINNORMISH = 6.7e-290    # ≈ 2^-960: keep the relative model clear of subnormals
# 2^-915: above this, a nonzero exact FMA residual cannot underflow, so
# `fma(x, y, -p) == 0` proves `p == x·y` (derivation at the use site)
const _FMA_EXACT_FLOOR = ldexp(1.0, -915)

# the Float64-tier estimators. Built only for Float64 operands; a Float128 or
# Dyadic operand may not survive narrowing, so the wide rows drop both and hand
# the ladder the whole job. `fq` is deferred and guarded (a generic closure may
# lack a Float128 method inside); `yd` is eager and guarded the same way.
@inline _fq1(f, x::Float64) = () -> f(Float128(x))
@inline _fq1(f, x) = nothing
@inline _fq2(f, x::Float64, y::Float64) = () -> f(Float128(x), Float128(y))
@inline _fq2(f, x, y) = nothing
@inline _yd1(f, x::Float64) = _f64guard(f, x)
@inline _yd1(f, x) = NaN
@inline _yd2(f, x::Float64, y::Float64) = _f64guard(f, x, y)
@inline _yd2(f, x, y) = NaN
@inline function _f64guard(f, xs...)
    try
        Float64(f(xs...))
    catch
        NaN
    end
end
@inline function _try128(fq)
    try
        Float128(fq())
    catch
        Float128(NaN)
    end
end

# exact BigFloat image of any carrier value, at its own width
_exactbig(x::Float64)  = setprecision(() -> BigFloat(x), BigFloat, 64)
_exactbig(x::Float128) = setprecision(() -> BigFloat(x), BigFloat, 128)
_exactbig(x::BigFloat) = x
_exactbig(x::Dyadic)   = BigFloat(x)                    # exact at its own width

# a value whose true tail lies strictly below its last bit in a known
# direction: the rung-3 Add's protocol past the alignment band. Sound because
# DYADIC_ALIGN_MAX (94) > P + N + 2 for every P ≤ 16, N ≤ 60 — the tail is
# below both the finest stochastic sub-grid unit and any rounding threshold.
struct Sticky{T<:CarrierValue}
    v::T
    sgn::Int
end

_sigfloor(xs...) = maximum(x -> precision(_exactbig(x)), xs)
_ladderprec(prec::Int, xs...) = max(prec, _sigfloor(xs...) + 8)

# directed one-argument MPFR enclosure, with the two eager stages for Float64.
#
# @inline is not cosmetic here. Unannotated, these builders were NOT inlined
# for any `f` that can throw (log, sin, cos, log2, …), so the three closures
# were boxed and the Enclosure heap-allocated even when stage 1 of `_finish`
# decided immediately and the ladder was never called: 236 ns and 7
# allocations for Log against 22 ns and none for Exp, whose libm row happens
# to inline. Inlined, the Enclosure stays in registers and the whole Group B
# lands at Exp's cost (implmentplan.md Step 5).
@inline _mpfr1(f, x) = Enclosure(_ladder1(f, x), _fq1(f, x), _yd1(f, x))
_ladder1(f, x) = prec -> setprecision(BigFloat, _ladderprec(prec, x)) do
    b = _exactbig(x)
    (setrounding(() -> f(b), BigFloat, RoundDown),
     setrounding(() -> f(b), BigFloat, RoundUp))
end

@inline @inline _mpfr2(f, x, y) = Enclosure(_ladder2(f, x, y), _fq2(f, x, y), _yd2(f, x, y))

# ---- the correctly-rounded variants -----------------------------------------
# MPFR computes every one of its primitives with CORRECT rounding, so a single
# round-to-nearest evaluation r satisfies |true − r| ≤ ½ulp(r) and
# [prevfloat(r), nextfloat(r)] strictly contains the true value. One MPFR call
# and two cheap steps replace two directed calls plus two `setrounding`
# round-trips: measured on Exp at rung 1, 1614 ns / 47 allocs → 793 / 26; at
# rung 2, 2205 → 1097. The enclosure is exactly 2 ulps wide instead of 1, which
# is nothing against a ≤ 16-bit grid — 97.6% of enclosures still resolve on the
# first rung.
#
# THE PRECONDITION IS `f` BEING ONE MPFR PRIMITIVE, AND IT IS NOT CHECKABLE
# HERE. A composite closure rounds more than once, its error can exceed ½ulp,
# and a one-ulp widening would then be a guess wearing a proof's clothes. Every
# use is therefore an explicit opt-in at the call site, and `Softplus`
# (`b + log1p(exp(-b))`) keeps the directed pair above for exactly this reason.
# `test-ops.jl` pins the containment property itself — that the nearest-based
# enclosure contains the directed one — rather than only its usual consequence.
#
# This is also precisely the guarantee libquadmath does NOT publish for
# binary128, which is why the Float128 estimators stay deferred.
# FIRST RUNG ONLY, and that restriction is load-bearing rather than cautious.
# [prevfloat(r), nextfloat(r)] is always two ulps wide and NEVER collapses to a
# point, but `_project_interval` detects an exactly-representable result by the
# directed pair coming back equal. Take that away and a value landing exactly on
# a grid point under a directed mode straddles at every precision: the ladder
# escalates forever and dies at the cap. That is not hypothetical — it is what
# the end-to-end differential produced for Exp on Binary{16,5,SIGNED,EXTENDED}
# under RTP_SF, after the containment property alone had tested clean.
#
# So the cheap enclosure serves the ~97.6% of cases that resolve on rung one,
# and every escalation falls back to the rigorous directed pair, which is
# unchanged and still the reference.
@inline function _ladder1_cr(f, x)
    prec -> prec <= IV_FIRST_RUNG ?
        setprecision(BigFloat, _ladderprec(prec, x)) do
            r = f(_exactbig(x)); (prevfloat(r), nextfloat(r))
        end :
        _ladder1(f, x)(prec)
end
@inline function _ladder2_cr(f, x, y)
    prec -> prec <= IV_FIRST_RUNG ?
        setprecision(BigFloat, _ladderprec(prec, x, y)) do
            r = f(_exactbig(x), _exactbig(y)); (prevfloat(r), nextfloat(r))
        end :
        _ladder2(f, x, y)(prec)
end
@inline _mpfr1_cr(f, x) = Enclosure(_ladder1_cr(f, x), _fq1(f, x), _yd1(f, x))
@inline _mpfr2_cr(f, x, y) = Enclosure(_ladder2_cr(f, x, y), _fq2(f, x, y), _yd2(f, x, y))
_ladder2(f, x, y) = prec -> setprecision(BigFloat, _ladderprec(prec, x, y)) do
    bx, by = _exactbig(x), _exactbig(y)
    (setrounding(() -> f(bx, by), BigFloat, RoundDown),
     setrounding(() -> f(bx, by), BigFloat, RoundUp))
end

# π-scaled evaluation: g(π·x) with the π rounding folded into the enclosure.
# Valid absent an interior extremum of g on the tiny m-interval — the
# quarter-integer inputs where extrema/rational values sit are peeled by the
# callers (Niven: the only rational values of the π-trig functions on dyadic
# arguments occur at quarter-integers).
@inline _mpfr_pitrig(g, r; yd::Float64 = NaN) = Enclosure(prec -> setprecision(BigFloat, _ladderprec(prec, r)) do
    br = _exactbig(r)
    ml = setrounding(() -> BigFloat(π) * br, BigFloat, RoundDown)
    mh = setrounding(() -> BigFloat(π) * br, BigFloat, RoundUp)
    a1 = setrounding(() -> g(ml), BigFloat, RoundDown)
    a2 = setrounding(() -> g(mh), BigFloat, RoundDown)
    b1 = setrounding(() -> g(ml), BigFloat, RoundUp)
    b2 = setrounding(() -> g(mh), BigFloat, RoundUp)
    (min(a1, a2), max(b1, b2))
end, _fq1(v -> g(Float128(π) * v), r), yd)

# g(x)/π, sign-aware in the denominator direction
@inline _mpfr_divpi(g, x) = Enclosure(_ladder_divpi(g, x), _fq1(v -> g(v) / Float128(π), x), _yd1(v -> g(v) / π, x))
_ladder_divpi(g, x) = prec -> setprecision(BigFloat, _ladderprec(prec, x)) do
    bx = _exactbig(x)
    lo = setrounding(BigFloat, RoundDown) do
        gl = g(bx)
        gl / setrounding(() -> BigFloat(π), BigFloat, gl >= 0 ? RoundUp : RoundDown)
    end
    hi = setrounding(BigFloat, RoundUp) do
        gh = g(bx)
        gh / setrounding(() -> BigFloat(π), BigFloat, gh >= 0 ? RoundDown : RoundUp)
    end
    (lo, hi)
end

# ---- Group A: exact arithmetic ---------------------------------------------
# Float64 fast case by error-free transform; anything inexact or non-Float64
# escalates to exact BigFloat at derived precision. Exactness by construction,
# never by width assumption.

@inline function _twosum(a::Float64, b::Float64)
    s = a + b
    bb = s - a
    (s, (a - (s - bb)) + (b - bb))
end

_bigprec2(x, y) = _sigfloor(x, y) + abs(exponent_or0(x) - exponent_or0(y)) + 8
exponent_or0(x) = (isfinite(x) && !iszero(x)) ? exponent(x) : 0

function _exact_add(x, y)
    setprecision(BigFloat, max(64, _bigprec2(x, y))) do
        _exactbig(x) + _exactbig(y)
    end
end
function _exact_mul(x, y)
    setprecision(BigFloat, max(64, 2 * _sigfloor(x, y) + 8)) do
        _exactbig(x) * _exactbig(y)
    end
end
function _exact_fma(x, y, z)
    setprecision(BigFloat,
        max(64, 2 * _sigfloor(x, y) + _sigfloor(z) +
            abs(exponent_or0(x) + exponent_or0(y) - exponent_or0(z)) + 16)) do
        _exactbig(x) * _exactbig(y) + _exactbig(z)
    end
end
function _exact_sum3(x, y, z)
    lo = min(exponent_or0(x), exponent_or0(y), exponent_or0(z))
    hi = max(exponent_or0(x), exponent_or0(y), exponent_or0(z))
    setprecision(BigFloat, max(64, (hi - lo) + _sigfloor(x, y, z) + 16)) do
        (_exactbig(x) + _exactbig(y)) + _exactbig(z)
    end
end

# ---- the fast layers' primitives --------------------------------------------
# Float128 twin of _twosum (IEEE-CR add, so the Knuth transform is exact)
@inline function _twosum128(a::Float128, b::Float128)
    s = a + b
    bb = s - a
    (s, (a - (s - bb)) + (b - bb))
end
# the sticky escape's second premise: the neglected tail must lie below the
# finest stochastic sub-grid unit, 2^(e_head − (P−1) − N). Neither P nor N is
# visible here, so the grid's maxima bound it: (16 − 1) + 60 + 2.
const _STICKY_MIN = 77
@inline _expdiff(a, b) = abs(exponent(a) - exponent(b))
@inline function _span3(x, y, z)
    lo = typemax(Int); hi = typemin(Int)
    for v in (x, y, z)
        iszero(v) && continue
        e = exponent(v)
        lo = min(lo, e); hi = max(hi, e)
    end
    hi - lo
end
# two terms bit-disjoint by > _STICKY_MIN binades: the larger is the head and
# exact; the smaller contributes only its sign
@inline _sum_wide(a, b) =
    abs(a) >= abs(b) ? Sticky(a, signbit(b) ? -1 : 1) : Sticky(b, signbit(a) ? -1 : 1)
# three terms spanning past the band: distill exact Float128 terms until the
# head is fl(Σ) up to its own lsb and the residual has a determinable sign
function _faa_wide(x::Float128, y::Float128, z::Float128)
    v1, v2, v3 = x, y, z
    for _ in 1:6
        if abs(v2) < abs(v3); v2, v3 = v3, v2; end
        if abs(v1) < abs(v2); v1, v2 = v2, v1; end
        if abs(v2) < abs(v3); v2, v3 = v3, v2; end
        t, tt = _twosum128(v2, v3)
        s, e  = _twosum128(v1, t)
        v1, v2, v3 = s, e, tt
        (iszero(v2) && iszero(v3)) && return v1                        # exact
        iszero(v1) && continue
        if iszero(v3)
            return Sticky(v1, signbit(v2) ? -1 : 1)
        elseif iszero(v2)
            abs(v3) < ldexp(one(Float128), exponent(v1) - 112) &&
                return Sticky(v1, signbit(v3) ? -1 : 1)
        elseif abs(v3) < abs(v2)
            return Sticky(v1, signbit(v2) ? -1 : 1)
        end
    end
    _exact_sum3(x, y, z)
end

function ωeval(::Val{:Add}, x::Float64, y::Float64)
    (isnan(x) | isnan(y)) && return NaN
    if isinf(x) || isinf(y)
        (isinf(x) && isinf(y) && x != y) && return NaN     # ∞ + (−∞)
        return isinf(x) ? x : y
    end
    s, e = _twosum(x, y)
    e == 0.0 && return iszero(s) ? 0.0 : s
    FAST_ARITH[] || return _exact_add(x, y)
    s2, e2 = _twosum128(Float128(x), Float128(y))
    iszero(e2) && return s2                                  # exact in Float128 (proof)
    _expdiff(x, y) >= _STICKY_MIN && return _sum_wide(x, y)
    _exact_add(x, y)
end
# rung 2: the same shape one carrier up
function ωeval(::Val{:Add}, x::Float128, y::Float128)
    (isnan(x) | isnan(y)) && return _cnan(Float128)
    if isinf(x) || isinf(y)
        (isinf(x) && isinf(y) && x != y) && return _cnan(Float128)
        return isinf(x) ? x : y
    end
    FAST_ARITH[] || return _exact_add(x, y)
    s, e = _twosum128(x, y)
    iszero(e) && return iszero(s) ? zero(Float128) : s
    _expdiff(x, y) >= _STICKY_MIN && return _sum_wide(x, y)
    _exact_add(x, y)
end
ωeval(::Val{:Add}, x, y) = _ωadd_wide(x, y)
function _ωadd_wide(x, y)
    (isnan(x) | isnan(y)) && return _cnan(BigFloat)
    if isinf(x) || isinf(y)
        (isinf(x) && isinf(y) && signbit(x) != signbit(y)) && return _cnan(BigFloat)
        return isinf(x) ? _exactbig(x) : _exactbig(y)
    end
    _exact_add(x, y)
end

ωeval(::Val{:Subtract}, x, y) = ωeval(Val(:Add), x, _negate(y))
_negate(y) = -y

function ωeval(::Val{:Multiply}, x::Float64, y::Float64)
    (isnan(x) | isnan(y)) && return NaN
    if isinf(x) || isinf(y)
        (iszero(x) | iszero(y)) && return NaN              # 0 · ∞
        return copysign(Inf, sign(x) * sign(y))
    end
    (iszero(x) | iszero(y)) && return 0.0
    p = x * y
    fma(x, y, -p) == 0.0 && isfinite(p) && !iszero(p) && return p
    FAST_ARITH[] || return _exact_mul(x, y)
    Float128(x) * Float128(y)                               # 53 + 53 ≤ 113: exact
end
function ωeval(::Val{:Multiply}, x::Float128, y::Float128)
    (isnan(x) | isnan(y)) && return _cnan(Float128)
    if isinf(x) || isinf(y)
        (iszero(x) | iszero(y)) && return _cnan(Float128)
        return (signbit(x) ⊻ signbit(y)) ? _cninf(Float128) : _cinf(Float128)
    end
    (iszero(x) | iszero(y)) && return _czero(Float128)
    FAST_ARITH[] || return _exact_mul(x, y)
    p = x * y
    (isfinite(p) && !iszero(p) && fma(x, y, -p) == 0) && return p
    _exact_mul(x, y)
end
function ωeval(::Val{:Multiply}, x, y)
    (isnan(x) | isnan(y)) && return _cnan(BigFloat)
    if isinf(x) || isinf(y)
        (iszero(x) | iszero(y)) && return _cnan(BigFloat)
        return (signbit(x) ⊻ signbit(y)) ? _cninf(BigFloat) : _cinf(BigFloat)
    end
    (iszero(x) | iszero(y)) && return _czero(BigFloat)
    _exact_mul(x, y)
end

function ωeval(::Val{:FMA}, x, y, z)
    (isnan(x) | isnan(y) | isnan(z)) && return _cnan(BigFloat)
    p = ωeval(Val(:Multiply), x, y)                        # exact or ±Inf/NaN
    isnan(p) && return _cnan(BigFloat)
    ωeval(Val(:Add), p, z)
end
# rungs 1–2: the exact product lives in Float128 (≤ 106 bits from Float64
# factors; fma-certified from Float128 ones), then one exact-or-sticky add
function ωeval(::Val{:FMA}, x::F, y::F, z::F) where {F<:Union{Float64, Float128}}
    (isnan(x) | isnan(y) | isnan(z)) && return _cnan(F)
    if isinf(x) || isinf(y)
        (iszero(x) | iszero(y)) && return _cnan(F)
        pinf = (signbit(x) ⊻ signbit(y)) ? _cninf(F) : _cinf(F)
        (isinf(z) && z != pinf) && return _cnan(F)
        return pinf
    end
    isinf(z) && return z
    (iszero(x) | iszero(y)) && return iszero(z) ? _czero(F) : z
    FAST_ARITH[] || return _exact_fma(x, y, z)
    if F === Float64
        # the product is very often exact ALREADY in Float64 (small formats
        # multiply few significant bits); fma certifies it, and then x·y + z is
        # just an exact two-operand sum, which Add's own cascade resolves with
        # the same proofs. Widening every FMA to Float128 first cost 452 ns
        # where Add costs 9 (implmentplan.md Step 4).
        #
        # The magnitude floor is NOT belt-and-braces. The residual
        # d = x·y − p is nonzero ⇒ |d| ≥ |x·y|·2^-106 (an exact product of two
        # Float64s carries ≤ 106 significant bits). Only when that bound sits
        # at or above floatmin is `fma(x, y, -p) == 0` a PROOF of exactness —
        # below it the residual can itself underflow to zero and certify an
        # inexact product. |p| ≥ 2^-915 gives |d| ≥ 2^-1022 = floatmin with
        # margin. Every rung-1 datum product clears this by ~130 binades
        # (a rung-1 format has 2B ≤ 1024 and P ≤ 16), so the floor costs
        # nothing in practice and makes the peel unconditionally sound.
        p64 = x * y
        if isfinite(p64) && abs(p64) >= _FMA_EXACT_FLOOR && fma(x, y, -p64) == 0.0
            return ωeval(Val(:Add), p64, z)
        end
    end
    x128, y128, z128 = Float128(x), Float128(y), Float128(z)
    p = x128 * y128
    (isfinite(p) && fma(x128, y128, -p) == 0) || return _exact_fma(x, y, z)
    s, e = _twosum128(p, z128)
    iszero(e) && return iszero(s) ? zero(Float128) : s
    (iszero(z128) || _expdiff(p, z128) >= _STICKY_MIN) && return _sum_wide(p, z128)
    _exact_fma(x, y, z)
end

function ωeval(::Val{:FAA}, x, y, z)
    (isnan(x) | isnan(y) | isnan(z)) && return _cnan(BigFloat)
    infs = count(isinf, (x, y, z))
    if infs > 0
        pos = any(v -> isinf(v) && !signbit(v), (x, y, z))
        neg = any(v -> isinf(v) && signbit(v), (x, y, z))
        (pos && neg) && return _cnan(BigFloat)
        return pos ? _cinf(BigFloat) : _cninf(BigFloat)
    end
    _exact_sum3(x, y, z)
end
# The same peel as FMA's, and cheaper to justify. Knuth's two-sum is EXACT for
# all finite inputs — the error term of a sum is always representable,
# subnormals included — so unlike the two-product in FMA there is no residual
# that can underflow and no magnitude floor is needed. Both error terms zero ⇒
# x+y == s1 and s1+z == s2, hence x+y+z == s2 exactly. Overflow poisons e1/e2
# with NaN and `iszero` is false there, so the guard covers it too.
#
# Written as a DISPATCHED pair rather than an `F === Float64` test inside the
# shared method: a runtime type test does not narrow the argument types, so the
# Float128 instantiation would still appear to call the Float64-only `_twosum`
# and JET reports the unreachable MethodError (it did — this is why the shape
# differs from the FMA peel, whose helpers all have Float128 methods).
@inline function _faa_exact_f64(x::Float64, y::Float64, z::Float64)
    s1, e1 = _twosum(x, y)
    iszero(e1) || return nothing
    s2, e2 = _twosum(s1, z)
    (iszero(e2) && isfinite(s2)) || return nothing
    iszero(s2) ? 0.0 : s2                       # the draft's single zero
end
@inline _faa_exact_f64(::Any, ::Any, ::Any) = nothing

function ωeval(::Val{:FAA}, x::F, y::F, z::F) where {F<:Union{Float64, Float128}}
    (isnan(x) | isnan(y) | isnan(z)) && return _cnan(F)
    infs = count(isinf, (x, y, z))
    if infs > 0
        pos = any(v -> isinf(v) && !signbit(v), (x, y, z))
        neg = any(v -> isinf(v) && signbit(v), (x, y, z))
        (pos && neg) && return _cnan(F)
        return pos ? _cinf(F) : _cninf(F)
    end
    FAST_ARITH[] || return _exact_sum3(x, y, z)
    let e = _faa_exact_f64(x, y, z)
        e === nothing || return e
    end
    x128, y128, z128 = Float128(x), Float128(y), Float128(z)
    s1, e1 = _twosum128(x128, y128)
    s2, e2 = _twosum128(s1, z128)
    (iszero(e1) && iszero(e2)) && return iszero(s2) ? zero(Float128) : s2
    _span3(x128, y128, z128) >= _STICKY_MIN && return _faa_wide(x128, y128, z128)
    _exact_sum3(x, y, z)
end

# ---- rung 3 on the Dyadic carrier ------------------------------------------
# Exact arithmetic is native: Dyadic closes under add and multiply. The add
# uses the STICKY form; past the alignment band the small operand contributes
# only a sign, carried to the projection by `Sticky`.
@inline function ωeval(::Val{:Add}, x::Dyadic, y::Dyadic)
    v, sg = DyadicNumbers.add_sticky_dy(x, y)
    sg == 0 ? v : Sticky(v, sg)
end
@inline ωeval(::Val{:Subtract}, x::Dyadic, y::Dyadic) = ωeval(Val(:Add), x, -y)
@inline ωeval(::Val{:Multiply}, x::Dyadic, y::Dyadic) = DyadicNumbers.mul_dy(x, y)
@inline function ωeval(::Val{:FMA}, x::Dyadic, y::Dyadic, z::Dyadic)
    p = DyadicNumbers.mul_dy(x, y)
    ωeval(Val(:Add), p, z)
end
# FAA is the one row where the sticky protocol does NOT compose (two tails can
# cancel; Sticky carries one direction for one neglected tail). When either
# alignment leaves the exact band, drop to the exact MPFR sum.
@inline function ωeval(::Val{:FAA}, x::Dyadic, y::Dyadic, z::Dyadic)
    (isnan(x) | isnan(y) | isnan(z)) && return _cnan(Dyadic)
    if isinf(x) || isinf(y) || isinf(z)
        hasp = _isposinf(x) | _isposinf(y) | _isposinf(z)
        hasn = _isneginf(x) | _isneginf(y) | _isneginf(z)
        (hasp & hasn) && return _cnan(Dyadic)
        return hasp ? _cinf(Dyadic) : _cninf(Dyadic)
    end
    v1, s1 = DyadicNumbers.add_sticky_dy(x, y)
    if s1 == 0
        v2, s2 = DyadicNumbers.add_sticky_dy(v1, z)
        s2 == 0 && return v2                    # both adds exact
    end
    _exact_sum3(BigFloat(x), BigFloat(y), BigFloat(z))
end
# everything else: Dyadic has no transcendentals nor should it — convert
# exactly into the BigFloat rows (which yield a BigFloat or an Enclosure)
for op in OP_REGISTRY
    op.name in (:Add, :Subtract, :Multiply, :FMA, :FAA, :Convert) && continue
    op.name in _EXACT_SELECTION && continue          # typed ::CarrierValue below
    xs = [Symbol(:x, i) for i in 1:op.arity]
    @eval @inline ωeval(v::Val{$(QuoteNode(op.name))}, $((:($x::Dyadic) for x in xs)...)) =
        ωeval(v, $((:(BigFloat($x)) for x in xs)...))
end
# a lane result with no neglected tail: the block schema divides lane results
# by a scale, which the sticky protocol does not survive — recompute the rare
# sticky case exactly on BigFloat
@inline _nosticky(r) = r
@inline _nosticky(op::Val, xs...) = _nosticky_r(ωeval(op, xs...), op, xs...)
@inline _nosticky_r(r, op, xs...) = r
@inline _nosticky_r(::Sticky, op::Val, xs...) = ωeval(op, map(BigFloat, xs)...)

# ---- exact selections: parametric in the carrier ---------------------------
# Bare NaN/0.0 literals are Float64 and would lie on a wider carrier: every
# special is built at the operand's carrier, and the methods are homogeneous
# in C — a mixed-carrier call is a caller bug and should fail to dispatch.
# Typed ::CarrierValue, which names Dyadic explicitly: one implementation at
# every rung.

ωeval(::Val{:Abs}, x::C) where {C<:CarrierValue} = isnan(x) ? _cnan(C) : abs(x)
ωeval(::Val{:Negate}, x::C) where {C<:CarrierValue} = isnan(x) ? _cnan(C) : -x
ωeval(::Val{:CopySign}, x::C, y::C) where {C<:CarrierValue} =
    isnan(x) ? _cnan(C) : copysign(x, signbit(y) ? -one(C) : one(C))

function ωeval(::Val{:Clamp}, x::C, lo::C, hi::C) where {C<:CarrierValue}
    (isnan(x) | isnan(lo) | isnan(hi)) && return _cnan(C)
    x < lo ? lo : (x > hi ? hi : x)
end

# IEEE 754-2019 extremum semantics [interp where the draft text was unseen]:
#   Maximum/Minimum propagate NaN; the *Number forms prefer the number;
#   *Magnitude compare |·| with the plain compare as tie-break;
#   *Finite prefer finite operands, NaN when neither is finite.
for (nm, pick) in ((:Maximum, :(a >= b)), (:Minimum, :(a <= b)))
    @eval function ωeval(::Val{$(QuoteNode(nm))}, a::C, b::C) where {C<:CarrierValue}
        (isnan(a) | isnan(b)) && return _cnan(C)
        # the single-zero datum set has no ±0 distinction to honour
        $pick ? a : b
    end
end
for (nm, base) in ((:MaximumNumber, :Maximum), (:MinimumNumber, :Minimum))
    @eval function ωeval(::Val{$(QuoteNode(nm))}, a::C, b::C) where {C<:CarrierValue}
        isnan(a) && return isnan(b) ? _cnan(C) : b
        isnan(b) && return a
        ωeval(Val($(QuoteNode(base))), a, b)
    end
end
for (nm, base) in ((:MaximumMagnitude, :Maximum), (:MinimumMagnitude, :Minimum))
    cmp = base === :Maximum ? :(>) : :(<)
    @eval function ωeval(::Val{$(QuoteNode(nm))}, a::C, b::C) where {C<:CarrierValue}
        (isnan(a) | isnan(b)) && return _cnan(C)
        $(cmp)(abs(a), abs(b)) && return a
        $(cmp)(abs(b), abs(a)) && return b
        ωeval(Val($(QuoteNode(base))), a, b)
    end
end
for (nm, mag) in ((:MaximumMagnitudeNumber, :MaximumMagnitude),
                  (:MinimumMagnitudeNumber, :MinimumMagnitude))
    @eval function ωeval(::Val{$(QuoteNode(nm))}, a::C, b::C) where {C<:CarrierValue}
        isnan(a) && return isnan(b) ? _cnan(C) : b
        isnan(b) && return a
        ωeval(Val($(QuoteNode(mag))), a, b)
    end
end
# the Finite variants (draft §4.11.3 table): prefer finite operands; then
# infinities beat NaN; two infinities compare. Only (NaN, NaN) is NaN. These
# are the reduction semantics ConvertToBlockMaxAbsFinite's NaN seed relies on.
for (nm, base) in ((:MaximumFinite, :Maximum), (:MinimumFinite, :Minimum))
    @eval function ωeval(::Val{$(QuoteNode(nm))}, a::C, b::C) where {C<:CarrierValue}
        fa, fb = isfinite(a), isfinite(b)
        fa & fb && return ωeval(Val($(QuoteNode(base))), a, b)
        fa && return a
        fb && return b
        isnan(a) && return isnan(b) ? _cnan(C) : b
        isnan(b) && return a
        ωeval(Val($(QuoteNode(base))), a, b)
    end
end

# ---- the quotient family: fma exactness proof, else the ladder --------------
# fma(q, y, -x) == 0 is a proof only where fma is EXACT — Float64 hardware, and
# `fma128`, which is correctly rounded by construction and bit-compatible with
# fmaq. An MPFR "proof" at ambient precision yields false positives, so the
# BigFloat rows go straight to the ladder.
#
# The Float128 tier (float128use.md §1). Measured exactness rates over the code
# space of rung-2 formats: at P = 5, 15.2% of quotients, 6.2% of reciprocals and
# 9.2% of square roots are exact; at P = 2 it is 75.0%, 49.9% and 24.9%. Low
# precision is where this package lives, so the proof earns its keep.
#
# THE FLOOR IS A PROOF OBLIGATION, not defensive coding — the Float64 twin of
# this constant was shipped without it and a test caught the bug. For division,
# the residual d = q·y − x is a difference between an exact product of two
# Float128s (≤ 226 significant bits) and x (≤ 113), with both terms of magnitude
# ≈ |x| because q = fl(x/y). So d ≠ 0 ⇒ |d| ≥ |x|·2^-225. `fma128` correctly
# rounds d and returns zero only below half the minimum subnormal, 2^-16495.
# The implication "fma128 == 0 ⇒ exact" therefore needs |x|·2^-225 ≥ 2^-16495,
# i.e. |x| ≥ 2^-16270. The constant below adds ~70 binades of margin. Square
# root takes the identical bound with s·s in place of q·y.
#
# A rung-2 format has 2B ≤ 16384 and P ≤ 16, so its smallest positive datum is
# about 2^-8206 — clear of the floor by more than 7,900 binades. Like
# `_FMA_EXACT_FLOOR`, it never fires in practice and makes the proof sound
# unconditionally.
const _F128_EXACT_FLOOR = ldexp(one(Float128), -16200)

"""
    _try_div128(x, y) -> Union{Float128, Nothing}

`x / y` when it is EXACTLY representable in `Float128`, else `nothing` — a
refusal, not an error: the caller runs the unchanged MPFR ladder. Assumes the
caller has already peeled NaN, the infinities and the zeros, so both operands
are finite and nonzero.
"""
@inline function _try_div128(x::Float128, y::Float128)
    q = x / y
    (isfinite(q) && !iszero(q) && abs(x) >= _F128_EXACT_FLOOR) || return nothing
    iszero(fma128(q, y, -x)) ? q : nothing
end

"""
    _try_recip128(x) -> Union{Float128, Nothing}

`1 / x` when exact in `Float128`, else `nothing`. No magnitude floor: the
residual `q·x − 1` is measured against ONE, so a nonzero residual is at least
2^-226 in magnitude and cannot underflow.
"""
@inline function _try_recip128(x::Float128)
    q = one(Float128) / x
    (isfinite(q) && !iszero(q)) || return nothing
    iszero(fma128(q, x, -one(Float128))) ? q : nothing
end

"""
    _try_sqrt128(x) -> Union{Float128, Nothing}

`√x` when exact in `Float128`, else `nothing`. Assumes `x > 0` and finite.
"""
@inline function _try_sqrt128(x::Float128)
    s = sqrt(x)
    (isfinite(s) && !iszero(s) && x >= _F128_EXACT_FLOOR) || return nothing
    iszero(fma128(s, s, -x)) ? s : nothing
end

function ωeval(::Val{:Divide}, x::Float64, y::Float64)
    (isnan(x) | isnan(y)) && return NaN
    if isinf(x)
        isinf(y) && return NaN
        return copysign(Inf, sign(x) * (signbit(y) ? -1.0 : 1.0))
    end
    isinf(y) && return 0.0
    if iszero(y)
        # one unsigned zero: x/0 has no determinable sign → NaN [interp]
        return NaN
    end
    iszero(x) && return 0.0
    q = x / y
    (isfinite(q) && fma(q, y, -x) == 0.0) && return q
    Enclosure(_ladder2(/, x, y), () -> Float128(x) / Float128(y), isfinite(q) ? q : NaN)
end
function ωeval(::Val{:Divide}, x::Float128, y::Float128)
    (isnan(x) | isnan(y)) && return _cnan(Float128)
    if isinf(x)
        isinf(y) && return _cnan(Float128)
        return (signbit(x) ⊻ signbit(y)) ? _cninf(Float128) : _cinf(Float128)
    end
    isinf(y) && return _czero(Float128)
    iszero(y) && return _cnan(Float128)        # one unsigned zero, as at rung 1
    iszero(x) && return _czero(Float128)
    q = _try_div128(x, y)
    q === nothing || return q
    _mpfr2_cr(/, x, y)
end
function ωeval(::Val{:Divide}, x, y)
    (isnan(x) | isnan(y)) && return _cnan(BigFloat)
    if isinf(x)
        isinf(y) && return _cnan(BigFloat)
        return (signbit(x) ⊻ signbit(y)) ? _cninf(BigFloat) : _cinf(BigFloat)
    end
    isinf(y) && return _czero(BigFloat)
    iszero(y) && return _cnan(BigFloat)
    iszero(x) && return _czero(BigFloat)
    _mpfr2_cr(/, x, y)
end

function ωeval(::Val{:Recip}, x::C) where {C<:AbstractFloat}
    isnan(x) && return _cnan(C)
    isinf(x) && return _czero(C)
    iszero(x) && return _cnan(C)               # 1/0: no determinable sign [interp]
    if x isa Float64
        q = 1.0 / x
        (isfinite(q) && fma(q, x, -1.0) == 0.0) && return q
        return Enclosure(_ladder1(inv, x), () -> inv(Float128(x)), isfinite(q) ? q : NaN)
    elseif x isa Float128
        q = _try_recip128(x)
        q === nothing || return q
    end
    Enclosure(_ladder1(inv, x))
end

function ωeval(::Val{:Sqrt}, x::C) where {C<:AbstractFloat}
    isnan(x) && return _cnan(C)
    signbit(x) && !iszero(x) && return _cnan(C)
    iszero(x) && return _czero(C)
    isinf(x) && return _cinf(C)
    if x isa Float64
        s = sqrt(x)
        fma(s, s, -x) == 0.0 && return s
        return Enclosure(_ladder1(sqrt, x), () -> sqrt(Float128(x)), s)
    elseif x isa Float128
        s = _try_sqrt128(x)
        s === nothing || return s
    end
    Enclosure(_ladder1(sqrt, x))
end

function ωeval(::Val{:RSqrt}, x::C) where {C<:AbstractFloat}
    isnan(x) && return _cnan(C)
    signbit(x) && !iszero(x) && return _cnan(C)
    iszero(x) && return _cnan(C)               # 1/√0 unsigned [interp]
    isinf(x) && return _czero(C)
    if x isa Float64
        s = sqrt(x)
        if fma(s, s, -x) == 0.0
            r = 1.0 / s
            fma(r, s, -1.0) == 0.0 && return r
        end
        return Enclosure(_ladder1(b -> inv(sqrt(b)), x), () -> inv(sqrt(Float128(x))), 1.0 / s)
    elseif x isa Float128
        s = _try_sqrt128(x)                     # both stages, as at rung 1
        if s !== nothing
            r = _try_recip128(s)
            r === nothing || return r
        end
    end
    Enclosure(_ladder1(b -> inv(sqrt(b)), x))
end

# ---- Group B: the enclosure ladder ------------------------------------------
# Each row: NaN, domain rows, exact-value peels, then a directed enclosure.
# Domain violations are NaN (the flow of learning is unbroken — no exceptional
# states).

# ---- exact constants in the incoming carrier --------------------------------
# The exact peels below (Log2 at a power of two, Exp2 at an integer, the
# π-scaled inverse-trig rows at their rational points) exist so the enclosure
# does not chase an interior grid point forever. They were built as `BigFloat`,
# which made each of them SLOWER than the general path it shortcuts — measured
# 499 ns against 29 ns for Log2, 536 against 23 for Exp2. A half, a quarter and
# a small integer are exact in every carrier that reaches here (C is Float64,
# Float128 or BigFloat: `Dyadic <: Real`, not `<: AbstractFloat`), so build them
# with ldexp and one() and keep the carrier the caller arrived with.
@inline _chalf(::Type{C}) where {C<:AbstractFloat} = ldexp(one(C), -1)
@inline _cquarter(::Type{C}) where {C<:AbstractFloat} = ldexp(one(C), -2)
@inline _csigned(v::C, negative::Bool) where {C<:AbstractFloat} = negative ? -v : v

# 2^n in the narrowest carrier that holds it EXACTLY, else an exact BigFloat.
# The check is a round-trip rather than a hard-coded exponent bound: an exact
# power of two is representable iff ldexp gives back a finite nonzero value at
# the same exponent, subnormals included. Never inferred from C — a narrow
# input can have an exact result only a wider result format can see.
@inline function _exact_pow2(n::Int)
    r64 = ldexp(1.0, n)
    (isfinite(r64) && !iszero(r64) && exponent(r64) == n) && return r64
    r128 = ldexp(one(Float128), n)
    (isfinite(r128) && !iszero(r128) && exponent(r128) == n) && return r128
    setprecision(() -> ldexp(BigFloat(1), n), BigFloat, 64)
end

# libm-shaped rows sharing one pattern: (name, bigf, domain predicate on
# finite x [true = in domain], value rows at specials)
function ωeval(::Val{:Exp}, x::C) where {C<:AbstractFloat}
    isnan(x) && return _cnan(C)
    isinf(x) && return signbit(x) ? _czero(C) : _cinf(C)
    iszero(x) && return one(C)
    _mpfr1_cr(exp, x)
end
function ωeval(::Val{:Exp2}, x::C) where {C<:AbstractFloat}
    isnan(x) && return _cnan(C)
    isinf(x) && return signbit(x) ? _czero(C) : _cinf(C)
    iszero(x) && return one(C)
    # exact at integer x: 2^n is a datum candidate — peel to avoid chasing an
    # interior grid point forever
    (isinteger(x) && abs(x) <= 2^20) && return _exact_pow2(Int(x))
    _mpfr1_cr(exp2, x)
end
function ωeval(::Val{:ExpMinusOne}, x::C) where {C<:AbstractFloat}
    isnan(x) && return _cnan(C)
    isinf(x) && return signbit(x) ? -one(C) : _cinf(C)
    iszero(x) && return _czero(C)
    _mpfr1_cr(expm1, x)
end
function ωeval(::Val{:Log}, x::C) where {C<:AbstractFloat}
    isnan(x) && return _cnan(C)
    iszero(x) && return _cninf(C)
    signbit(x) && return _cnan(C)
    isinf(x) && return _cinf(C)
    isone(x) && return _czero(C)
    _mpfr1_cr(log, x)
end
function ωeval(::Val{:Log2}, x::C) where {C<:AbstractFloat}
    isnan(x) && return _cnan(C)
    iszero(x) && return _cninf(C)
    signbit(x) && return _cnan(C)
    isinf(x) && return _cinf(C)
    # exact at powers of two — the enclosure would straddle the integer forever
    if x == ldexp(one(C), exponent(x))
        return C(exponent(x))          # a small integer, exact in every carrier
    end
    _mpfr1_cr(log2, x)
end
function ωeval(::Val{:LogOnePlus}, x::C) where {C<:AbstractFloat}
    isnan(x) && return _cnan(C)
    iszero(x) && return _czero(C)
    isinf(x) && return signbit(x) ? _cnan(C) : _cinf(C)
    x < -1 && return _cnan(C)
    x == -1 && return _cninf(C)
    _mpfr1_cr(log1p, x)
end

for (nm, bf) in ((:Sin, :sin), (:Cos, :cos), (:Tan, :tan))
    @eval function ωeval(::Val{$(QuoteNode(nm))}, x::C) where {C<:AbstractFloat}
        isnan(x) && return _cnan(C)
        isinf(x) && return _cnan(C)
        iszero(x) && return $(nm === :Cos ? :(one(C)) : :(_czero(C)))
        _mpfr1_cr($bf, x)
    end
end
function ωeval(::Val{:ArcSin}, x::C) where {C<:AbstractFloat}
    isnan(x) && return _cnan(C)
    abs(x) > 1 && return _cnan(C)
    iszero(x) && return _czero(C)
    _mpfr1_cr(asin, x)
end
function ωeval(::Val{:ArcCos}, x::C) where {C<:AbstractFloat}
    isnan(x) && return _cnan(C)
    abs(x) > 1 && return _cnan(C)
    isone(x) && return _czero(C)
    _mpfr1_cr(acos, x)
end
# directed enclosure of s · π/2
_mpfr_halfpi(s::Int) = Enclosure(prec -> setprecision(BigFloat, max(prec, 64)) do
    lo = setrounding(() -> BigFloat(π) / 2, BigFloat, s > 0 ? RoundDown : RoundUp)
    hi = setrounding(() -> BigFloat(π) / 2, BigFloat, s > 0 ? RoundUp : RoundDown)
    s > 0 ? (lo, hi) : (-hi, -lo)
end)

function ωeval(::Val{:ArcTan}, x::C) where {C<:AbstractFloat}
    isnan(x) && return _cnan(C)
    iszero(x) && return _czero(C)
    isinf(x) && return _mpfr_halfpi(signbit(x) ? -1 : 1)
    _mpfr1_cr(atan, x)
end
for (nm, bf, oddzero) in ((:Sinh, :sinh, true), (:Cosh, :cosh, false),
                          (:Tanh, :tanh, true), (:ArcSinh, :asinh, true))
    @eval function ωeval(::Val{$(QuoteNode(nm))}, x::C) where {C<:AbstractFloat}
        isnan(x) && return _cnan(C)
        if isinf(x)
            $(nm === :Tanh ?
              :(return signbit(x) ? -one(C) : one(C)) :
              nm === :Cosh ?
              :(return _cinf(C)) :
              :(return signbit(x) ? _cninf(C) : _cinf(C)))
        end
        iszero(x) && return $(oddzero ? :(_czero(C)) : :(one(C)))
        _mpfr1_cr($bf, x)
    end
end
function ωeval(::Val{:ArcCosh}, x::C) where {C<:AbstractFloat}
    isnan(x) && return _cnan(C)
    x < 1 && return _cnan(C)
    isone(x) && return _czero(C)
    isinf(x) && return _cinf(C)
    _mpfr1_cr(acosh, x)
end
function ωeval(::Val{:ArcTanh}, x::C) where {C<:AbstractFloat}
    isnan(x) && return _cnan(C)
    abs(x) > 1 && return _cnan(C)
    iszero(x) && return _czero(C)
    abs(x) == 1 && return signbit(x) ? _cninf(C) : _cinf(C)
    _mpfr1_cr(atanh, x)
end

function ωeval(::Val{:Softplus}, x::C) where {C<:AbstractFloat}
    isnan(x) && return _cnan(C)
    isinf(x) && return signbit(x) ? _czero(C) : _cinf(C)
    # two forms, both monotone compositions under whole-expression directed
    # rounding: x + log1p(exp(-x)) for x > 0 — tight for large x, and exp(-x)
    # UNDERflows rather than overflowing MPFR's exponent range at huge x —
    # log1p(exp(x)) otherwise
    _mpfr1(b -> b > 0 ? b + log1p(exp(-b)) : log1p(exp(b)), x)
end

# π-scaled trig: exact mod-2 reduction (rem by a power of two is exact on
# every carrier), quarter-integer peels (Niven), then the π-folded enclosure
@inline function _mod2(x::AbstractFloat)
    two = oftype(x, 2)
    r = rem(x, two)
    r < zero(x) ? r + two : r
end
_isquarter(r) = isinteger(4r)

function ωeval(::Val{:SinPi}, x::C) where {C<:AbstractFloat}
    isnan(x) && return _cnan(C)
    isinf(x) && return _cnan(C)
    r = _mod2(x)
    if _isquarter(r) && isinteger(2r)          # r ∈ {0, ½, 1, 1½}
        r == 0 && return _czero(C)
        r == 1 && return _czero(C)
        return r < 1 ? one(C) : -one(C)
    end
    _mpfr_pitrig(sin, r; yd = _yd1(sinpi, r))
end
function ωeval(::Val{:CosPi}, x::C) where {C<:AbstractFloat}
    isnan(x) && return _cnan(C)
    isinf(x) && return _cnan(C)
    r = _mod2(x)
    if _isquarter(r) && isinteger(2r)
        r == 0 && return one(C)
        r == 1 && return -one(C)
        return _czero(C)                       # r ∈ {½, 1½}
    end
    _mpfr_pitrig(cos, r; yd = _yd1(cospi, r))
end
function ωeval(::Val{:TanPi}, x::C) where {C<:AbstractFloat}
    isnan(x) && return _cnan(C)
    isinf(x) && return _cnan(C)
    r = _mod2(x)
    if _isquarter(r)
        isinteger(r) && return _czero(C)
        isinteger(2r) && return _cnan(C)       # poles at ½, 1½: unsigned ∞ → NaN [interp]
        # tan(π·(k/4)) = ±1 at the odd quarter-integers
        return (r == oftype(r, 0.25) || r == oftype(r, 1.25)) ? one(C) : -one(C)
    end
    _mpfr_pitrig(tan, r; yd = _yd1(tanpi, r))
end

function ωeval(::Val{:ArcSinPi}, x::C) where {C<:AbstractFloat}
    isnan(x) && return _cnan(C)
    abs(x) > 1 && return _cnan(C)
    iszero(x) && return _czero(C)
    # ArcSinPi(±1) = ±½ — exact, and a datum candidate: peel it [Niven]
    abs(x) == 1 && return _csigned(_chalf(C), signbit(x))
    _mpfr_divpi(asin, x)
end
function ωeval(::Val{:ArcCosPi}, x::C) where {C<:AbstractFloat}
    isnan(x) && return _cnan(C)
    abs(x) > 1 && return _cnan(C)
    isone(x) && return _czero(C)
    x == -1 && return one(C)
    iszero(x) && return _chalf(C)
    _mpfr_divpi(acos, x)
end
function ωeval(::Val{:ArcTanPi}, x::C) where {C<:AbstractFloat}
    isnan(x) && return _cnan(C)
    iszero(x) && return _czero(C)
    isinf(x) && return _csigned(_chalf(C), signbit(x))
    isone(abs(x)) && return _csigned(_cquarter(C), signbit(x))
    _mpfr_divpi(atan, x)
end

function ωeval(::Val{:Hypot}, x::C, y::C) where {C<:AbstractFloat}
    (isnan(x) | isnan(y)) && return _cnan(C)
    (isinf(x) | isinf(y)) && return _cinf(C)
    iszero(x) && return ωeval(Val(:Abs), y)
    iszero(y) && return ωeval(Val(:Abs), x)
    _mpfr2_cr(hypot, x, y)
end
# ±π as a directed enclosure (the (Y, −∞) and (0, X<0) rows)
_mpfr_pi(s::Int) = Enclosure(prec -> setprecision(BigFloat, max(prec, 64)) do
    lo = setrounding(() -> BigFloat(π), BigFloat, s > 0 ? RoundDown : RoundUp)
    hi = setrounding(() -> BigFloat(π), BigFloat, s > 0 ? RoundUp : RoundDown)
    s > 0 ? (lo, hi) : (-hi, -lo)
end)

# the draft's ArcTan2 / ArcTan2Pi tables, row for row and IN ORDER: (0, 0) and
# (±∞, ±∞) are NaN (the limit is indeterminate — NOTE 1, NOTE 2); the axis
# and infinity rows are exact constants. A row that is an exact GRID POINT
# (½, 1, −½, −1 for ArcTan2Pi) can never be resolved by the interval ladder,
# which is how the missing peels were found.
function ωeval(::Val{:ArcTan2}, y::C, x::C) where {C<:AbstractFloat}
    (isnan(x) | isnan(y)) && return _cnan(C)
    (iszero(y) && iszero(x)) && return _cnan(C)
    (isinf(y) && isinf(x)) && return _cnan(C)
    _isposinf(x) && return _czero(C)
    (iszero(y) && x > 0) && return _czero(C)
    _isposinf(y) && return _mpfr_halfpi(1)
    (y > 0 && iszero(x)) && return _mpfr_halfpi(1)
    _isneginf(x) && return _mpfr_pi(y >= 0 ? 1 : -1)
    (iszero(y) && x < 0) && return _mpfr_pi(1)
    _isneginf(y) && return _mpfr_halfpi(-1)
    (y < 0 && iszero(x)) && return _mpfr_halfpi(-1)
    _mpfr2_cr(atan, y, x)
end
function ωeval(::Val{:ArcTan2Pi}, y::C, x::C) where {C<:AbstractFloat}
    (isnan(x) | isnan(y)) && return _cnan(C)
    (iszero(y) && iszero(x)) && return _cnan(C)
    (isinf(y) && isinf(x)) && return _cnan(C)
    _isposinf(x) && return _czero(C)
    (iszero(y) && x > 0) && return _czero(C)
    _isposinf(y) && return C(0.5)
    (y > 0 && iszero(x)) && return C(0.5)
    _isneginf(x) && return y >= 0 ? one(C) : -one(C)
    (iszero(y) && x < 0) && return one(C)
    _isneginf(y) && return C(-0.5)
    (y < 0 && iszero(x)) && return C(-0.5)
    if abs(x) == abs(y)                              # the exact quarter-integer peels
        q = (x > 0 ? (y > 0 ? 1 : -1) : (y > 0 ? 3 : -3))
        return ldexp(C(q), -2)         # q/4 with q ∈ {±1, ±3}: exact
    end
    _arctan2pi_general(y, x)
end
function _arctan2pi_general(y, x)
    Enclosure(_ladder_atan2pi(y, x), _fq2((a, b) -> atan(a, b) / Float128(π), y, x),
              _yd2((a, b) -> atan(a, b) / π, y, x))
end
function _ladder_atan2pi(y, x)
    prec -> setprecision(BigFloat, _ladderprec(prec, x, y)) do
        by, bx = _exactbig(y), _exactbig(x)
        lo = setrounding(BigFloat, RoundDown) do
            a = atan(by, bx)
            a / setrounding(() -> BigFloat(π), BigFloat, a >= 0 ? RoundUp : RoundDown)
        end
        hi = setrounding(BigFloat, RoundUp) do
            a = atan(by, bx)
            a / setrounding(() -> BigFloat(π), BigFloat, a >= 0 ? RoundDown : RoundUp)
        end
        (lo, hi)
    end
end