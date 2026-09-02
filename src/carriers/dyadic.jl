# DyadicNumbers — the rung-3 exact carrier
#
# PROVENANCE: adapted from SmallFloats.jl `src/dyadic.jl`
#   repo   ~/github/SmallFloats.jl (unregistered)
#   commit 7f864f08dbe8a31de60d0b4e9a1d826871186bd2 (2026-08-27)
#   port   2026-08-28 — restyled to AIFloats conventions (comment style,
#          prose trimmed); ALGORITHMS UNCHANGED. Additions for this package
#          are marked "AIFloats:" and are Base-surface conveniences only.
#   gate   test/test-dyadic.jl compares this module's behaviour against golden
#          digests captured from the original (test/support/dyadic_golden.sha256,
#          captured by test/support/dyadic_capture.jl on a machine with
#          SmallFloats) — plan §9.9.
#
# An exact dyadic rational S · 2^Q plus the three non-finite rows. Every datum
# of every P3109 format is exactly S · 2^Q with |S| < 2^16, so arithmetic on
# datums is closed and exact here, allocation-free; MPFR buys nothing for it.
# The transcendental fallback still goes to MPFR via an exact BigFloat image.
#
# THIS FILE HAS NO AIFloats DEPENDENCIES and loads first — the type must be
# checkable on its own terms. Every function is total over the four kinds.
#
# `<: Real`, NOT `<: AbstractFloat`: methods elsewhere written `::AbstractFloat`
# mean "a float carrier", and Dyadic implements ~ten operations rather than the
# full AbstractFloat obligation. `promotecarrier` targets BigFloat, never this.

"""
    DyadicNumbers

The rung-3 exact carrier: an exact dyadic rational `S · 2^Q` plus the three
non-finite rows, with `Dyadic` as its type.

Every datum of every P3109 format is exactly `S · 2^Q` with `|S| < 2^16`, so
arithmetic on datums is closed and exact here, allocation-free — MPFR buys
nothing for it. Transcendental fallbacks still escalate to MPFR through an
exact `BigFloat` image.

`Dyadic <: Real`, deliberately **not** `<: AbstractFloat`: methods elsewhere
written `::AbstractFloat` mean "a float carrier", and `Dyadic` implements about
ten operations rather than the full `AbstractFloat` obligation.
`AIFloats.promotecarrier` targets `BigFloat`, never this.

Implementation detail, and unstable: it is documented on the
[Internal carriers](@ref internals) page, not in the public reference. Vendored
from SmallFloats.jl (provenance header in `src/carriers/dyadic.jl`) and
verified against golden digests in `test/support/dyadic_golden.sha256`.

Not exported; reach it as `AIFloats.DyadicNumbers` and its type as
`AIFloats.Dyadic`.
"""
module DyadicNumbers

export Dyadic, DY_FINITE, DY_POSINF, DY_NEGINF, DY_NAN,
       dyadic_to_rational, rational_to_dyadic, isdyadic

# a separate kind field keeps the finite path branch-free after one check
const DY_FINITE = 0x00
const DY_POSINF = 0x01
const DY_NEGINF = 0x02
const DY_NAN    = 0x03

"""
    Dyadic(S::Int128, Q::Int64)          -> the exact value S · 2^Q
    Dyadic(kind::UInt8)                  -> one of the three non-finite rows

An exact dyadic rational, the rung-3 evaluation carrier. `S` is signed and
deliberately not normalized (the only consumer, `round_to_precision`,
realigns anyway), so `==` compares values, not fields. `kind` is the LAST
field: trailing, the tag lands in `Q`'s slack and the struct is 32 bytes.
"""
struct Dyadic <: Real
    S::Int128
    Q::Int64
    kind::UInt8

    # Public three-field construction is checked because every operation below
    # assumes exactly four tags and canonical zero payloads for special values.
    @inline function Dyadic(S::Int128, Q::Int64, kind::UInt8)
        kind <= DY_NAN || throw(ArgumentError(
            "invalid Dyadic kind $kind: expected one of DY_FINITE, DY_POSINF, " *
            "DY_NEGINF, DY_NAN (0x00 through 0x03)"))
        kind == DY_FINITE || (iszero(S) && iszero(Q)) || throw(ArgumentError(
            "non-finite Dyadic values require the canonical zero payload"))
        new(S, Q, kind)
    end

    # Arithmetic has already established the tag and payload invariants. Keep
    # that hot implementation path explicit and free of repeated validation.
    global @inline _rawdyadic(S::Int128, Q::Int64, kind::UInt8) = new(S, Q, kind)
end
Dyadic(S::Integer, Q::Integer) = _rawdyadic(Int128(S), Int64(Q), DY_FINITE)

# the tag is range-checked: constructors check, kernels assume
function Dyadic(kind::UInt8)
    kind <= DY_NAN || throw(ArgumentError(
        "invalid Dyadic kind $kind: expected one of DY_FINITE, DY_POSINF, " *
        "DY_NEGINF, DY_NAN (0x00 through 0x03)"))
    _rawdyadic(Int128(0), Int64(0), kind)
end

const DYADIC_ZERO   = Dyadic(Int128(0), Int64(0))
const DYADIC_ONE    = Dyadic(Int128(1), Int64(0))
const DYADIC_POSINF = Dyadic(DY_POSINF)
const DYADIC_NEGINF = Dyadic(DY_NEGINF)
const DYADIC_NAN    = Dyadic(DY_NAN)

# ---- predicates: total over the four kinds; none can throw -------------------
@inline isfinite_dy(x::Dyadic) = x.kind == DY_FINITE
@inline isnan_dy(x::Dyadic)    = x.kind == DY_NAN
@inline isinf_dy(x::Dyadic)    = x.kind == DY_POSINF || x.kind == DY_NEGINF
@inline iszero_dy(x::Dyadic)   = x.kind == DY_FINITE && iszero(x.S)
# sound only because DY_FINITE == 0x00
@inline bothfinite_dy(x::Dyadic, y::Dyadic) = (x.kind | y.kind) == DY_FINITE

Base.isfinite(x::Dyadic) = isfinite_dy(x)
Base.isnan(x::Dyadic)    = isnan_dy(x)
Base.isinf(x::Dyadic)    = isinf_dy(x)
Base.iszero(x::Dyadic)   = iszero_dy(x)
Base.zero(::Type{Dyadic}) = DYADIC_ZERO
Base.zero(::Dyadic)       = DYADIC_ZERO
Base.one(::Type{Dyadic})  = DYADIC_ONE
Base.one(::Dyadic)        = DYADIC_ONE

# sign in {-1, 0, 1}; NaN answers 0 deliberately — callers test isnan first
@inline function sign_dy(x::Dyadic)
    isfinite_dy(x) && return x.S > 0 ? 1 : (x.S < 0 ? -1 : 0)
    x.kind == DY_POSINF && return 1
    x.kind == DY_NEGINF && return -1
    0
end
Base.sign(x::Dyadic) = sign_dy(x)
Base.signbit(x::Dyadic) = sign_dy(x) < 0

# typemin(Int128) cannot be negated in place; |typemin| = 2^127 = 1 · 2^(Q+127)
@noinline function _negate_typemin(Q::Int64)
    Q <= typemax(Int64) - 127 || throw(OverflowError(
        "Dyadic: negating a typemin(Int128) significand needs exponent " *
        "$Q + 127, which exceeds Int64"))
    _rawdyadic(one(Int128), Q + 127, DY_FINITE)
end

@inline function Base.abs(x::Dyadic)
    if isfinite_dy(x)
        s = x.S
        s >= 0 && return x
        s == typemin(Int128) && return _negate_typemin(x.Q)
        return _rawdyadic(-s, x.Q, DY_FINITE)
    end
    x.kind == DY_NEGINF ? DYADIC_POSINF : x
end
@inline function Base.:-(x::Dyadic)
    if isfinite_dy(x)
        s = x.S
        s == typemin(Int128) && return _negate_typemin(x.Q)
        return _rawdyadic(-s, x.Q, DY_FINITE)
    end
    x.kind == DY_POSINF && return DYADIC_NEGINF
    x.kind == DY_NEGINF && return DYADIC_POSINF
    x
end

# |S| as UInt128: abs(typemin(Int128)) wraps; the unsigned reading is 2^127
@inline mag_dy(S::Int128) = unsigned(abs(S))
# significant bits of |S|; zero answers 0
@inline nbits_dy(S::Int128) = 128 - leading_zeros(mag_dy(S))

# ---- addition, with the alignment bands --------------------------------------
#   exact Int128 alignment      :  ΔQ ≤ 94                (32-bit head + carry)
#   sticky (tail is sign only)  :  ΔQ > P + N + 2
#   total coverage              ⟺  P + N ≤ 92  (P = 16, N = 60 ⇒ 76: margin 16)
# DYADIC_ADD_COVERAGE is asserted by the suite: raising P past 16 or N past 60
# would silently open a gap between the bands.
const DYADIC_HEAD_BITS    = 32
const DYADIC_ALIGN_MAX    = 127 - DYADIC_HEAD_BITS - 1     # 94
const DYADIC_ADD_COVERAGE = 92                             # P + N must not exceed

"""
    add_dy(x, y) -> Dyadic

Exact sum when the operands align within `DYADIC_ALIGN_MAX`; otherwise the
caller is past the sticky threshold and [`add_sticky_dy`](@ref) applies
(this throws). The `kind` carries the IEEE ∞/NaN algebra.
"""
@inline function add_dy(x::Dyadic, y::Dyadic)
    bothfinite_dy(x, y) || return _add_special(x, y)
    iszero(x.S) && return y
    iszero(y.S) && return x
    if x.Q >= y.Q
        d = x.Q - y.Q
        d > DYADIC_ALIGN_MAX && return _add_wide(x, y, d)
        return _add_aligned(x, y, d)
    else
        d = y.Q - x.Q
        d > DYADIC_ALIGN_MAX && return _add_wide(y, x, d)
        return _add_aligned(y, x, d)
    end
end

# inlinable on purpose (measured: the gate + an inlinable helper is the fastest
# shape; pairing it with @noinline loses 20%)
@inline function _add_special(x::Dyadic, y::Dyadic)
    kx, ky = x.kind, y.kind
    (kx == DY_NAN) | (ky == DY_NAN) && return DYADIC_NAN
    kx == DY_FINITE && return y                    # y is the infinity
    ky == DY_FINITE && return x                    # x is the infinity
    kx == ky ? x : DYADIC_NAN                      # ∞ + (−∞)
end

# the aligned exact sum: `big`/`small` ordered by EXPONENT, not magnitude
@inline _add_aligned(big::Dyadic, small::Dyadic, d::Integer) =
    _rawdyadic((big.S << d) + small.S, small.Q, DY_FINITE)

@noinline _add_wide(::Dyadic, ::Dyadic, d::Int) = throw(ArgumentError(
    "Dyadic add with ΔQ = $d exceeds the exact alignment band " *
    "(DYADIC_ALIGN_MAX = $DYADIC_ALIGN_MAX); the caller must take the sticky " *
    "path, which is only sound for ΔQ > P + N + 2"))

@noinline _throw_add_wide(nb::Int, d::Int) = throw(ArgumentError(
    "Dyadic add would overflow Int128: the larger operand carries $nb " *
    "significand bits and the alignment shift is $d, totalling $(nb + d) > 126"))

"""
    add_dy_checked(x, y) -> Dyadic

[`add_dy`](@ref) with its width precondition enforced (a separate function,
not `@boundscheck`: that elides only under `@inbounds`, and no engine call
site is one).
"""
@inline function add_dy_checked(x::Dyadic, y::Dyadic)
    bothfinite_dy(x, y) || return _add_special(x, y)
    iszero(x.S) && return y
    iszero(y.S) && return x
    hi, lo, d = x.Q >= y.Q ? (x, y, Int(x.Q - y.Q)) : (y, x, Int(y.Q - x.Q))
    d > DYADIC_ALIGN_MAX && return _add_wide(hi, lo, d)
    nb = nbits_dy(hi.S)
    nb + d <= 126 || _throw_add_wide(nb, d)
    _add_aligned(hi, lo, d)
end

"""
    add_sticky_dy(x, y) -> (Dyadic, Int)

The sum with a sticky sign in `{-1, 0, +1}` describing a tail below the
returned value's last bit: the exact band when the operands align, the
sign-only band otherwise.
"""
@inline function add_sticky_dy(x::Dyadic, y::Dyadic)
    bothfinite_dy(x, y) || return (_add_special(x, y), 0)
    iszero(x.S) && return (y, 0)
    iszero(y.S) && return (x, 0)
    if x.Q >= y.Q
        d = x.Q - y.Q
        d <= DYADIC_ALIGN_MAX && return (_add_aligned(x, y, d), 0)
        return (x, y.S > 0 ? 1 : -1)
    else
        d = y.Q - x.Q
        d <= DYADIC_ALIGN_MAX && return (_add_aligned(y, x, d), 0)
        return (y, x.S > 0 ? 1 : -1)
    end
end

"""
    mul_dy(x, y) -> Dyadic

Exact product, **unchecked**: precondition `nbits(x.S) + nbits(y.S) ≤ 96`,
which every operand the engine forms satisfies (a datum carries ≤ 16 bits).
[`mul_dy_checked`](@ref) enforces it.
"""
@inline function mul_dy(x::Dyadic, y::Dyadic)
    (isnan_dy(x) | isnan_dy(y)) && return DYADIC_NAN
    if isinf_dy(x) || isinf_dy(y)
        (iszero_dy(x) | iszero_dy(y)) && return DYADIC_NAN          # 0 · ∞
        return sign_dy(x) * sign_dy(y) > 0 ? DYADIC_POSINF : DYADIC_NEGINF
    end
    _rawdyadic(x.S * y.S, x.Q + y.Q, DY_FINITE)
end

@noinline _throw_mul_wide(nx::Int, ny::Int) = throw(ArgumentError(
    "Dyadic multiply would overflow Int128: $nx + $ny significand bits > 96"))

"""
    mul_dy_checked(x, y) -> Dyadic

[`mul_dy`](@ref) with its width precondition enforced: throws `ArgumentError`
rather than wrapping when the significand product would leave `Int128`.
"""
@inline function mul_dy_checked(x::Dyadic, y::Dyadic)
    (isnan_dy(x) | isnan_dy(y)) && return DYADIC_NAN
    if isinf_dy(x) || isinf_dy(y)
        (iszero_dy(x) | iszero_dy(y)) && return DYADIC_NAN
        return sign_dy(x) * sign_dy(y) > 0 ? DYADIC_POSINF : DYADIC_NEGINF
    end
    nx, ny = nbits_dy(x.S), nbits_dy(y.S)
    nx + ny <= 96 || _throw_mul_wide(nx, ny)
    _rawdyadic(x.S * y.S, x.Q + y.Q, DY_FINITE)
end

# ---- ordering by VALUE (fields are not normalized). Total; no band: sign,
# then binade, then aligned significands (bounded by the width difference).
@inline function cmp_dy(x::Dyadic, y::Dyadic)
    (isnan_dy(x) | isnan_dy(y)) && return 2            # unordered
    sx, sy = sign_dy(x), sign_dy(y)
    sx != sy && return sx < sy ? -1 : 1
    isinf_dy(x) && isinf_dy(y) && return 0
    isinf_dy(x) && return sx > 0 ? 1 : -1
    isinf_dy(y) && return sy > 0 ? -1 : 1
    sx == 0 && return 0                                # both zero
    ex, ey = _exponent_raw(x), _exponent_raw(y)
    if ex != ey
        m = ex < ey ? -1 : 1
        return sx > 0 ? m : -m
    end
    ax, ay = mag_dy(x.S), mag_dy(y.S)
    if x.Q >= y.Q
        ax <<= (x.Q - y.Q)
    else
        ay <<= (y.Q - x.Q)
    end
    m = ax == ay ? 0 : (ax < ay ? -1 : 1)
    sx > 0 ? m : -m
end
Base.:(==)(x::Dyadic, y::Dyadic) = cmp_dy(x, y) == 0
Base.:(<)(x::Dyadic, y::Dyadic)  = cmp_dy(x, y) == -1
Base.:(<=)(x::Dyadic, y::Dyadic) = cmp_dy(x, y) <= 0

# the SORTING order (NaN last, as for every AbstractFloat), and the isequal /
# isunordered / max / min contracts that go with it
@inline function Base.isless(x::Dyadic, y::Dyadic)
    c = cmp_dy(x, y)
    c == 2 ? (!isnan_dy(x) & isnan_dy(y)) : c == -1
end
@inline Base.isequal(x::Dyadic, y::Dyadic) =
    isnan_dy(x) ? isnan_dy(y) : cmp_dy(x, y) == 0
@inline Base.isunordered(x::Dyadic) = isnan_dy(x)
@inline Base.max(x::Dyadic, y::Dyadic) =
    (isnan_dy(x) | isnan_dy(y)) ? DYADIC_NAN : (cmp_dy(x, y) == -1 ? y : x)
@inline Base.min(x::Dyadic, y::Dyadic) =
    (isnan_dy(x) | isnan_dy(y)) ? DYADIC_NAN : (cmp_dy(x, y) == 1 ? y : x)
@inline Base.minmax(x::Dyadic, y::Dyadic) =
    (isnan_dy(x) | isnan_dy(y)) ? (DYADIC_NAN, DYADIC_NAN) :
        (cmp_dy(x, y) == 1 ? (y, x) : (x, y))

# ---- Base arithmetic: TOTAL (BigFloat result at exact precision), so escaped
# values compose; the engine uses the partial kernels above by name
@inline function _bigspan(x::Dyadic, y::Dyadic)
    lo = min(x.Q, y.Q)
    hi = max(x.Q + nbits_dy(x.S), y.Q + nbits_dy(y.S))
    max(Int(hi - lo) + 1, 2)
end
function Base.:+(x::Dyadic, y::Dyadic)
    (isfinite_dy(x) & isfinite_dy(y)) || return BigFloat(x) + BigFloat(y)
    setprecision(() -> BigFloat(x) + BigFloat(y), BigFloat, _bigspan(x, y))
end
Base.:-(x::Dyadic, y::Dyadic) = x + (-y)
function Base.:*(x::Dyadic, y::Dyadic)
    (isfinite_dy(x) & isfinite_dy(y)) || return BigFloat(x) * BigFloat(y)
    p = max(nbits_dy(x.S) + nbits_dy(y.S), 2)
    setprecision(() -> BigFloat(x) * BigFloat(y), BigFloat, p)
end

"""`x · 2^n`, exactly and unconditionally: an exponent-field add, no range to leave."""
@inline function Base.ldexp(x::Dyadic, n::Integer)
    isfinite_dy(x) || return x
    _rawdyadic(x.S, x.Q + Int64(n), DY_FINITE)
end

@inline _exponent_raw(x::Dyadic) = x.Q + nbits_dy(x.S) - 1
"""⌊log₂|x|⌋; undefined for zero and the non-finite rows (throws)."""
@inline function exponent_dy(x::Dyadic)
    isfinite_dy(x) && !iszero(x.S) ||
        throw(DomainError(x, "Dyadic exponent is defined only for finite nonzero values"))
    _exponent_raw(x)
end
Base.exponent(x::Dyadic) = exponent_dy(x)

# ---- integer rounding: pure integer arithmetic, no allocation ----------------
# Q ≥ 0 is already an integer (the operand IS the answer; never re-form as
# S << Q). -Q ≥ 128 puts the whole significand below the point: 0 < |x| < ½.
const _DY_TINY = -1

# split a finite NON-INTEGER x as q + r/2^sh with q = ⌊x⌋, 0 ≤ r < 2^sh;
# precondition x.Q < 0, x.S ≠ 0. Tests the ORIGINAL Q before negating it.
@inline function _split_dy(x::Dyadic)
    x.Q <= -128 && return (x.S < 0 ? -one(Int128) : zero(Int128), one(Int128), _DY_TINY)
    sh = -Int(x.Q)                                         # 1:127
    q = x.S >> sh                                          # arithmetic shift floors
    (q, x.S - (q << sh), sh)
end
@inline _int_dy(q::Int128) = _rawdyadic(q, Int64(0), DY_FINITE)
@inline _rounds_to_self(x::Dyadic) = !isfinite_dy(x) || x.Q >= 0 || iszero(x.S)

function Base.floor(x::Dyadic)
    _rounds_to_self(x) && return x
    q, _, _ = _split_dy(x)
    _int_dy(q)
end
function Base.ceil(x::Dyadic)
    _rounds_to_self(x) && return x
    q, r, _ = _split_dy(x)
    _int_dy(iszero(r) ? q : q + one(Int128))
end
function Base.trunc(x::Dyadic)
    _rounds_to_self(x) && return x
    q, r, _ = _split_dy(x)
    _int_dy((x.S < 0) & !iszero(r) ? q + one(Int128) : q)
end
"""Round half to even, matching `Base.round(::AbstractFloat)`."""
function Base.round(x::Dyadic)
    _rounds_to_self(x) && return x
    q, r, sh = _split_dy(x)
    sh == _DY_TINY && return DYADIC_ZERO                   # 0 < |x| < ½: no tie possible
    iszero(r) && return _int_dy(q)
    half = one(Int128) << (sh - 1)                         # r vs 2^(sh-1), not 2r vs 2^sh
    up = r > half || (r == half && !iseven(q))
    _int_dy(up ? q + one(Int128) : q)
end
Base.round(x::Dyadic, ::RoundingMode{:Down})    = floor(x)
Base.round(x::Dyadic, ::RoundingMode{:Up})      = ceil(x)
Base.round(x::Dyadic, ::RoundingMode{:ToZero})  = trunc(x)
Base.round(x::Dyadic, ::RoundingMode{:Nearest}) = round(x)
# AIFloats: ties away from zero — needed by the Base `round(x, RoundNearestTiesAway)`
# veneer at rung 3. Same split; a tie goes to the larger magnitude.
function Base.round(x::Dyadic, ::RoundingMode{:NearestTiesAway})
    _rounds_to_self(x) && return x
    q, r, sh = _split_dy(x)
    sh == _DY_TINY && return DYADIC_ZERO
    iszero(r) && return _int_dy(q)
    half = one(Int128) << (sh - 1)
    # q = ⌊x⌋; for x < 0 the tie (r == half) is nearer −∞ in magnitude terms
    up = r > half || (r == half && x.S > 0)
    _int_dy(up ? q + one(Int128) : q)
end

# ---- conversions: exact in both directions for every value the engine forms
function Base.BigFloat(x::Dyadic)
    x.kind == DY_NAN    && return BigFloat(NaN)
    x.kind == DY_POSINF && return BigFloat(Inf)
    x.kind == DY_NEGINF && return BigFloat(-Inf)
    iszero(x.S) && return BigFloat(0)
    p = max(nbits_dy(x.S) + 1, 2)
    setprecision(BigFloat, p) do
        ldexp(BigFloat(x.S), x.Q)
    end
end
# out to an ordinary binary float: the fast path only where NO rounding occurs
# on either route (Base.ldexp is not correctly rounded at the underflow
# boundary), else a SINGLE rounding through the exact BigFloat
function _dyadic_to(::Type{T}, x::Dyadic) where {T<:AbstractFloat}
    x.kind == DY_NAN    && return T(NaN)
    x.kind == DY_POSINF && return T(Inf)
    x.kind == DY_NEGINF && return T(-Inf)
    iszero(x.S) && return zero(T)
    _exact_in(T, x) && return ldexp(T(x.S), x.Q)
    T(BigFloat(x))
end
@inline function _exact_in(::Type{T}, x::Dyadic) where {T<:AbstractFloat}
    nb = nbits_dy(x.S)
    nb <= Base.precision(T) || return false
    e = x.Q + nb - 1
    Base.exponent(floatmin(T)) <= e <= Base.exponent(floatmax(T))
end
Base.Float64(x::Dyadic) = _dyadic_to(Float64, x)
Base.Float32(x::Dyadic) = _dyadic_to(Float32, x)
Base.Float16(x::Dyadic) = _dyadic_to(Float16, x)
# `float(::Dyadic)` is deliberately NOT defined: the generic rounding core's
# zero row would otherwise silently re-open a path this carrier must not take
Base.big(x::Dyadic) = BigFloat(x)

"""`(S, Q, 1)`; `den == 0` signals non-finite, as Base's contract requires."""
function Base.decompose(x::Dyadic)
    x.kind == DY_NAN    && return (Int128(0), 0, Int128(0))
    x.kind == DY_POSINF && return (Int128(1), 0, Int128(0))
    x.kind == DY_NEGINF && return (Int128(-1), 0, Int128(0))
    (x.S, Int(x.Q), Int128(1))
end

# ---- Dyadic ↔ Rational: the exact bridge, both directions ---------------------
_fit_rat(::Type{BigInt}, n::BigInt, _) = n
_fit_rat(::Type{T}, n::BigInt, what) where {T<:Integer} =
    typemin(T) <= n <= typemax(T) ? T(n) :
        throw(OverflowError("dyadic_to_rational: the $what needs " *
                            "$(ndigits(n; base=2)) bits, which Rational{$T} " *
                            "cannot hold; use Rational{BigInt}"))

"""
    dyadic_to_rational([T=BigInt,] x::Dyadic) -> Rational{T}

The exact value as a rational. `±Inf` map to `±1//0` (as Base does); NaN
throws. A narrow `T` is checked, never wrapped. The reduction is a shift.
"""
function dyadic_to_rational(::Type{T}, x::Dyadic) where {T<:Integer}
    x.kind == DY_NAN && throw(InexactError(:dyadic_to_rational, Rational{T}, x))
    x.kind == DY_POSINF && return Base.unsafe_rational(one(T), zero(T))
    x.kind == DY_NEGINF && return (T <: Unsigned || T === Bool) ?
        throw(InexactError(:dyadic_to_rational, Rational{T}, x)) :
        Base.unsafe_rational(-one(T), zero(T))
    iszero(x.S) && return Base.unsafe_rational(zero(T), one(T))
    n, q = BigInt(x.S), Int(x.Q)
    if q >= 0
        Base.unsafe_rational(_fit_rat(T, n << q, "numerator"), one(T))
    else
        k = min(trailing_zeros(n), -q)
        Base.unsafe_rational(_fit_rat(T, n >> k, "numerator"),
                             _fit_rat(T, BigInt(1) << (-q - k), "denominator"))
    end
end
dyadic_to_rational(x::Dyadic) = dyadic_to_rational(BigInt, x)

"""Whether `q` is exactly a [`Dyadic`](@ref): its denominator is a power of two (`±1//0` count)."""
isdyadic(q::Rational) = iszero(denominator(q)) || ispow2(denominator(q))

"""The exact `Dyadic` for a dyadic rational; refuses (InexactError) rather than rounds."""
function rational_to_dyadic(q::Rational)
    n, d = numerator(q), denominator(q)
    if iszero(d)
        iszero(n) && throw(InexactError(:rational_to_dyadic, Dyadic, q))
        return n > 0 ? DYADIC_POSINF : DYADIC_NEGINF
    end
    iszero(n) && return DYADIC_ZERO
    ispow2(d) || throw(InexactError(:rational_to_dyadic, Dyadic, q))
    k = trailing_zeros(d)
    nb = BigInt(n)
    tz = trailing_zeros(nb)
    s = nb >> tz
    typemin(Int128) <= s <= typemax(Int128) || throw(InexactError(:rational_to_dyadic, Dyadic, q))
    Q = tz - k
    typemin(Int64) <= Q <= typemax(Int64) ||
        throw(OverflowError("rational_to_dyadic: exponent $Q exceeds Int64"))
    Dyadic(Int128(s), Int64(Q))
end
Base.Rational{T}(x::Dyadic) where {T<:Integer} = dyadic_to_rational(T, x)
Dyadic(q::Rational) = rational_to_dyadic(q)

# ---- from a binary float: exact, since every binary float IS a dyadic rational
dyadic_from(x::Dyadic) = x
function dyadic_from(x::Base.IEEEFloat)
    isnan(x) && return DYADIC_NAN
    isinf(x) && return x > 0 ? DYADIC_POSINF : DYADIC_NEGINF
    iszero(x) && return DYADIC_ZERO
    num, pow, den = Base.decompose(x)
    n = Int128(num) * sign(den)             # den is ±1; its SIGN is the value's
    tz = trailing_zeros(n)
    _rawdyadic(n >> tz, Int64(pow) + tz, DY_FINITE)
end
function dyadic_from(x::AbstractFloat)
    isnan(x) && return DYADIC_NAN
    isinf(x) && return x > 0 ? DYADIC_POSINF : DYADIC_NEGINF
    iszero(x) && return DYADIC_ZERO
    num, pow, den = Base.decompose(x)
    n = BigInt(num) * sign(den)
    # normalize: decompose(::BigFloat) returns the numerator at full allocated
    # precision, trailing zeros included — those are exponent, not significand
    tz = trailing_zeros(n)
    if tz > 0
        n >>= tz
        pow += tz
    end
    _fits_int128(n) || throw(InexactError(:Dyadic, Dyadic,
        "significand needs $(ndigits(n; base=2)) bits after normalization, " *
        "which exceeds Int128; Dyadic is the carrier for P3109 datums (≤ 16 " *
        "significand bits) and their exact combinations, not for arbitrary reals"))
    _rawdyadic(Int128(n), Int64(pow), DY_FINITE)
end
@inline _fits_int128(n::BigInt) = ndigits(n; base=2) <= 127
Dyadic(x::AbstractFloat) = dyadic_from(x)
Dyadic(x::Integer) = Dyadic(Int128(x), Int64(0))

# ---- AIFloats additions: the Base-surface conveniences the veneers reach
# (compat/base.jl) at rung 3. None is used by the engine's kernels.
@inline function Base.copysign(x::Dyadic, y::Dyadic)
    isnan_dy(x) && return x
    signbit(y) ? -abs(x) : abs(x)
end
Base.isone(x::Dyadic) = isfinite_dy(x) && cmp_dy(x, DYADIC_ONE) == 0
"""`significand(x) ∈ [1, 2)`, exactly (an exponent-field move)."""
Base.significand(x::Dyadic) = isfinite_dy(x) && !iszero(x.S) ? ldexp(x, -_exponent_raw(x)) : x
"""`(f, e)` with `x == f · 2^e`, `f ∈ [½, 1)`, exactly."""
function Base.frexp(x::Dyadic)
    (isfinite_dy(x) && !iszero(x.S)) || return (x, 0)
    e = _exponent_raw(x) + 1
    (ldexp(x, -e), Int(e))
end
(::Type{T})(x::Dyadic) where {T<:Integer} = T(BigFloat(x))
Base.Bool(x::Dyadic) = Bool(BigFloat(x))

Base.show(io::IO, x::Dyadic) =
    x.kind == DY_NAN    ? print(io, "Dyadic(NaN)") :
    x.kind == DY_POSINF ? print(io, "Dyadic(Inf)") :
    x.kind == DY_NEGINF ? print(io, "Dyadic(-Inf)") :
    print(io, "Dyadic(", x.S, " * 2^", x.Q, ")")

end # module DyadicNumbers
