# ωRoundToPrecision — the generic family
#
# One core, exact for any exact input, over every float carrier (Float64,
# Float128, BigFloat). The value is scaled onto the target grid by an exact
# power-of-two scaling; the fractional part ν and the sticky direction νs feed
# one predicate per rounding-mode class.
#
# A second, bit-level fixed-point family (`_rab`, below) serves the Float64
# and Dyadic hot paths; it is pinned bit-identical to this one by the
# exhaustive gate in test/test-rounding-paths.jl. THIS family is total and is
# the semantics; any semantic edit must land in BOTH families.

# ---- sticky-aware comparisons ----------------------------------------------
# the true fraction is ν + νs·ε, ε infinitesimal
@inline _νgt(ν, νs::Int, c) = ν > c || (ν == c && νs > 0)
@inline _νeq(ν, νs::Int, c) = ν == c && νs == 0
@inline _νge(ν, νs::Int, c) = ν > c || (ν == c && νs >= 0)

# ---- the RTE/RTO evenness predicate ----------------------------------------
# "ties to even" means ties to the even CODE POINT. For P > 1 that is an even
# significand; for P == 1 there is no significand bit — every datum is a power
# of two — so evenness is evenness of the biased exponent (zero counts even).
@inline _codeiseven(Sfl::Int64, Q::Int64, B::Int, P::Int) =
    P > 1 ? iseven(Sfl) : (Sfl == 0 || iseven(Q + B))

# ---- stochastic sub-grid helpers -------------------------------------------
# ⌊(ν + νs·ε)·2^N⌋ — the step-down applies when the scaled fraction lands
# exactly on the grid but the true value is strictly below it
@inline function _νfloorscaled(ν, νs::Int, N::Int)
    s = ldexp(ν, N)
    f = floor(s)
    r = Int64(f)
    (νs < 0 && s == f) ? r - 1 : r
end

# round-nearest-ties-even of (ν + νs·ε)·2^N
@inline function _νrnite(ν, νs::Int, N::Int)
    s = ldexp(ν, N)
    f = floor(s)
    k = Int64(f)
    r = s - f
    half = oftype(r, 0.5)
    away = r > half || (r == half && (νs > 0 || (νs == 0 && isodd(k))))
    away ? k + 1 : k
end

# ---- one predicate per mode ------------------------------------------------
# away == true means: round the magnitude up (to Sfl + 1 on the target grid)
@inline _roundaway(::ρRTZ, ν, νs, Sfl, Q, B, P, sign, R) = false
@inline _roundaway(::ρRTP, ν, νs, Sfl, Q, B, P, sign, R) = _νgt(ν, νs, 0) && sign > 0
@inline _roundaway(::ρRTN, ν, νs, Sfl, Q, B, P, sign, R) = _νgt(ν, νs, 0) && sign < 0
@inline _roundaway(::ρRTA, ν, νs, Sfl, Q, B, P, sign, R) = _νge(ν, νs, oftype(ν, 0.5))
@inline _roundaway(::ρRTE, ν, νs, Sfl, Q, B, P, sign, R) =
    _νgt(ν, νs, oftype(ν, 0.5)) ||
    (_νeq(ν, νs, oftype(ν, 0.5)) && !_codeiseven(Sfl, Q, B, P))
@inline _roundaway(::ρRTO, ν, νs, Sfl, Q, B, P, sign, R) =
    _νgt(ν, νs, 0) && _codeiseven(Sfl, Q, B, P)
@inline _roundaway(::ρRSA{N}, ν, νs, Sfl, Q, B, P, sign, R) where {N} =
    _νfloorscaled(ν, νs, N) + R >= Int64(1) << N
@inline _roundaway(::ρRSB{N}, ν, νs, Sfl, Q, B, P, sign, R) where {N} =
    _νfloorscaled(ν, νs, N + 1) + (2R + 1) >= Int64(1) << (N + 1)
@inline _roundaway(::ρRSC{N}, ν, νs, Sfl, Q, B, P, sign, R) where {N} =
    _νrnite(ν, νs, N) + R >= Int64(1) << N

# ---- the core ---------------------------------------------------------------
# ⌊log₂|a|⌋ via frexp — total over normals AND subnormals on every carrier
@inline function _floorexp(a)
    _, ex = frexp(a)
    ex - 1
end

function _rtp_core(P::Int, B::Int, μ::RoundingMode, X, R::Int, sticky::Int)
    isnan(X) && return ROUNDED_NAN
    if isinf(X)
        if X > 0
            # +Inf with sticky < 0: the true value is finite and over-large —
            # a finite sentinel beyond every format, so it saturates
            sticky < 0 && return Rounded(KIND_FIN, Int8(1), (Int64(1) << P) - 1, HUGEQ)
            return ROUNDED_PINF
        else
            sticky > 0 && return Rounded(KIND_FIN, Int8(-1), (Int64(1) << P) - 1, HUGEQ)
            return ROUNDED_NINF
        end
    end

    local sign::Int, Sfl::Int64, Q::Int64, ν, νs::Int
    if iszero(X)
        sticky == 0 && return ROUNDED_ZERO
        # |true value| ∈ (0, ε): on the grid at the subnormal floor, fraction 0⁺
        sign = sticky > 0 ? 1 : -1
        Q = Int64(2 - B - P)
        Sfl = Int64(0)
        ν = zero(X)                     # zero of the carrier
        νs = 1
    else
        sign = X > 0 ? 1 : -1
        a = abs(X)
        e = _floorexp(a)
        Q = Int64(max(e, 1 - B) - P + 1)
        S̃ = ldexp(a, -Int(Q))          # exact power-of-two scaling
        f = floor(S̃)
        Sfl = Int64(f)
        ν = S̃ - f                      # exact fraction
        νs = sticky == 0 ? 0 : sticky * sign   # sticky in the |value| direction
        if νs < 0 && iszero(ν)
            # the true magnitude is just below an exact grid point: back up one
            # ulp on the target grid (borrowing across a binade edge), ν = 1⁻
            if Sfl == Int64(1) << (P - 1) && Q > 2 - B - P
                Q -= 1
                Sfl = (Int64(1) << P) - 1
            else
                Sfl -= 1
            end
            ν = one(ν)
            νs = -1
        end
    end

    away = _roundaway(μ, ν, νs, Sfl, Q, Int(B), P, sign, R)
    S = away ? Sfl + 1 : Sfl
    if S == Int64(1) << P               # carry into the next binade
        S = Int64(1) << (P - 1)
        Q += 1
    end
    S == 0 && return ROUNDED_ZERO
    Rounded(KIND_FIN, Int8(sign), S, Q)
end

# ---- the fixed-point family: ν as a UInt128 fraction + a `lost` bit ----------
# PROVENANCE: SmallFloats.jl src/project.jl (commit 7f864f08, 2026-08-27),
# `_rab`/`_rtp_f64`/`_rtp_dyadic` — restyled to AIFloats mode names, algorithms
# unchanged. Twins of `_roundaway` above on (fraction, sticky) evidence; the
# carrier differs ((ν::UInt128, lost) here vs an exact float ν there).
const _HALF128 = UInt128(1) << 127
# true fraction = ν·2^-128 (+ lost bits) + νs·ε
@inline _bgt(ν::UInt128, lost::Bool, νs::Int, c::UInt128) = ν > c || (ν == c && (lost | (νs > 0)))
@inline _beq(ν::UInt128, lost::Bool, νs::Int, c::UInt128) = ν == c && !lost && νs == 0
@inline _bge(ν::UInt128, lost::Bool, νs::Int, c::UInt128) = ν > c || (ν == c && (lost | (νs >= 0)))
@inline function _bfloorscaled(ν::UInt128, lost::Bool, νs::Int, N::Int)
    k = Int64(ν >> (128 - N))
    (νs < 0 && !lost && (ν << N) == 0 && k > 0) && return k - 1   # exact grid hit, true below
    k
end
@inline function _brnite(ν::UInt128, lost::Bool, νs::Int, N::Int)
    k = Int64(ν >> (128 - N))
    rbit = (ν >> (127 - N)) & 0x1
    rbit == 0 && return k                                # fr < ½ regardless of ε
    low = ν << (N + 1)
    (low != 0 || lost || νs > 0) && return k + 1         # fr > ½
    νs < 0 && return k                                   # fr = ½ − ε
    isodd(k) ? k + 1 : k                                 # exact tie → even
end

@inline _rab(::ρRTZ, ν, lost, νs, Sfl, Q, B, P, sign, R) = false
@inline _rab(::ρRTP, ν, lost, νs, Sfl, Q, B, P, sign, R) = _bgt(ν, lost, νs, UInt128(0)) && sign > 0
@inline _rab(::ρRTN, ν, lost, νs, Sfl, Q, B, P, sign, R) = _bgt(ν, lost, νs, UInt128(0)) && sign < 0
@inline _rab(::ρRTA, ν, lost, νs, Sfl, Q, B, P, sign, R) = _bge(ν, lost, νs, _HALF128)
@inline _rab(::ρRTE, ν, lost, νs, Sfl, Q, B, P, sign, R) =
    _bgt(ν, lost, νs, _HALF128) || (_beq(ν, lost, νs, _HALF128) && !_codeiseven(Sfl, Q, B, P))
@inline _rab(::ρRTO, ν, lost, νs, Sfl, Q, B, P, sign, R) =
    _bgt(ν, lost, νs, UInt128(0)) && _codeiseven(Sfl, Q, B, P)
@inline _rab(::ρRSA{N}, ν, lost, νs, Sfl, Q, B, P, sign, R) where {N} =
    _bfloorscaled(ν, lost, νs, N) + R >= Int64(1) << N
@inline _rab(::ρRSB{N}, ν, lost, νs, Sfl, Q, B, P, sign, R) where {N} =
    _bfloorscaled(ν, lost, νs, N + 1) + (2R + 1) >= Int64(1) << (N + 1)
@inline _rab(::ρRSC{N}, ν, lost, νs, Sfl, Q, B, P, sign, R) where {N} =
    _brnite(ν, lost, νs, N) + R >= Int64(1) << N

# the Float64 bit path: mask-extracted guard/round/sticky. Precondition: X is
# finite, nonzero, NORMAL (the entry point routes everything else to the core).
function _rtp_f64(P::Int, B::Int, μ::RoundingMode, X::Float64, R::Int, sticky::Int)
    sign = X > 0.0 ? 1 : -1
    u = reinterpret(UInt64, abs(X))
    e = Int(u >> 52) - 1023
    m = (u & ((UInt64(1) << 52) - 1)) | (UInt64(1) << 52)    # 53-bit significand
    Q = Int64(max(e, 1 - B) - P + 1)
    d = e - Int(Q)                                           # units-bit position, ≤ P−1
    local Sfl::Int64, νfix::UInt128
    lost = false
    if d >= 0
        t = 52 - d                                           # ∈ [37, 52] at P ≤ 16
        Sfl = Int64(m >> t)
        νfix = UInt128(m & ((UInt64(1) << t) - 1)) << (128 - t)
    else
        Sfl = 0
        t = 52 - d                                           # > 52
        if t <= 128
            νfix = UInt128(m) << (128 - t)
        else
            sh = t - 128
            if sh >= 64
                νfix = UInt128(0); lost = true               # m ≠ 0 here
            else
                νfix = UInt128(m >> sh)
                lost = (m & ((UInt64(1) << sh) - 1)) != 0
            end
        end
    end
    νs = sticky == 0 ? 0 : sticky * sign
    # step-down for "true value just below an exact dyadic" — the identical
    # block in _rtp_core and _rtp_dyadic; all three must agree
    if νs < 0 && νfix == UInt128(0) && !lost
        if Sfl == Int64(1) << (P - 1) && Q > Int64(2 - B - P)
            Q -= 1
            Sfl = (Int64(1) << P) - 1
        else
            Sfl -= 1                                          # Sfl ≥ 1 here
        end
        νfix = typemax(UInt128); lost = false; νs = -1        # ν = 1⁻
    end
    away = _rab(μ, νfix, lost, νs, Sfl, Q, B, P, sign, R)
    S = away ? Sfl + 1 : Sfl
    if S == Int64(1) << P
        S = Int64(1) << (P - 1); Q += 1
    end
    S == 0 && return ROUNDED_ZERO
    Rounded(KIND_FIN, Int8(sign), S, Q)
end

# the zero-with-sticky row, written once and asserted equal to _rtp_core's
@inline function _rtp_zero_sticky(P::Int, B::Int, μ::RoundingMode, R::Int, sticky::Int)
    sticky == 0 && return ROUNDED_ZERO
    sign = sticky > 0 ? 1 : -1
    Q = Int64(2 - B - P)
    away = _rab(μ, UInt128(0), false, 1, Int64(0), Q, B, P, sign, R)  # |true| ∈ (0, ε)
    away || return ROUNDED_ZERO
    Rounded(KIND_FIN, Int8(sign), Int64(1), Q)
end

# the Dyadic path: X = S · 2^Q_d with S an exact integer, so scaling to the
# target grid is a SHIFT and the bits shifted out ARE ν as an exact fixed-point
# fraction — the same evidence shape as the bit path, one predicate family.
function _rtp_dyadic(P::Int, B::Int, μ::RoundingMode, X::Dyadic, R::Int, sticky::Int)
    sgn = Int(sign(X))
    m = abs(X.S)                                             # exact, nonzero
    nb = DyadicNumbers.nbits_dy(m)
    e = Int64(X.Q) + nb - 1                                  # ⌊log₂|X|⌋
    Q = max(e, Int64(1 - B)) - P + 1
    t = Q - Int64(X.Q)                                       # bits to shift out
    local Sfl::Int64, νfix::UInt128
    lost = false
    if t <= 0
        Sfl = Int64(m << (-t))                               # S̃ ≤ 2^P by construction
        νfix = UInt128(0)
    else
        Sfl = Int64(m >> t)
        frac = m & ((Int128(1) << t) - 1)                    # the shifted-out bits ARE ν
        if t <= 128
            νfix = UInt128(frac) << (128 - t)
        else
            sh = t - 128
            if sh >= 128
                νfix = UInt128(0); lost = !iszero(frac)
            else
                νfix = UInt128(frac >> sh)
                lost = !iszero(frac & ((Int128(1) << sh) - 1))
            end
        end
    end
    νs = sticky == 0 ? 0 : sticky * sgn
    if νs < 0 && νfix == UInt128(0) && !lost
        if Sfl == Int64(1) << (P - 1) && Q > Int64(2 - B - P)
            Q -= 1
            Sfl = (Int64(1) << P) - 1
        else
            Sfl -= 1
        end
        νfix = typemax(UInt128); lost = false; νs = -1
    end
    away = _rab(μ, νfix, lost, νs, Sfl, Q, B, P, sgn, R)
    S = away ? Sfl + 1 : Sfl
    if S == Int64(1) << P
        S = Int64(1) << (P - 1); Q += 1
    end
    S == 0 && return ROUNDED_ZERO
    Rounded(KIND_FIN, Int8(sgn), S, Q)
end

# per-carrier entry points. Float64: normal inputs take the bit path; specials,
# zero and subnormals go to the core. Float128 goes straight to the core
# (every operation it uses is exact there). BigFloat gets 8 guard bits of
# working precision. Dyadic cannot go through the core (its zero row builds
# zero(float(typeof(X))) and float(Dyadic) does not exist, by design).
function round_to_precision(P::Int, B::Int, μ::RoundingMode, X::Float64, R::Int, sticky::Int)
    (isnan(X) | isinf(X) | iszero(X)) && return _rtp_core(P, B, μ, X, R, sticky)
    ((reinterpret(UInt64, X) >> 52) & 0x7ff) == 0x000 && return _rtp_core(P, B, μ, X, R, sticky)
    _rtp_f64(P, B, μ, X, R, sticky)
end
round_to_precision(P::Int, B::Int, μ::RoundingMode, X::Float128, R::Int, sticky::Int) =
    _rtp_core(P, B, μ, X, R, sticky)
function round_to_precision(P::Int, B::Int, μ::RoundingMode, X::Dyadic, R::Int, sticky::Int)
    isnan(X) && return ROUNDED_NAN
    if isinf(X)
        if sign(X) > 0
            sticky < 0 && return Rounded(KIND_FIN, Int8(1), (Int64(1) << P) - 1, HUGEQ)
            return ROUNDED_PINF
        else
            sticky > 0 && return Rounded(KIND_FIN, Int8(-1), (Int64(1) << P) - 1, HUGEQ)
            return ROUNDED_NINF
        end
    end
    iszero(X) && return _rtp_zero_sticky(P, B, μ, R, sticky)
    _rtp_dyadic(P, B, μ, X, R, sticky)
end
round_to_precision(P::Int, B::Int, μ::RoundingMode, X::BigFloat, R::Int, sticky::Int) =
    setprecision(BigFloat, precision(X) + 8) do
        _rtp_core(P, B, μ, X, R, sticky)
    end