# the carrier lattice: what holds a datum in flight
#
# The carrier is a property of values in flight, not of formats at rest, and it
# is a function of the exponent bias B — not of the bitwidth K. K counts code
# points; B says how far apart they can be.
#
# The criterion: a datum satisfies |X| < 2^B, and an operation's worst-case
# intermediate is a monomial in n datum factors, which fits a carrier with
# maximum exponent emax exactly when ΣBᵢ ≤ emax. Stated on 2B so it is visibly
# the n = 2 case (Multiply/Divide) of the span rule:
#
#   rung 1  Float64    emax  1024
#   rung 2  Float128   emax 16384
#   rung 3  unbounded  (exact carrier)
#
# Rung 3's carrier is Dyadic (carriers/dyadic.jl); BigFloat held the rung
# through Phase 6 and is the differential oracle for its replacement — the
# same succession SmallFloats itself went through.

"""
    Head

Supertype of the carrier-selection tags. Its three singletons name the rungs:
`HeadF64` (Float64), `HeadF128` (Float128), `HeadExact` (the exact carrier).

Not exported.
"""
abstract type Head end
struct HeadF64   <: Head end
struct HeadF128  <: Head end
struct HeadExact <: Head end

carriertype(::HeadF64)   = Float64
carriertype(::HeadF128)  = Float128
carriertype(::HeadExact) = Dyadic
carriertype(::Type{H}) where {H<:Head} = carriertype(H())

rungindex(::HeadF64)   = 1
rungindex(::HeadF128)  = 2
rungindex(::HeadExact) = 3

joinhead(a::Head, b::Head) = rungindex(a) >= rungindex(b) ? a : b

@inline _rungindex_span(ΣB::Int) = ΣB <= 1024 ? 1 : ΣB <= 16384 ? 2 : 3
@inline _rungindex(::Type{F}) where {F<:Binary} = _rungindex_span(2 * ExponentBiasOf(F))

# Val barrier: no trait returns a Type (or a tag) from a ternary — each method
# has exactly one concrete return type.
"""
    rung(F)

The carrier rung of format `F` — the tag naming the narrowest carrier whose
exponent range holds any two-factor monomial of `F`'s datums exactly.

Not exported; call it as `AIFloats.rung`.
"""
rung(::Type{F}) where {F<:Binary} = _rung(Val(_rungindex(F)), F)
rung(b::Binary) = rung(typeof(b))
_rung(::Val{1}, _) = HeadF64()
_rung(::Val{2}, _) = HeadF128()
_rung(::Val{3}, _) = HeadExact()

"""
    datumcarrier(F)

The type `decode` returns for format `F`: the narrowest carrier that represents
every datum of `F` exactly and leaves room for two-factor products.

`Float64` for B ≤ 512, `Float128` for B ≤ 8192, the exact `Dyadic` carrier
above (a `Real`, not an `AbstractFloat`). Internal counterpart of the public
[`ValueType`](@ref); evaluation decisions use this, never `ValueType`. Not
exported.
"""
datumcarrier(::Type{F}) where {F<:Binary} = carriertype(rung(F))
datumcarrier(b::Binary) = datumcarrier(typeof(b))

# the two carrier traits stay distinct. `datumcarrier` is INTERNAL — what
# decode returns and ωeval computes on; the plan lets it become Dyadic, which
# is Real but not AbstractFloat. `promotecarrier` is PUBLIC — the target of
# promote_rule for `datum ⋄ external number`, and always a real Julia float,
# so `x + 1.0` on a wide format promotes to something with the whole Real
# interface. Routing both through one trait would force that surface onto an
# internal carrier.
"""
    promotecarrier(F)

The public promotion target for format `F` against external numeric types —
what `x + 1.0` promotes to. Always a Julia float with the complete `Real`
interface: `Float64` for B ≤ 512, `Float128` for B ≤ 8192, `BigFloat` above.
Never the internal exact carrier. Not exported.
"""
promotecarrier(::Type{F}) where {F<:Binary} = _promotecarrier(rung(F))
promotecarrier(b::Binary) = promotecarrier(typeof(b))
_promotecarrier(::HeadF64)   = Float64
_promotecarrier(::HeadF128)  = Float128
_promotecarrier(::HeadExact) = BigFloat

# carrier-generic special values. Bare NaN/Inf literals are Float64 — on a wider
# carrier they would narrow-then-widen silently, so every special is built at
# the carrier.
_cnan(::Type{C})  where {C<:AbstractFloat} = C(NaN)
_cinf(::Type{C})  where {C<:AbstractFloat} = C(Inf)
_cninf(::Type{C}) where {C<:AbstractFloat} = C(-Inf)
_czero(::Type{C}) where {C<:AbstractFloat} = zero(C)
_cnan(::Type{Dyadic})  = DyadicNumbers.DYADIC_NAN
_cinf(::Type{Dyadic})  = DyadicNumbers.DYADIC_POSINF
_cninf(::Type{Dyadic}) = DyadicNumbers.DYADIC_NEGINF
_czero(::Type{Dyadic}) = DyadicNumbers.DYADIC_ZERO

# the four types a datum can be in flight. Rows written against this rather
# than AbstractFloat are the ones that must also accept Dyadic.
const CarrierValue = Union{Float64, Float128, BigFloat, Dyadic}

# ---- exact binary128 representation adapter ---------------------------------
# Quadmath arithmetic functions are not part of this adapter. IEEE binary128
# layout is decoded directly, so the result is the exact represented value and
# no rounding assumption is involved. Keeping this knowledge here prevents the
# sign/exponent/significand rules from leaking into projection and block code.
@inline function _dyadic128(x::Float128)::Dyadic
    u = reinterpret(UInt128, x)
    neg = (u >> 127) != 0
    be = Int((u >> 112) & UInt128(0x7fff))
    frac = u & ((UInt128(1) << 112) - 1)
    if be == 0x7fff
        frac != 0 && return DyadicNumbers.DYADIC_NAN
        return neg ? DyadicNumbers.DYADIC_NEGINF : DyadicNumbers.DYADIC_POSINF
    end
    be == 0 && frac == 0 && return DyadicNumbers.DYADIC_ZERO
    sig = be == 0 ? frac : frac | (UInt128(1) << 112)
    q = be == 0 ? -16494 : be - 16383 - 112
    tz = trailing_zeros(sig)
    sig >>= tz
    q += tz
    s = Int128(sig)
    Dyadic(neg ? -s : s, q)
end

"""Return the identical normal Float64 value, or `nothing` without rounding."""
@inline function _try_f64_exact(x::Float128)::Union{Float64,Nothing}
    isfinite(x) && !iszero(x) || return nothing
    d = _dyadic128(x)
    a = d.S < 0 ? -d.S : d.S
    n = 128 - leading_zeros(UInt128(a))
    n <= 53 || return nothing
    e = Int(d.Q) + n - 1
    -1022 <= e <= 1023 || return nothing       # subnormals deliberately refuse
    m = UInt64(a) << (53 - n)
    u = (d.S < 0 ? UInt64(1) << 63 : UInt64(0)) |
        (UInt64(e + 1023) << 52) |
        (m & ((UInt64(1) << 52) - 1))
    reinterpret(Float64, u)
end

# signed-infinity predicates total over the carriers (`x == Inf` would need a
# promotion Dyadic deliberately lacks)
@inline _isposinf(x) = isinf(x) & !signbit(x)
@inline _isneginf(x) = isinf(x) & signbit(x)

# conversions out of the exact carrier for the types dyadic.jl cannot see.
# `_dyadic_to` is generic over `T<:AbstractFloat` and already carries the rule
# these need: take `ldexp` only where NO rounding occurs on either route, and
# otherwise take a SINGLE rounding through the exact BigFloat. Going straight to
# `T(BigFloat(x))` here skipped its exact branch and cost 196 ns / 13
# allocations against the 3.3 ns the identical `Float64` method already
# achieved (float128use.md §5).
(::Type{Float128})(x::Dyadic) = DyadicNumbers._dyadic_to(Float128, x)
(::Type{BFloat16})(x::Dyadic) = DyadicNumbers._dyadic_to(BFloat16, x)

# ---- lift: the carrier join, UPWARD ONLY ------------------------------------
# Every method is exact by construction. There is deliberately no narrowing
# method: a narrowing lift is a silent rounding on a path that believes it is
# exact, and a MethodError at the call site is the cheapest way to be told.
"""
    lift(h::Head, x) -> carriertype(h)

Move a carrier value **up** to the rung `h`, exactly. No narrowing method
exists, by design. Not exported.
"""
@inline lift(::HeadF64,   x::Float64)  = x
@inline lift(::HeadF128,  x::Float64)  = Float128(x)
@inline lift(::HeadF128,  x::Float128) = x
@inline lift(::HeadExact, x::Float64)  = Dyadic(x)
@inline lift(::HeadExact, x::Float128) = _dyadic128(x)
@inline lift(::HeadExact, x::BigFloat) = Dyadic(x)
@inline lift(::HeadExact, x::Dyadic)   = x

# the head a value in flight sits on, and the join over several
@inline _headof(::Float64)  = HeadF64()
@inline _headof(::Float128) = HeadF128()
@inline _headof(::BigFloat) = HeadExact()
@inline _headof(::Dyadic)   = HeadExact()
@inline _joinheads(x) = _headof(x)
@inline _joinheads(x, ys...) = joinhead(_headof(x), _joinheads(ys...))
