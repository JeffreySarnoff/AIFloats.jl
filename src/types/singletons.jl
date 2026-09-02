"""
    FormatKind

Supertype of the singleton tags that name a format's axes: [`Signedness`](@ref) and
[`Domain`](@ref).

Not exported; refer to it as `AIFloats.FormatKind`.
"""
abstract type FormatKind end

"""
    Signedness

Whether a format represents negative values. Its two instances are [`SIGNED`](@ref) and
[`UNSIGNED`](@ref).

`convert` moves between the singletons and `Bool` in both directions, with `true` meaning
signed, so `Signedness(true) === SIGNED` and `Bool(SIGNED) === true`.

Not exported; refer to it as `AIFloats.Signedness`.
"""
abstract type Signedness <: FormatKind end

"""
    Domain

Which values a format admits beyond the reals. Its two instances are [`FINITE`](@ref) and
[`EXTENDED`](@ref).

`convert` moves between the singletons and `Bool` in both directions, with `true` meaning
extended, so `Domain(true) === EXTENDED` and `Bool(EXTENDED) === true`.

Not exported; refer to it as `AIFloats.Domain`.
"""
abstract type Domain <: FormatKind end

# format signedness
struct ΣUNSIGNED <: Signedness end
struct ΣSIGNED <: Signedness end

"""
    UNSIGNED

The unsigned [`Signedness`](@ref): the format represents magnitudes only.

Having no sign bit leaves one more bit for the exponent, so an unsigned format admits
`P <= K` where a signed one admits only `P <= K - 1`.

Interchangeable with `false` wherever a signedness is expected.
"""
const UNSIGNED = ΣUNSIGNED()

"""
    SIGNED

The signed [`Signedness`](@ref): negative values are representable, at the cost of one bit.

Interchangeable with `true` wherever a signedness is expected.
"""
const SIGNED = ΣSIGNED()

"""
    ΣBool

`Union{ΣUNSIGNED, ΣSIGNED, Bool}` — what a signedness argument accepts.

This is why [`Binary`](@ref) takes either [`SIGNED`](@ref)/[`UNSIGNED`](@ref) or a plain
`Bool`; both spellings canonicalize to the same `Bool` parameter.
"""
const ΣBool = Union{ΣUNSIGNED, ΣSIGNED, Bool}
const ΣUBool = Union{ΣUNSIGNED, Bool}
const ΣSBool = Union{ΣSIGNED, Bool}

Base.convert(::Type{Bool}, x::Signedness) =
    x === SIGNED

Base.convert(::Type{Signedness}, x::Bool) =
   x ? SIGNED : UNSIGNED

Base.convert(::Type{Bool}, ::Type{ΣUNSIGNED}) = ΣUnsigned
Base.convert(::Type{Bool}, ::Type{ΣSIGNED}) = ΣSigned

Base.Bool(x::ΣUNSIGNED) = convert(Bool, ΣUNSIGNED)
Base.Bool(x::ΣSIGNED) = convert(Bool, ΣSIGNED)

Signedness(x::Bool) = convert(Signedness, x)

is_unsigned(x::Signedness) = x === UNSIGNED
is_unsigned(x::Bool) = x === ΣUnsigned

is_signed(x::Signedness) = x === SIGNED
is_signed(x::Bool) = x === ΣSigned

# format domain
struct ΔFINITE <: Domain end
struct ΔEXTENDED <: Domain end

"""
    FINITE

The finite [`Domain`](@ref): the format holds reals and NaN, and no infinities.

Interchangeable with `false` wherever a domain is expected. Displayed as `⏥`.
"""
const FINITE = ΔFINITE()

"""
    EXTENDED

The extended [`Domain`](@ref): the format's values are extended with the infinities.

"Extended" refers to the value domain, not to the bitwidth and not to the number of exponent
bits. Interchangeable with `true` wherever a domain is expected. Displayed as `∞`.
"""
const EXTENDED = ΔEXTENDED()

"""
    ΔBool

`Union{ΔFINITE, ΔEXTENDED, Bool}` — what a domain argument accepts.

This is why [`Binary`](@ref) takes either [`FINITE`](@ref)/[`EXTENDED`](@ref) or a plain
`Bool`; both spellings canonicalize to the same `Bool` parameter.
"""
const ΔBool = Union{ΔFINITE, ΔEXTENDED, Bool}
const ΔFBool = Union{ΔFINITE, Bool}
const ΔEBool = Union{ΔEXTENDED, Bool}

function Base.convert(::Type{Bool}, x::Domain)
    x === EXTENDED
end

Base.convert(::Type{Domain}, x::Bool) = x ? EXTENDED : FINITE

Base.convert(::Type{Bool}, ::Type{ΔFINITE}) = ΔFinite
Base.convert(::Type{Bool}, ::Type{ΔEXTENDED}) = ΔExtended

Base.Bool(x::ΔFINITE) = convert(Bool, ΔFINITE)
Base.Bool(x::ΔEXTENDED) = convert(Bool, ΔEXTENDED)

Domain(x::Bool) = convert(Domain, x)

is_finite(x::Domain) = x === FINITE
is_finite(x::Bool) = x === ΔFinite

is_extended(x::Domain) = x === EXTENDED
is_extended(x::Bool) = x === ΔExtended

@inline Base.string(x::Signedness) = x === SIGNED ? "SIGNED" : "UNSIGNED"
@inline Base.string(x::Domain) = x === EXTENDED ? "EXTENDED" : "FINITE"

function Base.show(io::IO, ::MIME"text/plain", S::Signedness)
    str = string(S)
    print(io, str)
end

function Base.show(io::IO, S::Signedness)
    str = string(S)
    print(io, str)
end

function Base.show(io::IO, ::MIME"text/plain", D::Domain)
    str = string(D)
    print(io, str)
end

function Base.show(io::IO, D::Domain)
    d = string(D)
    print(io, d)
end

# Projection Components (Rounding, Saturation)

"""
    ProjectionComponent

Supertype of the two halves of a [`Projection`](@ref): `AIFloats.RoundingMode` and
`AIFloats.SaturationMode`.

Not exported; refer to it as `AIFloats.ProjectionComponent`.
"""
abstract type ProjectionComponent end

"""
    RoundingMode

How a value that falls between two representable values is resolved to one of them.

Nine modes exist, in four families:

| Family | Modes |
|:--|:--|
| `ToNearestRoundingMode` | [`RTE`](@ref), [`RTA`](@ref) |
| `UnidirectionalRoundingMode` | [`RTP`](@ref), [`RTN`](@ref), [`RTZ`](@ref) |
| `ParityRoundingMode` | [`RTO`](@ref) |
| `StochasticRoundingMode` | [`RSA`](@ref), [`RSB`](@ref), [`RSC`](@ref) |

The first three families are `DeterministicRoundingMode`s. Not exported; refer to it as
`AIFloats.RoundingMode` — and note it is distinct from `Base.RoundingMode`.
"""
abstract type RoundingMode <: ProjectionComponent end

"""
    SaturationMode

What becomes of a value too large in magnitude for the format.

[`SF`](@ref) and [`SP`](@ref) are `SaturatingSaturationMode`s; [`SN`](@ref) is the one
`NonsaturatingSaturationMode`.

Not exported; refer to it as `AIFloats.SaturationMode`.
"""
abstract type SaturationMode <: ProjectionComponent end

abstract type DeterministicRoundingMode <: RoundingMode end
abstract type ToNearestRoundingMode <: DeterministicRoundingMode end
abstract type UnidirectionalRoundingMode <: DeterministicRoundingMode end
abstract type ParityRoundingMode <: DeterministicRoundingMode end
abstract type StochasticRoundingMode <: RoundingMode end

abstract type SaturatingSaturationMode <: SaturationMode end
abstract type NonsaturatingSaturationMode <: SaturationMode end

# rounding modes
struct ρRTE <: ToNearestRoundingMode end
struct ρRTA <: ToNearestRoundingMode end
struct ρRTP <: UnidirectionalRoundingMode end
struct ρRTN <: UnidirectionalRoundingMode end
struct ρRTZ <: UnidirectionalRoundingMode end
struct ρRTO <: ParityRoundingMode end
# The stochastic modes carry their random-bit budget N in the type, so a
# projection's randomness consumption is a compile-time fact and the
# pure-vs-stochastic split is static (pure ⇒ tabulable, stochastic ⇒ never).
# N is validated in the inner constructor: an out-of-range N cannot exist as a
# value. The cap 60 keeps every rounding predicate in Int64 arithmetic
# (StochasticB shifts by N + 1).
function _check_nrandbits(N)
    (N isa Int && 1 <= N <= 60) ||
        throw(ArgumentError("stochastic random-bit budget N must be an Int in 1:60, got $N"))
    nothing
end

struct ρRSA{N} <: StochasticRoundingMode
    ρRSA{N}() where {N} = (_check_nrandbits(N); new{N}())
end
struct ρRSB{N} <: StochasticRoundingMode
    ρRSB{N}() where {N} = (_check_nrandbits(N); new{N}())
end
struct ρRSC{N} <: StochasticRoundingMode
    ρRSC{N}() where {N} = (_check_nrandbits(N); new{N}())
end

ρRSA(N::Integer) = ρRSA{Int(N)}()
ρRSB(N::Integer) = ρRSB{Int(N)}()
ρRSC(N::Integer) = ρRSC{Int(N)}()

"""
    RTE

RoundToEven — to the nearest representable value; ties go to the one with an even last bit.

The unbiased default, and the same rule as IEEE 754's round-to-nearest-ties-to-even.
A `ToNearestRoundingMode`.
"""
const RTE = ρRTE()

"""
    RTA

RoundToAway — to the nearest representable value; ties go away from zero.

A `ToNearestRoundingMode`.
"""
const RTA = ρRTA()

"""
    RTP

RoundTowardPositive — to the nearest representable value at or above the exact one.

A `UnidirectionalRoundingMode`.
"""
const RTP = ρRTP()

"""
    RTN

RoundTowardNegative — to the nearest representable value at or below the exact one.

A `UnidirectionalRoundingMode`.
"""
const RTN = ρRTN()

"""
    RTZ

RoundTowardZero — truncation; magnitude never increases.

A `UnidirectionalRoundingMode`.
"""
const RTZ = ρRTZ()

"""
    RTO

RoundToOdd — an inexact result takes the odd neighbour; an exact result is left alone.
The report's predicate (\u00a74.7.4) is `RoundAway(ToOdd) = \u03bd > 0 and CodeIsEven`.

The one `ParityRoundingMode`.

!!! note "Motivation, not contract"
    Round-to-odd's practical use is avoiding double rounding: round a wide intermediate to
    odd, narrow it, and the second rounding lands where a single direct rounding would
    have. That is a property of the composition, not a guarantee this package makes about
    error magnitude or hardware cost on any particular device.
"""
const RTO = ρRTO()

"""
    RSA

StochasticA — a `StochasticRoundingMode`. Rounds away with probability

    P = \u230a\u03bd\u00b72^N\u230b / 2^N

where `\u03bd` is the exact leftover fraction. That is `\u03bd` **truncated** onto the `2^N` grid, so
`RSA` rounds away slightly less often than `\u03bd` warrants: its bias is never positive and
reaches `2^-N` in magnitude. It is the cheapest of the three — one shift, floor and
compare.

The report's predicate (\u00a74.7.4) is `RoundAway(StochasticA_{N,R}) = \u230a\u03bd\u00b72^N\u230b + R \u2265 2^N`,
with `R` the supplied random bits, `0 \u2264 R < 2^N`.

The mode carries its random-bit budget `N` in the type; this constant is the
default budget, `\u03c1RSA{8}()`. Other budgets via `AIFloats.\u03c1RSA(N)` with
`1 <= N <= 60`. Query with [`nrandbits`](@ref).

!!! warning "Not exactly unbiased"
    All three variants quantize the rounding probability onto a grid of `2^N` steps, so
    none is exactly unbiased at finite `N`. A fraction that is not on that grid — `\u03bd = 0.8`
    at `N = 3`, say — is rounded away with a grid probability, never with probability `\u03bd`.
    Choose the variant for the balance \u00a74.7.4 NOTE 2 describes, between accuracy and
    complexity, and choose `N` for how fine that grid must be.

!!! note "Motivation, not contract"
    Stochastic rounding is used in low-precision training because an update smaller than
    one unit in the last place is discarded by every deterministic mode but can accumulate
    under a random one. That is motivation from the wider literature, not a guarantee this
    package makes.

See also [`RSB`](@ref), [`RSC`](@ref).
"""
const RSA = ρRSA{DEFAULT_RBITS}()

"""
    RSB

StochasticB — a `StochasticRoundingMode`. Rounds away with probability

    P = \u230a\u03bd\u00b72^N + \u00bd\u230b / 2^N

that is, `\u03bd` rounded to the **nearest** grid point, ties resolved upward. Centring the
quantization this way halves the worst-case bias against [`RSA`](@ref)'s truncation, to
`2^-(N+1)`, and costs no extra random bits.

The report's predicate (\u00a74.7.4) is
`RoundAway(StochasticB_{N,R}) = \u230a\u03bd\u00b72^(N+1)\u230b + (2R + 1) \u2265 2^(N+1)`. Evaluating at doubled
resolution with the `+1` is what supplies the half-step offset: the same `N` random bits
buy nearest-rounding rather than truncation.

Differs from [`RSC`](@ref) only where `\u03bd\u00b72^N` lands exactly halfway — `RSB` goes up there,
`RSC` goes to even. Default budget `N = 8`; see [`RSA`](@ref) for the budget mechanics and
the caveats that apply to all three.
"""
const RSB = ρRSB{DEFAULT_RBITS}()

"""
    RSC

StochasticC — a `StochasticRoundingMode`. Rounds away with probability

    P = RNITE(\u03bd\u00b72^N) / 2^N

that is, `\u03bd` rounded to the **nearest** grid point with ties to even. Worst-case bias
matches [`RSB`](@ref)'s `2^-(N+1)`, and the even tie-break lets tie bias cancel across many
roundings instead of always pushing up. It is the most expensive of the three: it needs an
actual round-to-nearest-even of the scaled fraction, not just a floor.

The report's predicate (\u00a74.7.4) is
`RoundAway(StochasticC_{N,R}) = RNITE(\u03bd\u00b72^N) + R \u2265 2^N`, with `RNITE` the
round-to-nearest-ties-even the report defines alongside it.

Differs from [`RSB`](@ref) only at an exact halfway `\u03bd\u00b72^N`. Default budget `N = 8`; see
[`RSA`](@ref) for the budget mechanics and the caveats that apply to all three.
"""
const RSC = ρRSC{DEFAULT_RBITS}()

Base.string(x::ρRTE) = "RTE"
Base.string(x::ρRTA) = "RTA"
Base.string(x::ρRTP) = "RTP"
Base.string(x::ρRTN) = "RTN"
Base.string(x::ρRTZ) = "RTZ"
Base.string(x::ρRTO) = "RTO"
Base.string(x::ρRSA) = "RSA"
Base.string(x::ρRSB) = "RSB"
Base.string(x::ρRSC) = "RSC"

Base.String(x::ρRTE) = "RoundToEven"
Base.String(x::ρRTA) = "RoundToAway"
Base.String(x::ρRTP) = "RoundTowardPositive"
Base.String(x::ρRTN) = "RoundTowardNegative"
Base.String(x::ρRTZ) = "RoundTowardZero"
Base.String(x::ρRTO) = "RoundToOdd"
Base.String(x::ρRSA) = "StochasticA"
Base.String(x::ρRSB) = "StochasticB"
Base.String(x::ρRSC) = "StochasticC"

"""
    isstochastic(x)

Whether a rounding mode (or the rounding half of a [`Projection`](@ref)) is stochastic.

A compile-time constant: stochastic projections are never tabulable and consume
random bits; pure ones never touch RNG state.

# Examples

```jldoctest
julia> isstochastic(RSA), isstochastic(RTE)
(true, false)

julia> isstochastic(RSB_SF), isstochastic(RTE_SF)
(true, false)
```
"""
isstochastic(::Type{<:RoundingMode}) = false
isstochastic(::Type{<:StochasticRoundingMode}) = true
isstochastic(x::RoundingMode) = isstochastic(typeof(x))

"""
    nrandbits(x)

The random-bit budget `N` of a stochastic rounding mode (or of the rounding half
of a [`Projection`](@ref)); `0` for a deterministic mode.

# Examples

```jldoctest
julia> nrandbits(RSA), nrandbits(RTE)
(8, 0)

julia> nrandbits(AIFloats.ρRSA(12))
12
```
"""
nrandbits(::Type{<:RoundingMode}) = 0
nrandbits(::Type{ρRSA{N}}) where {N} = N
nrandbits(::Type{ρRSB{N}}) where {N} = N
nrandbits(::Type{ρRSC{N}}) where {N} = N
nrandbits(x::RoundingMode) = nrandbits(typeof(x))

# saturation modes
struct ρSF <: SaturatingSaturationMode end
struct ρSP <: SaturatingSaturationMode end
struct ρSN <: NonsaturatingSaturationMode end

"""
    SF

SatFinite — a saturating `AIFloats.SaturationMode`.

A `SaturatingSaturationMode`: [`project`](@ref) clamps everything past the largest finite
value — a genuine infinity too — to that value. See `AIFloats.saturate`.
"""
const SF = ρSF()

"""
    SP

SatPropagate — a saturating `AIFloats.SaturationMode`.

A `SaturatingSaturationMode`: [`project`](@ref) keeps a representable infinity and clamps
the rest to the largest finite value. See `AIFloats.saturate`.
"""
const SP = ρSP()

"""
    SN

SatNone — the non-saturating `AIFloats.SaturationMode`.

The one `NonsaturatingSaturationMode`: past the largest finite value, [`project`](@ref)
follows the draft's direction/signedness/domain rows — a directed rounding pointing back
into range gives the extremal finite, an extended domain spends its infinity, otherwise NaN.
See `AIFloats.saturate`.
"""
const SN = ρSN()

Base.string(x::ρSF) = "SF"
Base.string(x::ρSP) = "SP"
Base.string(x::ρSN) = "SN"

Base.String(x::ρSF) = "SatFinite"
Base.String(x::ρSP) = "SatPropagate"
Base.String(x::ρSN) = "SatNone"

# show projection components

Base.show(io::IO, ::MIME"text/plain", r::RoundingMode) = print(io, string(r))
Base.show(io::IO, r::RoundingMode) = print(io, string(r))

Base.show(io::IO, ::MIME"text/plain", s::SaturationMode) = print(io, string(s))
Base.show(io::IO, s::SaturationMode) = print(io, string(s))

# projections
"""
    Projection{R,S}

A rounding mode paired with a saturation mode — together, how a real number is mapped onto a
format's representable values.

Rounding settles what happens between neighbouring values; saturation settles what happens
past the largest. Build one with [`Projection(r, s)`](@ref), or use one of the 27 preset
constants named `<rounding>_<saturation>`, such as [`RTE_SF`](@ref). Read the halves back with
[`RoundOf`](@ref) and [`SatOf`](@ref).

A projection is applied to a number by [`project`](@ref).

# Examples

```jldoctest
julia> p = Projection(RTE, SF)
ρ(RTE, SF)

julia> p === RTE_SF
true

julia> RoundOf(p), SatOf(p)
(RTE, SF)
```
"""
struct Projection{R<:RoundingMode, S<:SaturationMode}
    rho::Tuple{R, S}
end

"""
    Projection(r, s)

Pair rounding mode `r` with saturation mode `s`.

All 27 combinations already exist as constants (`RTE_SF` through `RSC_SN`), and building one
returns a value identical to its constant.
"""
Projection(r::R, s::S) where {R<:RoundingMode, S<:SaturationMode} =
    Projection{R,S}((r,s))

"""
    RTE_SF

The [`Projection`](@ref) pairing [`RTE`](@ref) with [`SF`](@ref).

One of the 27 presets, named `<rounding>_<saturation>` over the 9 rounding modes
([`RTE`](@ref), [`RTA`](@ref), [`RTP`](@ref), [`RTN`](@ref), [`RTZ`](@ref), [`RTO`](@ref),
[`RSA`](@ref), [`RSB`](@ref), [`RSC`](@ref)) and the 3 saturation modes ([`SF`](@ref),
[`SP`](@ref), [`SN`](@ref)): `RTE_SF`, `RTE_SP`, `RTE_SN`, `RTA_SF`, … , `RSC_SN`.

`RTE_SF` rounds to nearest with ties to even and clamps everything, infinities included,
to the finite range. It is **not** the package default: [`DefaultProjection`](@ref) is
initially [`RTE_SN`](@ref), and `randn` — not ordinary construction — is what defaults to
`RTE_SF`.
"""
const RTE_SF = Projection(RTE, SF)
const RTE_SP = Projection(RTE, SP)
const RTE_SN = Projection(RTE, SN)

const RTA_SF = Projection(RTA, SF)
const RTA_SP = Projection(RTA, SP)
const RTA_SN = Projection(RTA, SN)

const RTP_SF = Projection(RTP, SF)
const RTP_SP = Projection(RTP, SP)
const RTP_SN = Projection(RTP, SN)

const RTN_SF = Projection(RTN, SF)
const RTN_SP = Projection(RTN, SP)
const RTN_SN = Projection(RTN, SN)

const RTZ_SF = Projection(RTZ, SF)
const RTZ_SP = Projection(RTZ, SP)
const RTZ_SN = Projection(RTZ, SN)

const RTO_SF = Projection(RTO, SF)
const RTO_SP = Projection(RTO, SP)
const RTO_SN = Projection(RTO, SN)

const RSA_SF = Projection(RSA, SF)
const RSA_SP = Projection(RSA, SP)
const RSA_SN = Projection(RSA, SN)

const RSB_SF = Projection(RSB, SF)
const RSB_SP = Projection(RSB, SP)
const RSB_SN = Projection(RSB, SN)

const RSC_SF = Projection(RSC, SF)
const RSC_SP = Projection(RSC, SP)
const RSC_SN = Projection(RSC, SN)

# RTE_SF carries the full explanation; its 26 siblings differ only in which modes they pair,
# so their docstrings are generated rather than spelled out one at a time.
for r in (RTE, RTA, RTP, RTN, RTZ, RTO, RSA, RSB, RSC), s in (SF, SP, SN)
    name = Symbol(string(r), "_", string(s))
    name === :RTE_SF && continue
    @eval @doc $("""
             $name

         The [`Projection`](@ref) pairing [`$(string(r))`](@ref) (`$(String(r))`) with
         [`$(string(s))`](@ref) (`$(String(s))`).

         One of the 27 presets; see [`RTE_SF`](@ref) for the naming scheme.
         """) $name
end

"""
    RoundOf(p)

The `AIFloats.RoundingMode` half of a [`Projection`](@ref).

# Examples

```jldoctest
julia> RoundOf(RTA_SN)
RTA
```
"""
RoundOf(p::Projection{R,S}) where {R<:RoundingMode, S<:SaturationMode} = p.rho[1]

"""
    SatOf(p)

The `AIFloats.SaturationMode` half of a [`Projection`](@ref).

# Examples

```jldoctest
julia> SatOf(RTA_SN)
SN
```
"""
SatOf(p::Projection{R,S}) where {R<:RoundingMode, S<:SaturationMode} = p.rho[2]

isstochastic(::Type{Projection{R,S}}) where {R<:RoundingMode, S<:SaturationMode} = isstochastic(R)
isstochastic(p::Projection) = isstochastic(typeof(p))
nrandbits(::Type{Projection{R,S}}) where {R<:RoundingMode, S<:SaturationMode} = nrandbits(R)
nrandbits(p::Projection) = nrandbits(typeof(p))

Base.show(io::IO, ::MIME"text/plain", p::Projection{R,S}) where {R<:RoundingMode, S<:SaturationMode} =
    print(io, "ρ(", string(RoundOf(p)), ", ", string(SatOf(p)), ")"    )

Base.show(io::IO, p::Projection{R,S}) where {R<:RoundingMode, S<:SaturationMode} =
    print(io, "ρ(", String(RoundOf(p)), ", ", String(SatOf(p)), ")")
