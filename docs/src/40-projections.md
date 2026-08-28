# [Projections](@id projections)

```@meta
CurrentModule = AIFloats
DocTestSetup = :(using AIFloats)
```

A format holds finitely many values, so most reals are not among them. A **projection** is
the choice of how a real is mapped onto one that is: a [rounding mode](@ref rounding-modes)
for values that fall between neighbours, and a [saturation mode](@ref saturation-modes) for
values past the largest.

!!! note "Names, not yet behavior"
    These constants currently *name* the modes and let you pass a choice around. Applying a
    projection to a number is not implemented — see [Implementation status](@ref status).

## [Rounding modes](@id rounding-modes)

Nine modes, each a singleton with a short name and a long one:

| Constant | Long name | Family | Behavior |
|:--|:--|:--|:--|
| [`RTE`](@ref) | `RoundToEven` | to nearest | nearest; ties to the even last bit |
| [`RTA`](@ref) | `RoundToAway` | to nearest | nearest; ties away from zero |
| [`RTP`](@ref) | `RoundTowardPositive` | unidirectional | toward +Inf |
| [`RTN`](@ref) | `RoundTowardNegative` | unidirectional | toward −Inf |
| [`RTZ`](@ref) | `RoundTowardZero` | unidirectional | truncate |
| [`RTO`](@ref) | `RoundToOdd` | parity | inexact results get a `1` last bit |
| [`RSA`](@ref) | `StochasticA` | stochastic | randomized |
| [`RSB`](@ref) | `StochasticB` | stochastic | randomized |
| [`RSC`](@ref) | `StochasticC` | stochastic | randomized |

The families are types, so a group can be dispatched on or tested as a group:

```jldoctest projections
julia> RTE isa AIFloats.ToNearestRoundingMode
true

julia> RTZ isa AIFloats.DeterministicRoundingMode
true

julia> RSA isa AIFloats.StochasticRoundingMode
true
```

`AIFloats.DeterministicRoundingMode` covers the to-nearest, unidirectional, and parity
families — everything except the stochastic three.

### Why three kinds matter at low precision

[`RTE`](@ref) is the familiar default and is unbiased, which is why IEEE 754 chose it.

[`RTO`](@ref) is also unbiased and much cheaper in hardware, at roughly twice the rounding
error. Its real use is avoiding double rounding: round a wide intermediate to odd, then
narrow it, and the second rounding lands where a single direct rounding would have.

Stochastic rounding rounds up or down at random, so it is unbiased *in expectation* rather
than per-operation. That matters when a weight update is smaller than one unit in the last
place: deterministic rounding discards every such update, while stochastic rounding lets them
accumulate. It is the reason very low-precision training works at all.

## [Saturation modes](@id saturation-modes)

Three modes, covering what happens to a value too large for the format:

| Constant | Long name | Family |
|:--|:--|:--|
| [`SF`](@ref) | `SatFinite` | saturating |
| [`SP`](@ref) | `SatPropagate` | saturating |
| [`SN`](@ref) | `SatNone` | non-saturating |

```jldoctest projections
julia> SF isa AIFloats.SaturatingSaturationMode
true

julia> SN isa AIFloats.NonsaturatingSaturationMode
true
```

## Short and long names

Every mode answers to both. Lowercase `string` gives the short name, capital `String` the
long one:

```jldoctest projections
julia> string(RTE), String(RTE)
("RTE", "RoundToEven")

julia> string(SF), String(SF)
("SF", "SatFinite")
```

Displaying a mode uses the short name:

```jldoctest projections
julia> RTE
RTE
```

## Pairing them

A [`Projection`](@ref) is one rounding mode and one saturation mode together:

```jldoctest projections
julia> p = Projection(RTA, SN)
ρ(RTA, SN)

julia> RoundOf(p), SatOf(p)
(RTA, SN)
```

All 27 pairings exist as constants named `<rounding>_<saturation>`, so building one is
usually unnecessary:

```jldoctest projections
julia> p === RTA_SN
true
```

The full set runs `RTE_SF`, `RTE_SP`, `RTE_SN`, `RTA_SF`, … , `RSC_SN`. [`RTE_SF`](@ref) —
round to nearest, ties to even, saturating — is the conventional default.

### How projections display

A `Projection` prints as `ρ(rounding, saturation)`, and like the modes it has a short form and
a long one. The short form is what the REPL shows:

```jldoctest projections
julia> RTE_SF
ρ(RTE, SF)

julia> repr(RTE_SF)
"ρ(RoundToEven, SatFinite)"
```

```@meta
DocTestSetup = nothing
```
