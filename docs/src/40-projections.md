# [Projections](@id projections)

```@meta
CurrentModule = AIFloats
DocTestSetup = :(using AIFloats)
```

A format holds finitely many values, so most reals are not among them. A **projection** is
the choice of how a real is mapped onto one that is: a [rounding mode](@ref rounding-modes)
for values that fall between neighbours, and a [saturation mode](@ref saturation-modes) for
values past the largest.

Use a projection with [`Convert`](@ref), a registered operation, or
[`project`](@ref). Projection is the package's single code-point write path, so
the selected rounding and saturation behavior is applied exactly once.

!!! note "Which names are the report's"
    AIFloats spells some modes differently from the Interim Report. The report says
    `NearestTiesToEven`, `NearestTiesToAway`, and `ToOdd`; AIFloats displays
    `RoundToEven`, `RoundToAway`, and `RoundToOdd`. Those are **package long names**,
    not report terminology. The mapping is in [Report names and package names](@ref
    report-names) below, and every semantic claim on this page is checked against
    Interim Report §4.2, §4.7.4, and §4.7.5.

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

### What each mode actually decides

Interim Report §4.7.4 defines every mode by one predicate, `RoundAway(µ)`, on the fraction
`ν` left over after truncating the exact significand. AIFloats implements exactly these:

| Mode | `RoundAway` is true when |
|:--|:--|
| [`RTZ`](@ref) | never |
| [`RTP`](@ref) | `ν > 0` and the value is positive |
| [`RTN`](@ref) | `ν > 0` and the value is negative |
| [`RTA`](@ref) | `ν ≥ 0.5` |
| [`RTE`](@ref) | `ν > 0.5`, or `ν = 0.5` and the truncated code is odd |
| [`RTO`](@ref) | `ν > 0` and the truncated code is even |
| [`RSA`](@ref)`{N}` | `⌊ν·2^N⌋ + R ≥ 2^N` |
| [`RSB`](@ref)`{N}` | `⌊ν·2^(N+1)⌋ + (2R + 1) ≥ 2^(N+1)` |
| [`RSC`](@ref)`{N}` | `RNITE(ν·2^N) + R ≥ 2^N` |

"Even" here is the report's `CodeIsEven`, which for `P = 1` formats — where there is no
significand bit to be even — falls back to the parity of the biased exponent.

### How the three stochastic variants differ

All three consume exactly `N` random bits and differ only in **how the rounding
probability is quantized** onto the grid of `2^N` steps:

| Mode | `P(round away)` | Quantization of `ν` | Bias |
|:--|:--|:--|:--|
| [`RSA`](@ref)`{N}` | `⌊ν·2^N⌋ / 2^N` | truncated | one-signed, up to `2^-N` |
| [`RSB`](@ref)`{N}` | `⌊ν·2^N + ½⌋ / 2^N` | nearest, ties up | centred, `2^-(N+1)` |
| [`RSC`](@ref)`{N}` | `RNITE(ν·2^N) / 2^N` | nearest, ties to even | centred, `2^-(N+1)` |

`RSB` and `RSC` can disagree only where `ν·2^N` lands exactly halfway. Cost runs opposite
to accuracy — that is the "balance between accuracy and complexity" of §4.7.4 NOTE 2.

!!! warning "None is exactly unbiased at finite `N`"
    Stochastic rounding is unbiased when `P(away) = ν`, which at a finite budget holds
    only for the `ν` that land on the grid. `ν = 0.8` at `N = 3` is rounded away with
    probability `¾` by all three. AIFloats claims no bias figure beyond the bounds above.

[Algorithms](@ref alg-stochastic) derives these probabilities from the §4.7.4 predicates,
works through where the variants diverge, and gives guidance on choosing between them and
on choosing `N`.

!!! note "Motivation, not contract"
    Round-to-odd's practical use is avoiding double rounding: round a wide intermediate to
    odd, narrow it, and the second rounding lands where a single direct rounding would
    have — a property of the composition, not of the mode alone. Stochastic rounding is
    used in low-precision training because a weight update smaller than one unit in the
    last place is discarded by every deterministic mode but can accumulate under a random
    one. Both statements are *motivation* from the wider literature, not guarantees this
    package makes, and neither is a claim about hardware cost or error magnitude on any
    particular device.

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

### What they do, exactly

Interim Report §4.7.5. The three modes agree on everything inside the finite range and
differ outside it — and they differ from *each other* only on a genuine infinity:

| | out-of-range finite | `±Inf` reaching saturation |
|:--|:--|:--|
| [`SF`](@ref) | clamps to the extremal finite | clamps to the extremal finite |
| [`SP`](@ref) | clamps to the extremal finite | kept when the format can represent it, else clamped |
| [`SN`](@ref) | the extremal finite when the rounding direction points back into range; otherwise the infinity if the format is `EXTENDED`, else NaN | the infinity if the format is `EXTENDED` and signed as needed, else NaN |

Two consequences worth stating outright, because they are easy to get wrong:

- Under `SN`, an **unsigned** `EXTENDED` format has no `-Inf`, so a negative overflow is
  NaN, not `-Inf`.
- Under `SN`, a `FINITE` format has no infinity at all, so every remaining out-of-range
  result is NaN.

`SF` and `SP` are indistinguishable on a finite input, however large. To see the
difference, project an actual infinity:

```jldoctest projections
julia> F = Binary(8, 3, SIGNED, EXTENDED);

julia> decode(Convert(F, RTE_SF, Inf)), decode(Convert(F, RTE_SP, Inf))
(49152.0, Inf)

julia> decode(Convert(F, RTE_SF, 1.0e100)), decode(Convert(F, RTE_SP, 1.0e100))
(49152.0, 49152.0)
```

Saturation never rounds. It receives the rounding mode only because §4.7.5's `SatNone`
rows need it to decide whether a directed rounding should deliver a finite.

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

The full set runs `RTE_SF`, `RTE_SP`, `RTE_SN`, `RTA_SF`, … , `RSC_SN`.

## Defaults, and how far each one reaches

The Interim Report defines **no** default projection. §4.5 requires the listed operation
specializations at `(NearestTiesToEven, SatNone)`; that is a conformance requirement, not a
package-wide default. AIFloats' default happens to be the same pair, as a package choice:

```jldoctest projections
julia> DefaultProjection()
ρ(RTE, SN)
```

| What | Default | Scope |
|:--|:--|:--|
| construction, convenience arithmetic, Base operators | [`RTE_SN`](@ref) | **task-local** — [`DefaultProjection`](@ref), bound by [`with_projection`](@ref) |
| `rand` | `RTZ_SN` | per call; keeps draws provably `< 1` |
| `randn` | `RTE_SF` | per call; clamps the tails, signed formats only |
| `Op(F, ρ, …)`, `Convert(F, ρ, x)`, [`project`](@ref) | none — `ρ` is explicit | per call |

The task-local default is bound for a dynamic extent and restored on return and on
exception; it nests, and a task started inside inherits it. There is deliberately no
setter: a process-wide one would let two concurrent tasks fight over what arithmetic
means.

```jldoctest projections
julia> with_projection(RTZ_SF) do
           DefaultProjection()
       end
ρ(RTZ, SF)

julia> DefaultProjection()          # restored on exit
ρ(RTE, SN)
```

Library code should still prefer an explicit projection. `Add(F, ρ, x, y)` never reads the
default at all.

## [Report names and package names](@id report-names)

| Interim Report §4.2 | AIFloats short | AIFloats long |
|:--|:--|:--|
| `NearestTiesToEven` | [`RTE`](@ref) | `RoundToEven` |
| `NearestTiesToAway` | [`RTA`](@ref) | `RoundToAway` |
| `TowardPositive` | [`RTP`](@ref) | `RoundTowardPositive` |
| `TowardNegative` | [`RTN`](@ref) | `RoundTowardNegative` |
| `TowardZero` | [`RTZ`](@ref) | `RoundTowardZero` |
| `ToOdd` | [`RTO`](@ref) | `RoundToOdd` |
| `Stochastic[A, B, C]` | [`RSA`](@ref), [`RSB`](@ref), [`RSC`](@ref) | `StochasticA/B/C` |
| `SatFinite` | [`SF`](@ref) | `SatFinite` |
| `SatPropagate` | [`SP`](@ref) | `SatPropagate` |
| `SatNone` | [`SN`](@ref) | `SatNone` |

The first, second, and sixth rows are the ones where AIFloats' long name is **not** the
report's word. Everything else matches.

## Stochastic projections and randomness

A stochastic projection needs `N` random bits per rounding decision, where `N` is carried
in the mode's type:

```jldoctest projections
julia> isstochastic(RSA_SN), nrandbits(RSA_SN)
(true, 8)

julia> isstochastic(RTE_SN)
false
```

The contract:

- `N` is in `1:60`. The report bounds the random bits `R` by `0 ≤ R < 2^N` (§4.7.4
  Details) and does not bound `N`; the ceiling of 60 is this package's limit.
- An explicit `R` must be in `0:(2^N - 1)`. Out of range is an `ArgumentError`.
- When both `R` and `rng` are supplied, **`R` wins** — it names the draw outright.
- With neither, a stochastic projection resolves `Random.default_rng()`.
- A **pure** projection touches no RNG state at all, whatever `rng` or `R` you pass.
- Array calls take an `rng` and consume one sequential stream in `eachindex` order, so a
  seeded call is reproducible and never depends on the scheduler. There is no per-element
  `R`.

```jldoctest projections
julia> F = Binary(8, 3, SIGNED, EXTENDED); T = BinaryValue(F);

julia> x, y = T(1.0), T(0.125);

julia> Add(F, RSA_SN, x, y; R = 3) === Add(F, RSA_SN, x, y; R = 3)
true

julia> Add(F, RSA_SN, x, y; R = 1 << 60)
ERROR: ArgumentError: explicit R=1152921504606846976 outside 0:255 for N=8 random bits
[...]
```

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
