# [Operations](@id operations)

```@meta
CurrentModule = AIFloats
DocTestSetup = :(using AIFloats)
```

The Interim Report defines operations as *mappings from operand datums to result datums*,
parameterized by the operand formats, the result format, and a projection (§4.1). AIFloats
implements that register directly: one generated family, one shape, no hand-written
per-operation variants.

Every name on this page comes from the registry, so an operation cannot exist without a
documented signature and cannot be documented with the wrong arity.

```jldoctest operations
julia> length(AIFloats.operations())
52

julia> AIFloats.operationinfo(:Add)
(name = :Add, arity = 2, group = :A, factors = 1)
```

`factors` is the carrier-width driver: the largest number of datum factors in any monomial
of the exact result. It is not the arity — `FAA` has three operands and one factor.

## The four signatures

Take any register name — `Add`, `Exp`, `FMA`, `MinimumMagnitude`, … — and it has these
shapes:

```jldoctest operations
julia> F = Binary8p4se; G = Binary8p3se; x = F(1.5); y = F(0.25);

julia> Add(F, RTE_SN, x, y)          # 1. the draft form: result format, ρ, operands
1.75

julia> Add(x, y)                     # 2. same-format convenience, task default ρ
1.75

julia> Exp(RTZ_SF, x)                # 3. projection-first (unary only)
4.0

julia> vmap(:Add, F, RTE_SN, [x, y], [y, x])   # 4. elementwise over arrays
2-element Vector{BinaryValue(Binary8p4se)}:
 1.75
 1.75
```

| Form | Result format | Projection | Notes |
|:--|:--|:--|:--|
| `Op(fr, ρ, xs...)` | `fr`, explicit | `ρ`, explicit | the draft's shape; operands may be of **different** formats |
| `Op(xs...)` | the shared operand format | task-local [`DefaultProjection`](@ref), resolved once | operands must share a format |
| `Op(ρ, x)` | the operand's format | `ρ`, explicit | unary operations only |
| `vmap(:Op, fr, ρ, As...)` | `fr` | `ρ`, resolved once per call | see [`vmap!`](@ref) to write into an existing array |

`fr` accepts a [`Binary`](@ref) format type, a datum type, or an alias — all three name the
same format:

```jldoctest operations
julia> Add(Binary8p4se, RTE_SN, x, y) === Add(BinaryValue(Binary8p4se), RTE_SN, x, y)
true
```

## Mixed operand formats

The explicit form accepts operands of any formats. Each is decoded onto a carrier wide
enough for the exact result, and the single result is projected once into `fr`:

```jldoctest operations
julia> Add(F, RTE_SN, F(1.5), G(0.25))
1.75
```

There is no promotion. `Binary8p4se(1) + Binary8p3se(1)` is deliberately a `MethodError`:
mixing formats is an explicit [`Convert`](@ref) or an explicit `Op(fr, ρ, …)` call, so no
result format is ever chosen for you.

## How the result is computed

The registry records which route each operation takes to a correctly rounded answer. Both
routes project exactly once, and both are pinned equal to a rigorous reference by the test
suite — the group affects speed, never the result.

| Group | Operations | Route |
|:--|:--|:--|
| `:A` | `Add`, `Subtract`, `Multiply`, `FMA`, `FAA`, `Abs`, `Negate`, `Clamp` | exact evaluation — an error-free transform or an exact escalation |
| `:B` | `Exp`, `Log`, `Sqrt`, `Divide`, the trigonometric, hyperbolic, and π-scaled families, `Hypot`, `Softplus`, … | the correctly rounded interval-enclosure ladder |
| `:C` | the extremum family (`Minimum`, `MaximumMagnitudeNumber`, `MinimumFinite`, …) | an exact selection among the operands |
| `:conv` | [`Convert`](@ref) | a projection with no arithmetic of its own |

!!! warning "Float128 is a carrier, not an oracle"
    `Quadmath.Float128` is used as a *value carrier*. libquadmath's elementary functions
    are **not** assumed to be correctly rounded, and no Quadmath transcendental result is
    ever accepted on its own. A fast result is accepted only when a proof or a
    two-sided enclosure check confirms it; otherwise the operation escalates to the
    rigorous MPFR ladder. The pure-Julia `AIFloats.fma128` and `AIFloats.faa128` carry
    their own documented guarantees. `AIFloats.FAST_ARITH` and `AIFloats.FAST_ENCLOSURE`
    switch the fast stages off for differential testing.

## Randomness

`rng` and `R` are consulted **only** under a stochastic projection. A pure projection
touches no RNG state, whatever you pass. The full contract — the `1:60` bound on `N`, the
`0:(2^N - 1)` bound on `R`, `R` taking precedence over `rng`, and the sequential
`eachindex` stream for arrays — is on the [Projections](@ref projections) page.

## Julia's operators are veneers

Same-format datums support Julia's ordinary spelling. Each veneer is exactly one register
call under the task's default projection — not a second, looser semantics:

```jldoctest operations
julia> x + y === Add(x, y)
true

julia> exp(y) === Exp(y)
true
```

`abs`, `sqrt`, `exp`, `log`, the trigonometric and hyperbolic families, `hypot`,
`copysign`, `max`/`min`, `fma`/`muladd`, and `clamp` all map this way. Comparison,
`isless`/`sort` in the draft's NaN-first total order, and the `AbstractFloat` contract
(`zero`, `eps`, `floatmin`, `frexp`, `nextfloat`, …) are on the same footing.

## Refusals are explicit

Where the draft defines no answer, AIFloats throws an `ArgumentError` that says why —
never a bare `MethodError`, and never a silently plausible number:

```jldoctest operations
julia> rem(x, y)
ERROR: ArgumentError: rem is not defined for Binary8p4se: the draft defines no remainder; the exact result is generally not a datum, so any answer would round outside `project`. Compute on `decode(x)` and `Convert` back if that is what you want.
[...]

julia> F(1//3)
ERROR: ArgumentError: cannot exactly project a Rational into Binary8p4se; convert explicitly, e.g. Binary8p4se(Float64(x)), and own the double rounding
[...]
```

An out-of-domain *value* is different from a refused *operation*: it has a defined answer.
Under an unsigned format, a negative input is out of domain and the projection delivers
NaN rather than throwing.

```jldoctest operations
julia> Binary8p4uf(-1.0)
NaN
```

## Blocked and scaled forms

Every register operation also has a `Block*` form (lanewise over shared-scale
[`Block`](@ref)s, with an explicit result scale) and a `Scaled*` form (§5.8, over
scale/value pairs). Both are generated from the same registry rows, so their arities
follow the scalar operation's. See [Advanced examples](@ref examples-advanced).

## Discovering the register

```jldoctest operations
julia> [(o.name, o.arity, o.group) for o in first(AIFloats.operations(), 3)]
3-element Vector{Tuple{Symbol, Int64, Symbol}}:
 (:Abs, 1, :A)
 (:Add, 2, :A)
 (:ArcCos, 1, :B)

julia> AIFloats.operationinfo(:FMA).arity
3
```

`AIFloats.operations()` and `AIFloats.operationinfo` are the supported way to enumerate the
register; the underlying `OP_REGISTRY` is private and its shape is not part of the
interface.

```@meta
DocTestSetup = nothing
```
