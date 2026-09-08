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

## Parameters and operands

§4.3.1 gives every operation the same signature schema:

```
Operation_{p1,...}(x1, ...) → r
```

The **parameters** are subscripts and the **operands** are the parenthesized list. For a
binary arithmetic operation the subscripts are `{fx, fy, fr, ρ}` — the two operand
formats, the result format, and the projection — so §4.10 writes multiplication as

```
Multiply_{fx,fy,fr,ρ}(x, y) → r
```

Julia gets `fx` and `fy` for free: a datum carries its format in its type, and dispatch
reads it. That leaves `fr` and `ρ` as the only subscripts without a carrier, and they keep
the report's position — ahead of the operands:

```julia
Multiply(fr, ρ, x, y)
```

Everything else on this page is that call with parameters supplied some other way. There
is exactly one implementation.

## The signatures

Take any register name — `Add`, `Exp`, `FMA`, `MinimumMagnitude`, … — and it has these
shapes:

```jldoctest operations
julia> F = Binary8p4se; G = Binary8p3se; x = F(1.5); y = F(0.25);

julia> Add(F, RTE_SN, x, y)          # 1. the draft form: result format, ρ, operands
1.75

julia> Add(x, y, F, RTE_SN)          # 2. the same call, operands first
1.75

julia> Add(x, y, RTZ_SF)             # 3. projection only; format from the operands
1.75

julia> Add(x, y)                     # 4. same-format convenience, task default ρ
1.75

julia> Exp(RTZ_SF, x)                # 5. projection-first (unary only)
4.0

julia> Add(F, RTE_SN)(x, y)          # 6. parameters bound, operands applied later
1.75

julia> vmap(:Add, F, RTE_SN, [x, y], [y, x])   # 7. elementwise over arrays
2-element Vector{BinaryValue(Binary8p4se)}:
 1.75
 1.75
```

| Form | Result format | Projection | Notes |
|:--|:--|:--|:--|
| `Op(fr, ρ, xs...)` | `fr`, explicit | `ρ`, explicit | the draft's shape; operands may be of **different** formats |
| `Op(xs..., fr, ρ)` | `fr`, explicit | `ρ`, explicit | the same call read from the other end; operands may differ |
| `Op(xs..., ρ)` | the shared operand format | `ρ`, explicit | every arity; operands must share a format |
| `Op(xs...)` | the shared operand format | [`DefaultProjection`](@ref) (task) resolves once | operands must share a format |
| `Op(ρ, x)` | the operand's format | `ρ`, explicit | unary operations only |
| `Op(fr, ρ)` | `fr`, explicit | `ρ`, explicit | no operands: an [`AIFloats.OpSpecialization`](@ref), applied later |
| `vmap(:Op, fr, ρ, As...)` | `fr`, explicit | `ρ`, resolved once per call | see [`vmap!`](@ref) to write into an existing array, which takes the result format from `dest` instead |

Every one of them accepts arrays of datums wherever it accepts datums, and the array call
is the [`vmap`](@ref) kernel — see [Arrays take the kernel](@ref ops-arrays) below.

`fr` accepts a [`Binary`](@ref) format type, a datum type, or an alias — all three name the
same format:

```jldoctest operations
julia> Add(Binary8p4se, RTE_SN, x, y) === Add(BinaryValue(Binary8p4se), RTE_SN, x, y)
true
```

## Binding the parameters

`Op(fr, ρ)` supplies the subscripts and nothing else. It returns an
[`AIFloats.OpSpecialization`](@ref) — the draft's *operation specialization* (§4.3.2.4) as
a value you can name, pass, and store:

```jldoctest operations
julia> mul = Multiply(F, RTE_SN)
Multiply(Binary8p4se, ρ(RoundToEven, SatNone))

julia> mul(x, y) === Multiply(F, RTE_SN, x, y)
true

julia> nameof(mul), formatof(mul) === F, Projection(mul) === RTE_SN
(:Multiply, true, true)
```

Nothing is projected when the parameters are bound; the call forwards to the method the
draft form would have run. A specialization over a constant projection is a zero-size
`isbits` value, so the forwarded call is the same static call, at the same cost.

### [Arrays take the kernel](@id ops-arrays)

A specialization applied to arrays is the *array* operation, not a `map` of the scalar
one. That matters more than it sounds:

```jldoctest operations
julia> A = [x, y]; B = [y, x];

julia> mul(A, B) == Multiply(F, RTE_SN, A, B) == map(mul, A, B)
true
```

All three agree, and two of them are fast. `mul(A, B)` runs [`vmap`](@ref) — the memoized
Shape-A gather when [`table_policy`](@ref) grants a table, the threaded compute loop past
`AIFloats.THREAD_MIN_ELEMS` otherwise. `map(mul, A, B)` runs the scalar path per element
and gathers from nothing. From `benchmark/arrays.jl`, `Add` over 4096 `Binary8p4se`
datums under `RTE_SN`:

| Spelling | ns/element |
|:--|--:|
| `Add(F, ρ, A, B)` | 0.26 |
| `Add(A, B, F, ρ)` | 0.26 |
| `Add(A, B, ρ)` | 0.26 |
| `Add(F, ρ)(A, B)` | 0.26 |
| `map(Add(F, ρ), A, B)` | 9.6 |

Prefer the operation over `map` for the same reason you prefer `vmap` over a hand-written
loop — it is the same answer through a kernel that was built for it. The scalar spellings
are on the same footing: `benchmark/scalar.jl` reads 8.7, 8.7, 8.6, and 8.6 ns for the
four forms of `Add` at `K = 8`.

## Mixed operand formats

The explicit form accepts operands of any formats. Each is decoded onto a carrier wide
enough for the exact result, and the single result is projected once into `fr`:

```jldoctest operations
julia> Add(F, RTE_SN, F(1.5), G(0.25))
1.75
```

There is no automatic promotion of different formats: `Binary8p4se(1) + Binary8p3se(1)`
raises a `MethodError`. Working with mixed formats requires an explicit
[`Convert`](@ref) or an explicit `Op(fr, ρ, …)` call. The computational system does not
presume to know how you want to resolve operations with values of mixed formats.

## How the result is computed

The registry records which route each operation takes to a correctly rounded answer. Every
route projects exactly once, and each is pinned equal to a rigorous reference by the test
suite — the group affects speed, never the result.

| Kind | Operations | Route |
|:--|:--|:--|
| **Sign manipulation** | `Abs`, `CopySign` | low-level bit operations and comparison |
| **Ring arithmetic** | `Negate`, `Add`, `Subtract`, `Multiply`, `FAA`, `FMA` | error-free computation |
| **Selection based** | `{Minimum, Maximum}[Magnitude]{Number, Finite}`, `Clamp` | exact order-based selection from a constrained set |
| **Enclosure** | `Sqrt`, `Divide`, `Exp`, `Log`, the trigonometric and hyperbolic families, and their π-scaled and inverse forms, … | the correctly rounded [interval-enclosure ladder](@ref alg-enclosure) |
| **Projection** | [`Convert`](@ref) | a projection with no arithmetic of its own |

The first three kinds are all exact, and differ in what they do with the operands: sign
manipulation **rewrites** one bit, ring arithmetic **computes** a result the operands do
not contain, and a selection **chooses** one that they do. (`Negate` is a sign-bit flip
too, and is listed with ring arithmetic because that is the role it plays there — the
additive inverse.)

The selection row is a schema — `[…]` optional, `{…}` a choice — naming the shape of the
extremum family rather than enumerating it. Not every combination the pattern admits
exists (there is no `MinimumMagnitudeFinite`), and the family also holds the bare
`Minimum` and `Maximum`. `AIFloats.operations()` is the complete and authoritative list;
this table is a map of the routes, not a census.

!!! note "These kinds are finer than the registry's groups"
    `AIFloats.operationinfo` reports `:B` for Enclosure and `:conv` for Projection, but it
    does not draw the other lines above. The Sign manipulation row alone spans two groups:
    `Abs` is recorded `:A` and `CopySign` is `:C`. `Clamp` is `:A` beside the ring
    operations, while the extremum family is `:C`.

    That is not an inconsistency in either scheme. The registry groups by **evaluation
    route** — how an exact answer is reached — and `Abs` and `Clamp` reach one the same way
    the ring operations do. The Kind column groups by what the operation *does with its
    operands*, which is the more useful reading here and a finer cut than the registry
    needs to make.

[Algorithms](@ref alg-enclosure) explains how the enclosure route *proves* a result is
correctly rounded rather than merely computing it carefully, and why no fixed working
precision could do the same.

!!! warning "Float128 is a carrier, not an oracle"
    `Quadmath.Float128` is used as a *value carrier*. libquadmath's elementary functions
    are **not** assumed to be correctly rounded, and no Quadmath transcendental result is
    ever accepted on its own. A fast result is accepted only when a proof or a
    two-sided enclosure check confirms it; otherwise the operation escalates to the
    rigorous MPFR ladder. The pure-Julia `AIFloats.fma128` and `AIFloats.faa128` carry
    their own documented guarantees. `AIFloats.FAST_ARITH` and `AIFloats.FAST_ENCLOSURE`
    switch the fast stages off for differential testing.

## An operation does not decompose

Every route above projects **exactly once**, and that is a property of the whole
operation, not of its pieces. It is tempting to read `Multiply_{fx,fy,fr,ρ}(x, y)` as a
same-format multiply followed by a conversion:

```julia
Multiply(x, y, fr, ρ)  ==  Convert(fr, ρ, Multiply(x, y, ρ))   # WRONG
```

It is not. The behavior line in §4.10 is

```
Multiply(x, y) → ωProject_{fr,ρ}(ωMultiply(ωDecode_{fx}(x), ωDecode_{fy}(y)))
```

`ωMultiply` runs on the ω-domain — exact values, not datums. No datum exists between the
decode and the project, so there is nowhere for a `Convert` to stand. Writing one there
forces a projection to have happened already, and two projections of one exact value is
the definition of a double rounding. [`Convert`](@ref) is itself a register operation
(`Convert_{fx,fr,ρ}`), so composing the two composes their projections.

The damage runs in both directions. With operands in a `P = 4` format whose exact product
needs six significand bits:

```jldoctest operations
julia> W = AIFloats.Formats.Binary16p8se; N = Binary8p2se;

julia> u = F(1.5); v = F(1.75); decode(u) * decode(v)          # the exact product
2.625

julia> Multiply(u, v, W, RTE_SN), Convert(W, RTE_SN, Multiply(u, v))
(2.625, 2.5)

julia> Multiply(u, v, N, RTE_SN), Convert(N, RTE_SN, Multiply(u, v))
(3.0, 2.0)
```

Into a **wider** result format the decomposition has already thrown away the bits the
exact product needed; into a **narrower** one it rounds twice and lands a full ulp away.
It agrees only when `fr` is the operand format, where the `Convert` is the identity — which
is exactly the case a test suite is most likely to cover.

This is why an [`AIFloats.OpSpecialization`](@ref) binds parameters and never composes
operations, and why there is no `∘` for them. A third defect settles it: `Multiply(x, y)`
has no result format to name when `fx ≠ fy`, and the mixed-format case is the one the
`fx`, `fy` subscripts exist for.

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
