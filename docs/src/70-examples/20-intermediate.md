# [Intermediate examples](@id examples-intermediate)

```@meta
CurrentModule = AIFloats
DocTestSetup = :(using AIFloats)
```

## Define a custom format

`Binary(K, P, signedness, domain)` returns a format type. Wrap it in
[`BinaryValue`](@ref) to obtain its concrete datum type.

```@example intermediate_format
using AIFloats

F = Binary(8, 3, SIGNED, EXTENDED)
T = BinaryValue(F)
(T, BitwidthOf(T), PrecisionOf(T), ExponentBiasOf(T))
```

## Compare projection choices

```@example intermediate_projections
using AIFloats

F = Binary(8, 3, SIGNED, EXTENDED)
value = 1.2
projections = (
    RTE = RTE_SN,
    RTP = RTP_SN,
    RTN = RTN_SN,
    RTZ = RTZ_SN,
    RTO = RTO_SN,
)
results = map(p -> Convert(F, p, value), projections)
(
    input = value,
    decoded = map(decode, results),
    codes = map(codepoint, results),
)
```

Several modes may select the same neighbor: one inexact input lies between only
two adjacent datums. Here upward, nearest-even, and round-to-odd select `1.25`,
while downward and toward-zero select `1.0`.

## Tell the saturation modes apart

Saturation matters outside the format's finite range — but a large *finite*
input does not separate the modes. `SF` and `SP` both clamp it, so the answers
are identical:

```@example intermediate_saturation_finite
using AIFloats

F = Binary(8, 3, SIGNED, EXTENDED)
finite = (SF = Convert(F, RTE_SF, 1.0e100), SP = Convert(F, RTE_SP, 1.0e100))
@assert finite.SF === finite.SP
finite
```

The defining difference is what happens to a genuine **infinity**. `SF` clamps
it; `SP` keeps it when the format can represent it:

```@example intermediate_saturation_inf
using AIFloats

F = Binary(8, 3, SIGNED, EXTENDED)
infinite = (SF = Convert(F, RTE_SF, Inf), SP = Convert(F, RTE_SP, Inf))
@assert infinite.SF !== infinite.SP
@assert isinf(infinite.SP) && isfinite(infinite.SF)
infinite
```

`SN` is governed by rounding direction, signedness, and domain, so it can yield
an extremal finite, an infinity, or NaN from the same input:

```@example intermediate_saturation_none
using AIFloats

E = Binary(8, 3, SIGNED, EXTENDED)     # signed, has infinities
U = Binary(8, 3, UNSIGNED, EXTENDED)   # no −Inf to reach
V = Binary(8, 3, SIGNED, FINITE)       # no infinities at all
(
    directed_back_into_range = Convert(E, RTZ_SN, 1.0e100),   # extremal finite
    extended_signed          = Convert(E, RTE_SN, -1.0e100),  # −Inf
    extended_unsigned        = Convert(U, RTE_SN, -1.0e100),  # NaN: no −Inf
    finite_domain            = Convert(V, RTE_SN, 1.0e100),   # NaN: no infinities
)
```

| Mode | out-of-range finite | `±Inf` |
|:--|:--|:--|
| `SF` | clamps to the extremal finite | clamps to the extremal finite |
| `SP` | clamps to the extremal finite | kept when representable, else clamped |
| `SN` | extremal finite if the rounding direction points back into range; else the infinity if `EXTENDED`; else NaN | the infinity if `EXTENDED` and signed as needed, else NaN |

## Change the projection for a block

Convenience operations and constructors read the *task's* default projection.
Bind it for a dynamic extent with `with_projection`; it is restored on return
and on exception, it nests, and a task started inside inherits it:

```@example intermediate_default
using AIFloats

F = Binary(8, 3, SIGNED, EXTENDED)
T = BinaryValue(F)
with_projection(RTZ_SF) do
    (DefaultProjection(), T(1.3))
end
```

There is no setter. A process-wide one would make two concurrently running
tasks silently fight over what arithmetic means, which is exactly what a
projection must never be.

Library code should still generally prefer explicit projections: `Add(F, ρ, x, y)`
never reads the default at all, and it is the fastest path by a wide margin.

## Reproduce stochastic rounding

An explicit `R` fixes the random draw used by a stochastic projection. This is
especially useful in tests:

```@example intermediate_explicit_r
using AIFloats

F = Binary(8, 3, SIGNED, EXTENDED)
T = BinaryValue(F)
x, y = T(1.0), T(0.125)
# With neither `R` nor `rng`, AIFloats draws from Random.default_rng()
# (the current task's TaskLocalRNG on Julia 1.12).
# Here the explicit `R` supplies the draw instead, making the call repeatable.
a = Add(F, RSA_SN, x, y; R=3)
b = Add(F, RSA_SN, x, y; R=3)
(a, b, a === b)
```

If neither `R` nor `rng` is supplied, AIFloats draws from
`Random.default_rng()`, just as `rand()` does. On Julia 1.12 this is the current
task's `TaskLocalRNG`, backed by Xoshiro256++; a fresh Julia session is seeded
from system randomness, so calls are not reproducible across sessions by
default. The concrete default-RNG type and its exact stream are Julia
implementation details and may change between Julia versions.

For a reproducible sequence, pass an explicitly seeded RNG and retain it across
calls:

```@example intermediate_seeded_rng
using AIFloats, Random

F = Binary(8, 3, SIGNED, EXTENDED)
T = BinaryValue(F)
x, y = T(1.0), T(0.125)
rng1 = Xoshiro(2026)
rng2 = Xoshiro(2026)
seq1 = [Add(F, RSA_SN, x, y; rng=rng1) for _ in 1:8]
seq2 = [Add(F, RSA_SN, x, y; rng=rng2) for _ in 1:8]
(seq1, seq1 == seq2)
```

Omitting `rng` is appropriate when nondeterministic session-to-session behavior
is wanted. Pass an RNG when reproducibility, stream ownership, or isolation
from unrelated random draws matters.

### The whole contract, in one place

```@example intermediate_stochastic_contract
using AIFloats, Random

F = Binary(8, 3, SIGNED, EXTENDED)
T = BinaryValue(F)
x, y = T(1.0), T(0.125)

# N — the random-bit budget — is carried in the mode's type, and is in 1:60.
budget = (nrandbits(RSA_SN), isstochastic(RSA_SN), isstochastic(RTE_SN))

# R takes precedence when both R and rng are supplied: the draw is named
# outright, so the rng is not consulted and its stream does not advance.
rng = Xoshiro(2026)
before = copy(rng)
withR = Add(F, RSA_SN, x, y; R = 3, rng = rng)
rng_untouched = (rng == before)

# A pure projection touches no RNG state at all, whatever you pass.
rng2 = Xoshiro(2026)
before2 = copy(rng2)
pure = Add(F, RTE_SN, x, y; rng = rng2)
pure_untouched = (rng2 == before2)

(budget = budget, withR = withR, rng_untouched = rng_untouched,
 pure = pure, pure_untouched = pure_untouched)
```

An out-of-range `R` is refused rather than wrapped:

```@example intermediate_stochastic_refuse
using AIFloats

F = Binary(8, 3, SIGNED, EXTENDED)
T = BinaryValue(F)
try
    Add(F, RSA_SN, T(1.0), T(0.125); R = 1 << 60)   # RSA_SN has N = 8, so R < 256
catch err
    err
end
```

Arrays take an `rng` and consume **one sequential stream in `eachindex` order**.
There is no per-element `R`, and the result never depends on the scheduler:

```@example intermediate_stochastic_arrays
using AIFloats, Random

F = Binary(8, 3, SIGNED, EXTENDED)
T = BinaryValue(F)
A = T[1.0, 1.0, 1.0, 1.0]
B = T[0.125, 0.125, 0.125, 0.125]

first_run  = vmap(:Add, F, RSA_SN, A, B; rng = Xoshiro(7))
second_run = vmap(:Add, F, RSA_SN, A, B; rng = Xoshiro(7))
@assert first_run == second_run
(first_run, first_run == second_run)
```

## Apply operations to arrays

`vmap` allocates the destination; `vmap!` writes into an
existing array. The kernel chooses a table gather or scalar computation without
changing the result.

```@example intermediate_arrays
using AIFloats

F = Binary(8, 3, SIGNED, EXTENDED)
T = BinaryValue(F)
A = T[0.25, 0.5, 1.0, 2.0]
B = T[2.0, 1.0, 0.5, 0.25]

C = vmap(:Add, F, RTE_SN, A, B)
D = similar(A)
vmap!(D, :Multiply, RTE_SN, A, B)
(C, D)
```

Registered same-format broadcasts use the same array machinery:

```@example intermediate_broadcast
using AIFloats

T = BinaryValue(Binary(8, 3, SIGNED, EXTENDED))
A = T[0.25, 0.5, 1.0, 2.0]
B = T[2.0, 1.0, 0.5, 0.25]
(A .+ B, exp.(A))
```

## Convert a whole array

`Convert(F, A)` resolves the task default **once**, before the loop, and never
per element:

```@example intermediate_convert_array
using AIFloats

F = Binary(8, 3, SIGNED, EXTENDED)
A = [0.1, 1.2, 3.7, 100.0]
converted = Convert(F, A)
(converted, eltype(converted), axes(converted) == axes(A))
```

Mismatched axes are a `DimensionMismatch`, not a silently truncated result:

```@example intermediate_axes_refuse
using AIFloats

F = Binary(8, 3, SIGNED, EXTENDED)
T = BinaryValue(F)
try
    vmap(:Add, F, RTE_SN, T[1.0, 2.0], T[1.0])
catch err
    err
end
```

Continue with [Advanced examples](@ref examples-advanced) for packed and
shared-scale storage.

```@meta
DocTestSetup = nothing
```
