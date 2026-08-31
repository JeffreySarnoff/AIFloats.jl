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

Saturation becomes observable outside the format's finite range:

```@example intermediate_saturation
using AIFloats

F = Binary(8, 3, SIGNED, EXTENDED)
(Convert(F, RTE_SF, 1.0e100), Convert(F, RTE_SP, 1.0e100))
```

## Change the session default safely

Convenience operations and constructors read a process-wide default. Restore
it in a `finally` block when changing it temporarily:

```@example intermediate_default
using AIFloats

F = Binary(8, 3, SIGNED, EXTENDED)
T = BinaryValue(F)
old = DefaultProjection()
try
    DefaultProjection!(RTZ_SF)
    (DefaultProjection(), T(1.3))
finally
    DefaultProjection!(old)
end
```

Library code should generally prefer explicit projections so it does not
depend on process-global state.

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

Continue with [Advanced examples](@ref examples-advanced) for packed and
shared-scale storage.

```@meta
DocTestSetup = nothing
```
