# [Basic examples](@id examples-basic)

```@meta
CurrentModule = AIFloats
DocTestSetup = :(using AIFloats)
```

These examples use the exported `binary8p4se` alias: an eight-bit, four-bit
precision, signed, extended format.

## Construct and inspect values

```@example basic_construct
using AIFloats

T = binary8p4se
x = T(1.5)
y = T(0.25)

(x, decode(x), codepoint(x), BinaryFormatOf(x))
```

A `BinaryValue` stores a code point. [`decode`](@ref) returns its exact numeric
value on the format's carrier; `codepoint` returns the stored encoding.

## Calculate with Julia syntax

Same-format values support Julia's ordinary numeric spelling. These methods use
the session's [`DefaultProjection`](@ref), initially `RTE_SN`.

```@example basic_arithmetic
using AIFloats

T = binary8p4se
x, y = T(1.5), T(0.25)
(x + y, x * y, x / y, sqrt(x), exp(y))
```

The named register operations are available when the result format and
projection should be visible at the call site:

```@example basic_register
using AIFloats

T = binary8p4se
x, y = T(1.5), T(0.25)
F = BinaryFormatOf(T)
(Add(F, RTE_SN, x, y), Multiply(F, RTZ_SF, x, y))
```

## Convert values explicitly

Construction uses the session default. [`Convert`](@ref) makes the format and
projection explicit:

```@example basic_convert
using AIFloats

F = BinaryFormatOf(binary8p4se)
value = 1.2
nearest = Convert(F, RTE_SN, value)
toward_zero = Convert(F, RTZ_SN, value)
(
    input = value,
    decoded = (decode(nearest), decode(toward_zero)),
    codes = (codepoint(nearest), codepoint(toward_zero)),
)
```

Convert between AIFloats formats explicitly as well:

```@example basic_cross_format
using AIFloats

x = binary8p4se(1.5)
Small = binary5p2se
s = Convert(Small, RTE_SN, x)
(s, decode(s), Float64(s))
```

## Classify and navigate

```@example basic_neighbors
using AIFloats

T = binary8p4se
x = T(1.5)
(Class(x), NextLessThan(x), NextGreaterThan(x), eps(x))
```

Special accessors make important endpoints easy to name:

```@example basic_endpoints
using AIFloats

T = binary8p4se
(MinPositiveOf(T), MinNormalOf(T), MaxFiniteOf(T))
```

Continue with [Intermediate examples](@ref examples-intermediate) for explicit
rounding control and array operations.

```@meta
DocTestSetup = nothing
```
