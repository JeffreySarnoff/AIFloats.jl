# [Basic examples](@id examples-basic)

```@meta
CurrentModule = AIFloats
DocTestSetup = :(using AIFloats)
```

These examples use the exported `Binary8p4se` alias: an eight-bit, four-bit
precision, signed, extended format. Throughout the documentation `F` is a
format, `T` a datum type, `x` a datum, `c` a code point, and `ρ` a projection.

## Construct and inspect values

```@example basic_construct
using AIFloats

F = Binary8p4se          # the format
T = BinaryValue(F)       # the datum type
x = F(1.5)
y = F(0.25)

(x, decode(x), codepoint(x), x isa T)
```

A datum stores a code point. [`decode`](@ref) returns its exact numeric value on
the format's carrier; `codepoint` returns the stored encoding. `formatof(x)`
recovers the format from a datum you were handed — there is no need for it when
you already hold `F`.

## Numbers and code points are distinct

Every constructor argument is a **number**, `Unsigned` included. To name a raw
code point, use [`fromcode`](@ref):

```@example basic_codes
using AIFloats

F = Binary8p4se
(fromcode(F, 0x45), F(0x45), F(69))
```

`fromcode(F, 0x45)` is the datum living at code point `0x45`. `F(0x45)` is the
number 69 projected into `F` — the same thing `F(69)` means. The two questions
never collide, so `F(codepoint(y))` can never silently reinterpret `y`.

An out-of-range code point is refused rather than truncated:

```@example basic_codes_refuse
using AIFloats

F = Binary5p2se          # a 5-bit format: code points are 0x00:0x1f
try
    fromcode(F, 0xff)
catch err
    err
end
```

## Calculate with Julia syntax

Same-format values support Julia's ordinary numeric spelling. These methods use
the task's [`DefaultProjection`](@ref), initially `RTE_SN`.

```@example basic_arithmetic
using AIFloats

F = Binary8p4se
x, y = F(1.5), F(0.25)
@assert x + y === Add(x, y)          # each operator is one register call
(x + y, x * y, x / y, sqrt(x), exp(y))
```

The named register operations are available when the result format and
projection should be visible at the call site:

```@example basic_register
using AIFloats

F = Binary8p4se
x, y = F(1.5), F(0.25)
(Add(F, RTE_SN, x, y), Multiply(F, RTZ_SF, x, y))
```

See [Operations](@ref operations) for the full family: signatures, mixed operand
formats, the correctness route each operation takes, and the refusals.

## Convert values explicitly

Construction uses the task's default projection. [`Convert`](@ref) makes the format and
projection explicit:

```@example basic_convert
using AIFloats

F = Binary8p4se
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

x = Binary8p4se(1.5)
Small = Binary5p2se
s = Convert(Small, RTE_SN, x)
(s, decode(s), Float64(s))
```

## Classify and navigate

```@example basic_neighbors
using AIFloats

F = Binary8p4se
x = F(1.5)
(Class(x), NextLessThan(x), NextGreaterThan(x), eps(x))
```

Special accessors make important endpoints easy to name:

```@example basic_endpoints
using AIFloats

F = Binary8p4se
(MinPositiveOf(F), MinNormalOf(F), MaxFiniteOf(F))
```

Continue with [Intermediate examples](@ref examples-intermediate) for explicit
rounding control and array operations.

```@meta
DocTestSetup = nothing
```
