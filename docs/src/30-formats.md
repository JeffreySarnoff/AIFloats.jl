# [Binary formats](@id formats)

```@meta
CurrentModule = AIFloats
DocTestSetup = :(using AIFloats)
```

[`Binary{K,P,S,D}`](@ref Binary) is the one format specifier. This page covers its
construction, its accessors, its aliases, and how it displays. For what the four parameters
*mean*, read [Concepts](@ref concepts) first.

## The canonical triad

Three spellings, three different questions. Every page uses these letters:

```jldoctest formats
julia> F = Binary8p4se          # the FORMAT — a type, and there is no instance
Binary{8, 4, ±, ∞}

julia> T = BinaryValue(F)       # the DATUM TYPE — a concrete AbstractFloat
BinaryValue(Binary8p4se)

julia> x = F(1.5)               # a DATUM of that type
1.5

julia> x isa T, x isa F
(true, false)
```

- `F()` is an error, on purpose — `F` already *is* the format.
- `F(x)` consumes a **number**, every `Integer` and `Unsigned` included.
- `fromcode(F, c)` consumes a **code point**. The two are different questions with
  different spellings, so `F(codepoint(y))` can never silently mean `y`.

```jldoctest formats
julia> fromcode(F, 0x45), F(0x45)
(1.625, 72.0)
```

The report's vocabulary differs from Julia's here. In Interim Report §3.1 a *floating-point
datum* is the mathematical element and a *floating-point value* is its code point in an
associated format. In Julia, `BinaryValue` is the object that stores that code point and
behaves numerically as the datum. This documentation says "datum" for the number and "code
point" for the encoding, and never uses "value" for both in one breath.

## Construction

```jldoctest formats
julia> B = Binary(16, 10, UNSIGNED, EXTENDED)
Binary{16, 10, +, ∞}
```

### It returns a type

`Binary(K, P, S, D)` gives back the parameterized type, and that type is the format —
there is no second, instance-shaped spelling of it:

```jldoctest formats
julia> B isa Type
true

julia> B()
ERROR: ArgumentError: Binary{16, 10, UNSIGNED, EXTENDED} is already the format; formats have no instances.
[...]
```

Every accessor and predicate in this package takes the format type. `B(x)` is not the
exception it looks like: it constructs the *datum* of `B` nearest `x`, and the datum type
is `BinaryValue(B)`.

### Singletons and `Bool`s are interchangeable

`S` accepts [`SIGNED`](@ref)/[`UNSIGNED`](@ref) or a `Bool`; `D` accepts
[`EXTENDED`](@ref)/[`FINITE`](@ref) or a `Bool`. In both cases `true` is the second-named
option — signed, extended.

```jldoctest formats
julia> Binary(16, 10, false, true) === B
true
```

The singletons are clearer at a call site and are what the accessors' documentation refers
to; the `Bool`s are convenient when the value is computed. Both reach the same type, because
both are canonicalized by `AIFloats.resolve_fields` before becoming parameters.

### Arguments are canonicalized

`K` and `P` are narrowed to `Int8` ([`IntParam`](@ref)), so the argument type does not affect
the result:

```jldoctest formats
julia> Binary(16, 10, SIGNED, FINITE) === Binary(Int32(16), Int32(10), SIGNED, FINITE)
true
```

!!! warning "`K` and `P` must have the same type"
    The constructor is `Binary(K::I, P::I, ...) where {I<:Integer}` — one type variable for
    both. Mixing them is a `MethodError`, so promote first:

    ```julia
    julia> Binary(Int8(8), 4, SIGNED, FINITE)
    ERROR: MethodError: no method matching Binary(::Int8, ::Int64, ...)

    julia> Binary(promote(Int8(8), 4)..., SIGNED, FINITE)
    Binary{8, 4, ±, ⏥}
    ```

### Invalid formats throw

```jldoctest formats
julia> Binary(2, 1, SIGNED, FINITE)
ERROR: ArgumentError: Invalid format: K=2, P=1, S=SIGNED, D=FINITE
[...]
```

The rules are `K > 2`, `P > 0`, and `P <= K - S`; [Concepts](@ref concepts) derives them
from the bit budget. [`Binary`](@ref) is the validator — it checks and throws, and there is
no supported non-throwing form. To test a combination without an exception, catch it:

```jldoctest formats
julia> isvalid_format(K, P, S, D) = try Binary(K, P, S, D); true catch; false end
isvalid_format (generic function with 1 method)

julia> isvalid_format(8, 4, SIGNED, FINITE), isvalid_format(2, 1, SIGNED, FINITE)
(true, false)
```

## Accessors

The four parameters come back out under names that say what they are:

```jldoctest formats
julia> BitwidthOf(B), PrecisionOf(B), SignednessOf(B), DomainOf(B)
(16, 10, false, true)
```

[`BitwidthOf`](@ref) and [`PrecisionOf`](@ref) return the stored `Int8`s;
[`SignednessOf`](@ref) and [`DomainOf`](@ref) return `Bool`s.

`AIFloats.TrailingSignificantBitsOf` gives the *stored* significand width, one less than the
precision:

```jldoctest formats
julia> PrecisionOf(B), AIFloats.TrailingSignificantBitsOf(B)
(10, 9)
```

## Predicates

Four predicates read better than comparing the `Bool`s:

```jldoctest formats
julia> is_unsigned(B), is_signed(B)
(true, false)

julia> is_extended(B), is_finite(B)
(true, false)
```

They also accept the singletons and raw `Bool`s directly, which is useful when you hold a
signedness rather than a format:

```jldoctest formats
julia> is_signed(SIGNED), is_extended(false)
(true, false)
```

!!! note "`is_finite` is about formats, not numbers"
    [`is_finite`](@ref) asks whether a *format* excludes the infinities. It is unrelated to
    `Base.isfinite`, which asks whether a number is one.

## Storage types

[`CodeType`](@ref) gives an unsigned integer wide enough for any code point of the format;
[`ValueType`](@ref) gives a float wide enough to hold any of its values exactly.

| `K` | [`CodeType`](@ref) | [`ValueType`](@ref) |
|:--|:--|:--|
| `K ≤ 8` | `UInt8` | `Float32` |
| `9 ≤ K ≤ 10` | `UInt16` | `Float64` |
| `K > 10` | `UInt16` | `Float128` |

Both accept a bitwidth as well as a format:

```jldoctest formats
julia> CodeType(B), ValueType(B)
(UInt16, Quadmath.Float128)

julia> CodeType(8), ValueType(8)
(UInt8, Float32)
```

## Display

A format has two written forms, and which appears depends on how it is shown.

```jldoctest formats
julia> B                                    # the REPL uses MIME"text/plain": glyphs
Binary{16, 10, +, ∞}

julia> repr(B)                              # plain show: words
"Binary{16, 10, UNSIGNED, EXTENDED}"
```

The same split is available as functions — lowercase `string` for words, capital `String`
for glyphs:

```jldoctest formats
julia> string(B)
"Binary{16, 10, UNSIGNED, EXTENDED}"

julia> String(B)
"Binary{16, 10, +, ∞}"
```

The glyphs are one per axis:

| Axis | Glyph | Meaning |
|:--|:--|:--|
| signedness | `±` | [`SIGNED`](@ref) |
| | `+` | [`UNSIGNED`](@ref) |
| domain | `∞` | [`EXTENDED`](@ref) |
| | `⏥` | [`FINITE`](@ref) |

This is *format* display. Datum display is a separate axis with its own scopes; see
[Datum display scope](@ref display-scope).

## Aliases

Every valid format in the `3 ≤ K ≤ 16` grid has a generated alias spelled the way the
report names formats (§3.2): `Binary⟨K⟩p⟨P⟩⟨s|u⟩⟨f|e⟩`. Those with `K ≤ 8` are exported;
the rest live in `AIFloats.Formats`.

```jldoctest formats
julia> Binary8p4se === Binary(8, 4, SIGNED, EXTENDED)
true

julia> AIFloats.Formats.Binary16p10ue === Binary(16, 10, UNSIGNED, EXTENDED)
true
```

An alias names a **format**. It is not a datum type and not a datum — `BinaryValue(F)` and
`F(x)` are those.

## Two spellings of every query

Each capitalized query has a lower-case Julia-style spelling. The pair is the *same generic
function object* — not a wrapper, not an adapter, not a compatibility shim, and with no
call-site cost either way:

| Capitalized | Julia-style |
|:--|:--|
| [`BitwidthOf`](@ref) | [`bitwidth`](@ref) |
| [`SignednessOf`](@ref) | [`signedness`](@ref) |
| [`DomainOf`](@ref) | [`domain`](@ref) |
| [`BinaryFormatOf`](@ref) | [`formatof`](@ref) |
| [`CodeType`](@ref) | [`codetype`](@ref) |
| [`ValueType`](@ref) | [`valuetype`](@ref) |

```jldoctest formats
julia> bitwidth === BitwidthOf, formatof === BinaryFormatOf
(true, true)
```

Use `formatof(x)` to recover a format from a datum you were handed. Do not write
`formatof(F)` when `F` is already the format.

[`formatinfo`](@ref) answers every static question at once, and folds to a literal when the
format is known at compile time:

```jldoctest formats
julia> info = formatinfo(Binary8p4se);

julia> info.name, info.bitwidth, info.precision, info.exponentbits
(:Binary8p4se, 8, 4, 4)

julia> info.datumtype
BinaryValue(Binary8p4se)
```

## [Datum display scope](@id display-scope)

How a **datum** prints is a separate question from how a format prints, and it has two
mechanisms with different reach:

| Mechanism | Scope |
|:--|:--|
| [`set_show_style!`](@ref) | **process-wide** fallback |
| an `IOContext` with `:binary_show_style` | that one `show`, composable |

```jldoctest formats
julia> x = Binary8p4se(1.5);

julia> sprint(show, x; context = :binary_show_style => :codepoint)
"0x44"

julia> sprint(show, x; context = :binary_show_style => :typed)
"Binary8p4se(1.5 ⇆ 0x44)"

julia> get_show_style()
:value
```

!!! warning "Library code should not call `set_show_style!`"
    It changes a process-wide preference that the caller may be relying on. Pass an
    `IOContext` instead. This is display state only — it is unrelated to the task-local
    numerical [`DefaultProjection`](@ref), which is bound rather than set for exactly the
    same reason.

```@meta
DocTestSetup = nothing
```
