# [Binary formats](@id formats)

```@meta
CurrentModule = AIFloats
DocTestSetup = :(using AIFloats)
```

[`Binary{K,P,S,D}`](@ref Binary) is the one format specifier. This page covers its
construction, its accessors, and how it displays. For what the four parameters *mean*, read
[Concepts](@ref concepts) first.

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

`AIFloats.validformat` holds the rules — `K > 2`, `P > 0`, `P <= K - S` — and can be called
directly to test a combination without building it.

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

A format's two renderings are the spelled-out `string` and the glyphic `String`:

```jldoctest formats
julia> string(B)
"Binary{16, 10, UNSIGNED, EXTENDED}"

julia> String(B)
"Binary{16, 10, +, ∞}"
```

```@meta
DocTestSetup = nothing
```
