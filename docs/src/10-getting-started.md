# [Getting started](@id getting-started)

```@meta
CurrentModule = AIFloats
DocTestSetup = :(using AIFloats)
```

## Install

AIFloats.jl is not yet in the General registry, so install it from its repository:

```julia
julia> using Pkg; Pkg.add(url = "https://github.com/JeffreySarnoff/AIFloats.jl")

julia> using AIFloats
```

To work against a local checkout instead:

```julia
julia> using Pkg; Pkg.develop(path = "/path/to/AIFloats.jl")
```

Once the package is registered, `Pkg.add("AIFloats")` will be the short form.

## Describe a format

A format needs four things: a bitwidth, a precision, a signedness, and a domain.

```jldoctest started
julia> B = Binary(8, 4, SIGNED, FINITE)
Binary{8, 4, ±, ⏥}
```

That reads as: 8 bits wide, 4 bits of significand, negatives representable, no infinities.
The glyphs in the display are a shorthand — `±` for signed, `⏥` for finite. Ask for the
spelled-out form with `string`:

```jldoctest started
julia> string(B)
"Binary{8, 4, SIGNED, FINITE}"
```

`Binary` returns a **type**, not a value:

```jldoctest started
julia> B isa Type
true
```

That is deliberate: a format is a compile-time description, and the four parameters are all
there is to it. There is no instance to make — `B()` is an error, on purpose. When you need
a value to store in an array or to dispatch on, you want a *datum*, and its type is
`BinaryValue(B)`:

```jldoctest started
julia> T = BinaryValue(B)
BinaryValue(Binary8p4sf)

julia> B(1.5) isa T
true
```

Those three spellings are the whole model, and the rest of the documentation uses these
letters for them:

| Letter | What it is | How you get it |
|:--|:--|:--|
| `F` | the **format** | `Binary(K, P, S, D)`, or an alias like `Binary8p4se` |
| `T` | the **datum type** | `BinaryValue(F)` |
| `x` | a **datum** | `F(1.5)`, `T(1.5)`, `fromcode(F, c)` |

A datum is not an instance of its format — `B(1.5) isa B` is `false`, because a format
describes a value set rather than belonging to one.

## Values and code points are distinct views

Every constructor argument is a **number**, and that includes every `Unsigned`. To name a
raw code point, use [`fromcode`](@ref) — a different question with a different spelling:

```jldoctest started
julia> F = Binary8p4se;

julia> fromcode(F, 0x45)          # the datum stored at code point 0x45
1.625

julia> F(0x45)                    # the number 0x45 is 69, projected into F
72.0
```

They used to be told apart by the argument's type, which silently made `F(codepoint(y))` a
reinterpretation. Now the two never collide.

## Read the fields back

```jldoctest started
julia> BitwidthOf(B), PrecisionOf(B)
(8, 4)

julia> SignednessOf(B), DomainOf(B)
(true, false)
```

`SignednessOf` and `DomainOf` return raw `Bool`s. The predicates are usually easier to read:

```jldoctest started
julia> is_signed(B), is_unsigned(B)
(true, false)

julia> is_finite(B), is_extended(B)
(true, false)
```

Each capitalized query has a lower-case Julia-style spelling, and the pair is **the same
function object** — not a wrapper, not a compatibility shim:

```jldoctest started
julia> bitwidth === BitwidthOf, signedness === SignednessOf
(true, true)

julia> bitwidth(B), domain(B), codetype(B)
(8, false, UInt8)
```

[`formatinfo`](@ref) answers all of them at once, and folds to a literal when the format is
known at compile time:

```jldoctest started
julia> info = formatinfo(B);

julia> info.bitwidth, info.precision, info.exponentbits, info.exponentbias
(8, 4, 4, 8)
```

## Pick storage types

Two helpers answer "what do I keep this in?":

```jldoctest started
julia> CodeType(B)
UInt8

julia> ValueType(B)
Float32
```

[`CodeType`](@ref) is wide enough for any bit pattern of the format; [`ValueType`](@ref) is
wide enough to hold any of its values exactly. Both widen as the format does:

```jldoctest started
julia> CodeType(16), ValueType(16)
(UInt16, Quadmath.Float128)
```

## Say how to round

Rounding and saturation are chosen together, as a [`Projection`](@ref):

```jldoctest started
julia> p = Projection(RTE, SF)
ρ(RTE, SF)

julia> RoundOf(p), SatOf(p)
(RTE, SF)
```

All 27 pairings already exist as constants, so you rarely build one:

```jldoctest started
julia> p === RTE_SF
true
```

The task's default is [`RTE_SN`](@ref) — round to nearest ties-to-even, no saturation:

```jldoctest started
julia> DefaultProjection()
ρ(RTE, SN)
```

That default is **task-local**, bound for a dynamic extent by
[`with_projection`](@ref) and never by a setter. Two other defaults are deliberately
different: `rand` draws under `RTZ_SN` and `randn` under `RTE_SF`. See
[Projections](@ref projections) for what each mode does.

## Invalid formats are rejected

Not every set of four numbers describes a real format. The constructor checks:

```jldoctest started
julia> Binary(8, 8, SIGNED, FINITE)
ERROR: ArgumentError: Invalid format: K=8, P=8, S=SIGNED, D=FINITE
[...]
```

Eight significand bits plus a sign bit needs nine bits, leaving nothing for the exponent.
The [Concepts](@ref concepts) page explains the bit budget these rules come from.

```@meta
DocTestSetup = nothing
```
