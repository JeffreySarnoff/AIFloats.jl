# [Getting started](@id getting-started)

```@meta
CurrentModule = AIFloats
DocTestSetup = :(using AIFloats)
```

## Install

```julia
julia> using Pkg; Pkg.add("AIFloats")

julia> using AIFloats
```

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
there is to it. When you need a value — to store in an array, say, or to dispatch on — call
the type:

```jldoctest started
julia> b = B()
Binary{8, 4, ±, ⏥}
```

Everything below works the same on either one.

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

`RTE_SF` — round to nearest, ties to even, saturating — is the conventional default.

## Invalid formats are rejected

Not every set of four numbers describes a real format. The constructor checks:

```jldoctest started
julia> Binary(8, 8, SIGNED, FINITE)
ERROR: ArgumentError: Invalid format: K=8, P=8, S=true, D=false
[...]
```

Eight significand bits plus a sign bit needs nine bits, leaving nothing for the exponent.
The [Concepts](@ref concepts) page explains the bit budget these rules come from.

```@meta
DocTestSetup = nothing
```
