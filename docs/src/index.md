```@meta
CurrentModule = AIFloats
```

# AIFloats

AIFloats.jl describes the small binary floating-point formats used in machine learning —
the 8-bit, 6-bit, 4-bit, and smaller formats that trade precision for memory bandwidth.

It follows **IEEE P3109**, the draft standard for arithmetic formats for machine learning,
in which a format is completely determined by four things: how many bits it occupies, how
many of those carry the significand, whether it represents negative values, and whether it
includes the infinities. Those four make a [`Binary`](@ref) format specifier.

```julia
julia> using AIFloats

julia> B = Binary(8, 4, SIGNED, FINITE)   # 8 bits wide, 4 bits of precision
Binary{8, 4, ±, ⏥}

julia> BitwidthOf(B), PrecisionOf(B)
(8, 4)

julia> is_signed(B), is_extended(B)
(true, false)

julia> CodeType(B), ValueType(B)          # how to store a code, and a value
(UInt8, Float32)
```

!!! note "Scope"
    AIFloats.jl currently models formats, not numbers. It will tell you what a format *is*
    and answer questions about it, but it does not yet produce the values a format
    represents, encode or decode code points, or do arithmetic. See
    [Implementation status](@ref status) for what exists today.

## Installation

```julia
julia> using Pkg; Pkg.add("AIFloats")
```

## Where to go next

| Page | What it covers |
|:--|:--|
| [Getting started](@ref getting-started) | Build a format and ask it questions, step by step |
| [Concepts](@ref concepts) | What K, P, S, and D mean, and why the rules are what they are |
| [Binary formats](@ref formats) | The full `Binary` API — construction, accessors, validity, display |
| [Projections](@ref projections) | Rounding and saturation modes, and the projections that pair them |
| [Implementation status](@ref status) | What is implemented and what is not |
| [Reference](@ref reference) | Every documented name |

## Contributors

```@raw html
<!-- ALL-CONTRIBUTORS-LIST:START - Do not remove or modify this section -->
<!-- prettier-ignore-start -->
<!-- markdownlint-disable -->

<!-- markdownlint-restore -->
<!-- prettier-ignore-end -->

<!-- ALL-CONTRIBUTORS-LIST:END -->
```
