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

!!! note "The normative source, and what it is not"
    Every semantic claim in this documentation conforms to: the
    **IEEE Working Group P3109 Interim Report on Arithmetic Formats for Machine
    Learning**, version 4.0.3 (1 September 2026), available here:
    [P3109/Public](https://github.com/P3109/Public/blob/main/IEEE%20P3109%20Interim%20Report.pdf).

    That report is an **unapproved draft**; its cover states it must not be used for
    conformance or compliance purposes. [`conformance`](@ref) reports what this package
    implements, in the shape the draft's §4.6 describes — not IEEE approval, not a
    certification, and not a compliance determination.

    AIFloats uses some language and spelling that differs from the report. In all cases
    this is done to glean advantage from working with Julia, in accord with Julia best
    practices. In all cases, this is noted in the docstring, or in the documentation.
    Often the Julia function name does not shadow the report's name, and both are
    available.

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
    AIFloats.jl models formats and their values, including encoding, decoding,
    correctly rounded scalar and array operations, shared-scale blocks, and
    packed storage. See [Implementation status](@ref status) for the supported
    surface and deliberate limits.

## Installation

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

## Where to go next

| Page | What it covers |
|:--|:--|
| [Getting started](@ref getting-started) | Build a format and ask it questions, step by step |
| [Concepts](@ref concepts) | What K, P, S, and D mean, and why the rules are what they are |
| [Binary formats](@ref formats) | The full `Binary` API — construction, accessors, validity, display |
| [Projections](@ref projections) | Rounding and saturation modes, and the projections that pair them |
| [Operations](@ref operations) | The register: signatures, result formats, refusals, correctness route |
| [Algorithms](@ref algorithms) | How the results are obtained: stochastic rounding, interval enclosure, the sticky protocol |
| [Basic examples](@ref examples-basic) | Construct datums, calculate, inspect, and convert |
| [Intermediate examples](@ref examples-intermediate) | Explicit projections, stochastic rounding, and arrays |
| [Advanced examples](@ref examples-advanced) | Packed storage, blocks, reductions, and block conversion |
| [Technical examples](@ref examples-technical) | Carrier, table-policy, conformance, and oracle diagnostics |
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
