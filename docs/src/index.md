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

The documentation is in four parts, and the menu on the left follows the same shape.

**Learn the model.** Read in order the first time; each page assumes the one before it.

| Page | What it covers |
|:--|:--|
| [Getting started](@ref getting-started) | Build a format and ask it questions, step by step |
| [Concepts](@ref concepts) | What `K`, `P`, `S` and `D` mean, and why the rules are what they are |
| [Binary formats](@ref formats) | The `F` / `T` / `x` model, aliases, queries, validity, display |
| [Projections](@ref projections) | Rounding and saturation modes, the projections that pair them, and the defaults |
| [Operations](@ref operations) | The register: signatures, result formats, refusals, and how each result is reached |

**Worked examples.** Every block runs on its own in a fresh session.

| Page | What it covers |
|:--|:--|
| [Basic examples](@ref examples-basic) | Construct datums, calculate, inspect, convert |
| [Intermediate examples](@ref examples-intermediate) | Explicit projections, saturation, the stochastic contract, arrays |
| [Advanced examples](@ref examples-advanced) | Packed storage, blocks, reductions, block conversion |
| [Technical examples](@ref examples-technical) | Table policy, cache snapshots, diagnostics, conformance |

**Look something up.** Generated, and complete by construction.

| Page | What it covers |
|:--|:--|
| [Reference](@ref reference) | Every exported and `public` name, in four listings |
| [Formats, datums, projections](@ref) | `Binary`, the axes and queries, `BinaryValue` and the codec, display, projections |
| [Operations, kernels, storage](@ref) | The register operations, `vmap`/`vmap!`, the table policy surface, `PackedVector` |
| [Blocks and scaled operations](@ref) | `Block`, `BlockVector`, and the generated `Block*` and `Scaled*` families |
| [Conformance](@ref) | `conformance` and the ϰ registry, the IEEE 754 aliases, carrier-level types and switches |
| [Benchmark results](@ref benchmarks) | Generated from a run of the suite, with the commit and machine it describes |

**How it works, and how to work on it.** Mechanism rather than interface — none of it is a
stable contract.

| Page | What it covers |
|:--|:--|
| [Algorithms](@ref algorithms) | Stochastic rounding, interval enclosure, and the sticky protocol |
| [Implementation](@ref status) | What is implemented, the deliberate limits, and what costs what |
| [Dyadic Numbers](@ref dyadic-numbers) | The exact carrier behind the block reductions |
| [FMA](@ref fma128) · [FAA](@ref faa128) | The pure-Julia fused operations for `Float128` |
| [Contributing](@ref contributing) · [Developing](@ref dev_docs) | Filing an issue; running the tests, the benchmarks and the docs build |

## Contributors

```@raw html
<!-- ALL-CONTRIBUTORS-LIST:START - Do not remove or modify this section -->
<!-- prettier-ignore-start -->
<!-- markdownlint-disable -->

<!-- markdownlint-restore -->
<!-- prettier-ignore-end -->

<!-- ALL-CONTRIBUTORS-LIST:END -->
```
