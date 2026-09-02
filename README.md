# AIFloats

**Small binary floating-point formats for machine learning, following IEEE P3109.**

At 8 bits and below, the choices IEEE 754 made for 32- and 64-bit arithmetic stop paying for
themselves — a second NaN or a signed zero costs a noticeable share of everything the format
can say. [IEEE P3109](https://JeffreySarnoff.github.io/AIFloats.jl/dev/20-concepts.html), the
draft standard for arithmetic formats for machine learning, spends those code points on
numbers instead. A P3109 format is determined by four parameters, and AIFloats.jl models
exactly those four.

The normative source for this release is the **IEEE Working Group P3109 Interim Report on
Arithmetic Formats for Machine Learning**, version 4.0.3 (1 September 2026), at
[P3109/Public](https://github.com/P3109/Public/blob/main/IEEE%20P3109%20Interim%20Report.pdf),
PDF SHA-256 `7de115ed6882b7550b8fa61e81e5173857b340c3bfe30db8d4ad74b472229b9e`. That
document is an **unapproved draft**: its cover states it must not be used for conformance or
compliance purposes. `conformance()` reports what this package implements, in the shape the
draft's §4.6 describes — it is not a certification. Run `draft_identity()` for the identity
this build was compared against.

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

> **Scope.** AIFloats.jl models every P3109 format from 3 to 16 bits and computes with
> their values: code points and decoding, the projection engine (every rounding and
> saturation mode), the draft's operation register (correctly rounded), Julia's operator
> surface, array kernels, shared-scale blocks, packed storage, and a live conformance
> declaration. See [Implementation status](https://JeffreySarnoff.github.io/AIFloats.jl/dev/50-status.html).

## Performance

Small formats are only worth having if working with them is cheap, so the cost of every
layer is measured rather than asserted. The durable relationships:

- decoding is allocation-free, and `K ≤ 8` reads a generated constant table rather than
  computing the value;
- exactly-evaluated operations (`Add`, `Multiply`, `FMA`, the extremum family) are
  substantially cheaper than the enclosure-based ones (`Exp`, `Log`, `Sin`, …), and both
  are allocation-free;
- a warm table gather avoids per-element recomputation entirely, and is the reason array
  work is fast where the format grid is small enough to afford a table;
- compute kernels thread above a measured element-count threshold; the gather never
  threads, because it already runs at memory bandwidth;
- passing a projection explicitly (`Add(F, ρ, x, y)`) never reads the task default and is
  the only form whose cost does not depend on the caller's scope.

Absolute numbers belong to the machine that measured them and live on the generated
[Benchmark results](https://JeffreySarnoff.github.io/AIFloats.jl/dev/60-benchmarks.html)
page, produced by `benchmark/runbenchmarks.jl` in an isolated environment.
[Performance characteristics](https://JeffreySarnoff.github.io/AIFloats.jl/dev/50-status.html#performance)
documents the thresholds and the cases that deliberately stay on a slower, always-correct
path.

## Installation

Not yet in the General registry — install from the repository:

```julia
julia> using Pkg; Pkg.add(url = "https://github.com/JeffreySarnoff/AIFloats.jl")
```

For a local checkout, `Pkg.develop(path = "/path/to/AIFloats.jl")`. Requires Julia 1.12.

## Documentation

[Getting started](https://JeffreySarnoff.github.io/AIFloats.jl/dev/10-getting-started.html) ·
[Concepts](https://JeffreySarnoff.github.io/AIFloats.jl/dev/20-concepts.html) ·
[Binary formats](https://JeffreySarnoff.github.io/AIFloats.jl/dev/30-formats.html) ·
[Projections](https://JeffreySarnoff.github.io/AIFloats.jl/dev/40-projections.html) ·
[Operations](https://JeffreySarnoff.github.io/AIFloats.jl/dev/45-operations.html) ·
[Reference](https://JeffreySarnoff.github.io/AIFloats.jl/dev/95-reference.html)

---

[![Stable Documentation](https://img.shields.io/badge/docs-stable-blue.svg)](https://JeffreySarnoff.github.io/AIFloats.jl/stable)
[![Development documentation](https://img.shields.io/badge/docs-dev-blue.svg)](https://JeffreySarnoff.github.io/AIFloats.jl/dev)
[![Test workflow status](https://github.com/JeffreySarnoff/AIFloats.jl/actions/workflows/Test.yml/badge.svg?branch=main)](https://github.com/JeffreySarnoff/AIFloats.jl/actions/workflows/Test.yml?query=branch%3Amain)
[![Coverage](https://codecov.io/gh/JeffreySarnoff/AIFloats.jl/branch/main/graph/badge.svg)](https://codecov.io/gh/JeffreySarnoff/AIFloats.jl)
[![Lint workflow Status](https://github.com/JeffreySarnoff/AIFloats.jl/actions/workflows/Lint.yml/badge.svg?branch=main)](https://github.com/JeffreySarnoff/AIFloats.jl/actions/workflows/Lint.yml?query=branch%3Amain)
[![Docs workflow Status](https://github.com/JeffreySarnoff/AIFloats.jl/actions/workflows/Docs.yml/badge.svg?branch=main)](https://github.com/JeffreySarnoff/AIFloats.jl/actions/workflows/Docs.yml?query=branch%3Amain)
[![Contributor Covenant](https://img.shields.io/badge/Contributor%20Covenant-2.1-4baaaa.svg)](CODE_OF_CONDUCT.md)
[![All Contributors](https://img.shields.io/github/all-contributors/JeffreySarnoff/AIFloats.jl?labelColor=5e1ec7&color=c0ffee&style=flat-square)](#contributors)
[![BestieTemplate](https://img.shields.io/endpoint?url=https://raw.githubusercontent.com/JuliaBesties/BestieTemplate.jl/main/docs/src/assets/badge.json)](https://github.com/JuliaBesties/BestieTemplate.jl)

## How to Cite

If you use AIFloats.jl in your work, please cite it using the metadata in
[CITATION.cff](https://github.com/JeffreySarnoff/AIFloats.jl/blob/main/CITATION.cff).
The package has no DOI yet; cite the repository and the version you used.

## Contributing

If you want to make contributions of any kind, please first take a look at our [contributing guide directly on GitHub](docs/src/90-contributing.md) or the [contributing page on the website](https://JeffreySarnoff.github.io/AIFloats.jl/dev/90-contributing.html)

---

### Contributors

<!-- ALL-CONTRIBUTORS-LIST:START - Do not remove or modify this section -->
<!-- prettier-ignore-start -->
<!-- markdownlint-disable -->

<!-- markdownlint-restore -->
<!-- prettier-ignore-end -->

<!-- ALL-CONTRIBUTORS-LIST:END -->
