# AIFloats

**Small binary floating-point formats for machine learning, following IEEE P3109.**

At 8 bits and below, the choices IEEE 754 made for 32- and 64-bit arithmetic stop paying for
themselves — a second NaN or a signed zero costs a noticeable share of everything the format
can say. [IEEE P3109](https://JeffreySarnoff.github.io/AIFloats.jl/dev/20-concepts/), the
draft standard for arithmetic formats for machine learning, spends those code points on
numbers instead. A P3109 format is determined by four parameters, and AIFloats.jl models
exactly those four.

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
> declaration. See [Implementation status](https://JeffreySarnoff.github.io/AIFloats.jl/dev/50-status/).

## Installation

```julia
julia> using Pkg; Pkg.add("AIFloats")
```

## Documentation

[Getting started](https://JeffreySarnoff.github.io/AIFloats.jl/dev/10-getting-started/) ·
[Concepts](https://JeffreySarnoff.github.io/AIFloats.jl/dev/20-concepts/) ·
[Binary formats](https://JeffreySarnoff.github.io/AIFloats.jl/dev/30-formats/) ·
[Projections](https://JeffreySarnoff.github.io/AIFloats.jl/dev/40-projections/) ·
[Reference](https://JeffreySarnoff.github.io/AIFloats.jl/dev/95-reference/)

---

[![Stable Documentation](https://img.shields.io/badge/docs-stable-blue.svg)](https://JeffreySarnoff.github.io/AIFloats.jl/stable)
[![Development documentation](https://img.shields.io/badge/docs-dev-blue.svg)](https://JeffreySarnoff.github.io/AIFloats.jl/dev)
[![Test workflow status](https://github.com/JeffreySarnoff/AIFloats.jl/actions/workflows/Test.yml/badge.svg?branch=main)](https://github.com/JeffreySarnoff/AIFloats.jl/actions/workflows/Test.yml?query=branch%3Amain)
[![Coverage](https://codecov.io/gh/JeffreySarnoff/AIFloats.jl/branch/main/graph/badge.svg)](https://codecov.io/gh/JeffreySarnoff/AIFloats.jl)
[![Lint workflow Status](https://github.com/JeffreySarnoff/AIFloats.jl/actions/workflows/Lint.yml/badge.svg?branch=main)](https://github.com/JeffreySarnoff/AIFloats.jl/actions/workflows/Lint.yml?query=branch%3Amain)
[![Docs workflow Status](https://github.com/JeffreySarnoff/AIFloats.jl/actions/workflows/Docs.yml/badge.svg?branch=main)](https://github.com/JeffreySarnoff/AIFloats.jl/actions/workflows/Docs.yml?query=branch%3Amain)
[![DOI](https://zenodo.org/badge/DOI/FIXME)](https://doi.org/FIXME)
[![Contributor Covenant](https://img.shields.io/badge/Contributor%20Covenant-2.1-4baaaa.svg)](CODE_OF_CONDUCT.md)
[![All Contributors](https://img.shields.io/github/all-contributors/JeffreySarnoff/AIFloats.jl?labelColor=5e1ec7&color=c0ffee&style=flat-square)](#contributors)
[![BestieTemplate](https://img.shields.io/endpoint?url=https://raw.githubusercontent.com/JuliaBesties/BestieTemplate.jl/main/docs/src/assets/badge.json)](https://github.com/JuliaBesties/BestieTemplate.jl)

## How to Cite

If you use AIFloats.jl in your work, please cite using the reference given in [CITATION.cff](https://github.com/JeffreySarnoff/AIFloats.jl/blob/main/CITATION.cff).

## Contributing

If you want to make contributions of any kind, please first take a look at our [contributing guide directly on GitHub](docs/src/90-contributing.md) or the [contributing page on the website](https://JeffreySarnoff.github.io/AIFloats.jl/dev/90-contributing/)

---

### Contributors

<!-- ALL-CONTRIBUTORS-LIST:START - Do not remove or modify this section -->
<!-- prettier-ignore-start -->
<!-- markdownlint-disable -->

<!-- markdownlint-restore -->
<!-- prettier-ignore-end -->

<!-- ALL-CONTRIBUTORS-LIST:END -->
