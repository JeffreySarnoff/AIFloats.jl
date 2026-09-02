# [Reference](@id reference)

Every **public** name in AIFloats.jl: the exported bindings and those declared
`public`.

The listing pages below are generated during the documentation build from
`Base.isexported` and `Base.ispublic`, and the build fails if a public binding is
neither documented nor listed as a reviewed exemption. The reference is therefore
complete by construction, and holds nothing private.

Names you can call unqualified are exported; the rest are `public` and are reached
as `AIFloats.name`.

The 504 generated format aliases are deliberately absent. Each says only that it
is the format its own name spells out — `Binary6p3ue` is
`Binary(6, 3, UNSIGNED, EXTENDED)` — so listing the 120 exported ones buried the
entries that carry information. They keep their docstrings and still answer to
`?Binary6p3ue`; [Concepts](@ref concepts) gives the naming scheme once and in
full.

| Page | What it lists |
|:--|:--|
| [Formats, datums, projections](@ref) | `Binary` and its aliases, the four axes, the format queries, `BinaryValue` and the codec, datum display, and the projection vocabulary |
| [Operations, kernels, storage](@ref) | the register operations, `vmap`/`vmap!` and the table policy surface, and `PackedVector` |
| [Blocks and scaled operations](@ref) | `Block`, `BlockVector`, and the generated `Block*`, `Scaled*`, and block-conversion families |
| [Conformance](@ref) | `conformance` and the ϰ registry, the IEEE 754 aliases, and the carrier-level types and switches |

For the narrative introduction to these names, start at
[Getting started](@ref getting-started); for the operation family as a whole, see
[Operations](@ref operations).

Implementation-only material — including the `AIFloats.DyadicNumbers` carrier and
its `Dyadic` type — lives on [Dyadic Numbers](@ref dyadic-numbers) and is explicitly
unstable.
