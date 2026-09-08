# Maude to Lean

`spec2.lean` is the source translation. [Lean/](Lean/README.md) reorganizes it
into 24 modules while preserving its declarations, proofs, attributes, axioms,
and `Maude` namespace. Work from that library for navigation and validation.

## Validate the organized translation

From `docs/other/Maude/Lean`:

```sh
python3 reorganize.py
lake build P3109.Relations.AxiomaticEquality
lake env lean CheckFoundations.lean
```

`reorganize.py` checks the pinned source hash and byte-for-byte reconstruction;
it does not write files. `--write` regenerates the modules and manifest.
For a new source translation, review and update the pinned hash and section
boundaries in that script before regeneration.

Foundational compilation passed. Full compilation was interrupted in the large
mutual equational-equality definition under resource pressure; a later bounded
attempt timed out. Later modules and the full importing client remain unverified.
See [Lean/VALIDATION.md](Lean/VALIDATION.md) for recorded evidence. The full checks,
when sufficient resources are available, are:

```sh
lake build
lake env lean Check.lean
```

## Translating a multi-file specification

Use one loader and select the top module. For example, from this directory,
the basic command shape for a fresh candidate translation is:

```sh
maude2lean --lean-version 4 --module P3109-SPEC \
  -o /tmp/P3109-candidate.lean load-spec.maude
```

This illustrates entry-point selection, not the exact regeneration command for
`spec2.lean`. Check the installed translator's `--help` and builtin mapping options
before replacing the pinned translation.

Maude follows the loader's relative `load`/`sload` paths; `sload` avoids repeated
loading of shared dependencies. The translator flattens the selected module and
its imports into one Lean file. It does not reproduce the Maude directory tree.

Lean inductive types cannot acquire new constructors in later files. Maude kinds
and mutually defined relations therefore need complete definitions before their
lemmas can be split into separate modules. The organized library preserves all
six original mutual blocks and follows source order. Translating overlapping
Maude modules independently instead creates duplicate types; separate namespaces
avoid naming conflicts but do not make those types interchangeable.

## Semantic limits

The current source uses native `Rat` and `String` aliases, but still represents
many operations by axioms. In particular, `ascii`, `char`, `find`, `modExp`, and
`rfind` have no semantics supplied by the reorganization. Successful Lean
compilation checks well-formedness, not axiom consistency or IEEE conformance.

Earlier translator experiments recorded collapsed numeric/string literals,
uninterpreted builtin arithmetic, and Lean forward-reference failures. Treat
those as historical findings, not a description of every current declaration.
Before accepting a new translation, check literal preservation, builtin meanings,
equation guards, and compilation against the Maude source.

An `owise` fallback is a Maude execution strategy and cannot safely become an
unconditional Lean equation. The current Maude specification avoids `owise`:
conformance name/arity checks use finite tables and structural recursion. Keep
that distinction when changing equations or translator settings.
