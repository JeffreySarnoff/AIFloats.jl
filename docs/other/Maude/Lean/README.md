# Organized Lean translation

This library reorganizes `../spec2.lean` without changing its declarations,
proofs, attributes, axioms, or `Maude` namespace. The requested filename
`spect2.lean` was absent; `spec2.lean` is the source used here.

The lossless source check and foundational compilation pass. Full compilation
was interrupted under memory pressure in the large equational-equality
definition; later modules remain unverified. See [VALIDATION.md](VALIDATION.md)
for the exact completed checks and remaining work.

From this directory, with the pinned Lean toolchain installed:

```sh
lake build
lake env lean Check.lean
python3 reorganize.py
```

Use `import P3109` for the entire specification. A narrower import such as
`import P3109.Syntax` loads that stage and its predecessors. The package has
no external dependencies. `Check.lean` checks the public entry point, original
names, simplifier attributes, rewrite lemmas, and representation instances.
For a smaller check of the foundational import boundary, run
`lake build P3109.Relations.AxiomaticEquality` followed by
`lake env lean CheckFoundations.lean`.

## Layout

| Modules under `P3109/` | Contents |
| --- | --- |
| `Foundations`, `Syntax` | Native type aliases, Maude sorts, subsorting, syntax kinds and operators |
| `Native/Operators`, `Predicates` | Native operator axioms, kind assignment, constructor predicates |
| `Relations/AxiomaticEquality` | Equality modulo Maude axioms |
| `Relations/EquationalEquality` | Mutually defined sort membership and equality modulo equations |
| `Native/Equations` | Congruence and equation axioms for native replacements |
| `Relations/Rewriting` | Mutually defined single-step and repeated rewriting |
| `Lemmas/Congruence` | Generic relation congruence theorem |
| `Lemmas/Equations/` | Boolean, extended-real, format, sequence/block, conformance lemmas and native attributes |
| `Lemmas/Rewriting/` | Boolean, extended-real, format, sequence, block, conformance, rational and string rewrite lemmas |
| `Representation` | String conversion and `Repr` instances |

All six original mutual blocks stay intact. Imports follow source order to
preserve the elaboration context, including accumulated global attributes.
The larger kernel modules and rational rewriting module reflect the source's
recursive structure and namespace organization.

## Preservation and maintenance

[PLAN.md](PLAN.md) records the plan and its review. [manifest.json](manifest.json)
maps each module to its inclusive source lines and SHA-256 body hash.
`python3 reorganize.py` verifies the generated files against the pinned source
and verifies byte-for-byte reconstruction, including comments and whitespace.
It makes no changes. `python3 reorganize.py --write` explicitly regenerates
the modules and manifest. Builds never regenerate source files.

For a new translation, review and update the source hash and section boundaries
in `reorganize.py`, regenerate, and repeat compilation and client checks. To
keep preservation verifiable, make semantic changes in the source translation
before regenerating, rather than editing extracted modules independently.

This remains the original translation's logical model: native operations
represented by axioms remain axioms. In particular, reorganizing does not
supply missing semantics for `ascii`, `char`, `find`, `modExp`, or `rfind`.
Successful compilation checks Lean well-formedness, not axiom consistency
or conformance to the IEEE specification.
