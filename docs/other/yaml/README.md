# Maude specification in YAML and JSON

An ordered, lossless data representation of `../Maude`. All 49 `.maude` files
and 11 supporting JSON/TSV files are represented. YAML and JSON carry identical
data and can independently regenerate the original source bytes.

This realizes the specification as structured data with execution through Maude.
It does not implement a second arithmetic evaluator. Maude terms, module
expressions, attributes, and conditions retain their original language: rationals
remain exact, partial operators remain partial, and symbolic residuals and
unimplemented contracts retain their meaning.

## Use

From the repository root, with Python 3.10+ and Maude installed:

```sh
python3 -m pip install -r docs/other/yaml/requirements.txt
python3 -B docs/other/yaml/realize.py check
python3 -B docs/other/yaml/validate.py
python3 -B docs/other/yaml/realize.py restore --format yaml --output /tmp/restored-maude
```

The restore destination must be new or empty. Use `--format json` for JSON.
Run `maude load-core.maude` from the restored directory, or choose another loader.
`validate.py` reconstructs both formats in temporary directories, verifies exact
bytes, and runs the original loader, example, core, and symbolic checks against
each reconstruction. It copies the original Python test harness into those
directories; test vectors and operation inventories come from the realization.

After editing the authoritative Maude source, run:

```sh
python3 -B docs/other/yaml/realize.py generate
python3 -B docs/other/yaml/validate.py
```

## Layout and data model

- `sources/` mirrors Maude paths with `.yaml` and `.json` appended. It includes
  libraries, symbolic modules, contracts, all four loaders, examples, tests,
  proof slices, operation inventory, traceability, proof records, and vectors.
- `manifest.yaml` / `manifest.json` index sources and hashes, named definitions,
  ordered loads, module references, and record counts.
- `schema.yaml` / `schema.json` define the source-document schema. Both express
  the same JSON Schema; the generator also checks semantic field agreement.
- `PLAN.md` records the reviewed implementation plan.
- `VALIDATION.md` records coverage and the completed validation results.

Each Maude document has `version`, `path`, `sha256`, `type`, and ordered `records`.
Each record has a one-based `line`, `kind`, `fields`, and exact `text`. For example,
an operator exposes `names`, `domain`, `arrow` (`->` or `~>`), `range`, and
`attributes`; an axiom exposes `label`, `lhs`, `rhs` or `sort`, `condition`, and
`attributes`. Module headers expose parameters; views expose source and target.
Import expressions preserve instantiation and renaming syntax, including labels.
Boundaries and record order determine declaration scope; imports are not flattened.

The term strings are syntax, not a resolved term AST. Builtin Maude modules
remain external dependencies. Consumers can query structured declarations, then
use Maude for parsing overloaded operators, instantiation, or evaluation.

Supporting documents contain parsed `data` and exact `text`. TSV uses `columns`
and positional `rows`, preserving literal headers (including the current spaces
before `id` in proof obligations). No numeric or evidence-status coercion is made.

## Fidelity and limits

Checks reject unknown syntax, stale/missing/extra source artifacts, duplicate
mapping keys, inconsistent extracted fields, hash changes, missing internal
loads/references, and escaping paths. Generation is deterministic and preserves
comments, equation order, whitespace, and line endings. The parser is intentionally
limited to syntax used by this specification; new syntax needs explicit support.

Maude remains authoritative: edit it and regenerate. Editing only extracted fields
is rejected. Source hashes establish snapshot identity, not mathematical validity.
The existing stale plan hash in `inventory/source.json`, open proof obligations,
external backend requirements, and unverified claims remain as recorded in Maude.
Python tooling, prose, Lean translations, and proof-session text logs remain in
the source tree; they are not Maude specification syntax or structured input data.
