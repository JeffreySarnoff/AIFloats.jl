# YAML and JSON realization plan

Use only `../Maude` as the source. Keep Maude authoritative and generate both
serializations from one ordered data model.

1. Inventory every `.maude` file, including loaders, libraries, symbolic modules,
   contracts, examples, tests, and proof slices. Include inventory JSON/TSV,
   proof JSON/TSV, and test-vector JSON as supporting data.
2. Represent each source as ordered records: comments, module/theory/view
   boundaries, imports, declarations, equations, memberships, and commands.
   Expose signatures, partial arrows, labels, conditions, attributes, parameters,
   and view mappings. Preserve terms and module expressions in Maude syntax.
3. Retain exact source text per record and source hashes. Generate paired YAML
   and JSON documents, a schema, and a manifest with module and load indexes.
   Preserve evidence statuses and provenance without upgrading their claims.
4. Validate schemas, complete source coverage, serialization equality, extracted
   fields, dependency resolution, and byte-exact regeneration. Reject unknown
   syntax, stale artifacts, duplicate keys, and unsafe output paths.
5. Test malformed and adversarial inputs. Regenerate a temporary Maude tree
   from each serialization and run the existing loader/example checks and
   executable suites against the regenerated specification.

Review refinements: an arithmetic reimplementation would introduce a second
semantics and could incorrectly evaluate contracts or residual symbolic terms.
Instead, this is a structured, lossless source realization with execution through
Maude. Do not flatten parameterized modules, reorder equations, coerce rational
terms to floats, split metadata at semicolons, or interpret evidence as proof.
Raw text and extracted fields must agree; neither may silently override the other.
The parser supports the syntax present in this tree and fails closed on extensions.

Acceptance: all source files represented, YAML equals JSON, all regenerated
source bytes match, negative tests pass, and regenerated executable checks pass.
Document unresolved source limitations separately from representation fidelity.
