# Validation — 2026-09-08

Command: `python3 -B docs/other/yaml/validate.py` with the pinned requirements
installed. The validator was installed in `/tmp/maude-yaml-validation` for this
run and exposed through `PYTHONPATH`; no project environment was modified.

| Check | Result |
| --- | --- |
| Complete source coverage | 49 Maude files + 11 supporting files |
| Named definitions | 49 functional modules, 5 theories, 62 views |
| Source axioms | 516 equations, 225 conditional equations, 9 conditional memberships |
| Schema, fields, hashes, deterministic output | Passed for all 60 documents in both formats |
| Exact restoration | All 60 source files byte-identical from each format |
| Representation tests | 9 passed |
| Loaders and examples | All 4 loaders and both examples passed for each format |
| Core executable suite | 67,541 checks passed for each format |
| Symbolic executable suite | 194 checks passed for each format |

The tests run against temporary reconstructed trees. The original Maude Python
harness is copied into each tree; reconstructed inventories and fixtures supply
its data. Manifest hashes identify the validated source snapshot.

These results establish representation fidelity and preserve the existing bounded
executable checks. They do not discharge the real-number contracts, external
backend obligations, saturation refinement, or other open proof obligations.
The source's historical plan-hash mismatch remains recorded without alteration.
