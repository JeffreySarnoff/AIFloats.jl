# Conversion checkpoint

Status: **conversion complete and reviewed**. Updated 2026-09-08.

## Final position

- Implemented the independent `P3109Reference` package under this directory,
  using the Maude sources and the specified idiomatic Julia guide. Existing
  repository Julia implementation, tests and related documentation were excluded.
- All 193 source API names have implementations and concrete test references.
  Shared exact kernels support scalar, scaled and block operations; symbolic
  decisions, residuals, contracts and finite conformance accounting are retained.
- Reviewed/refined the plans; completed `improvedconversion.md`, API/tool docs,
  source/rule/operation/case inventories, dependency records and proof obligations.
- Removed the four stale standalone assertions from each Maude tree at the
  user's request. Refreshed their YAML/JSON copies and manifests; files now
  contain load-only checks with accurate zero counts. No adaptations are ported.

## Verified results

| Gate | Result and evidence |
| --- | --- |
| Julia runtime | 1.13.0-rc4, official archive checksum verified; `evidence/runtime.toml` |
| Isolated package tests | 347,580 source assertions and 902 additional checks pass; `evidence/runs/pkg-test.txt` |
| Detailed fixture comparison | All 11 suites pass with count, ID and hash validation; `evidence/runs/julia-cases.json` |
| Fresh Maude | Core 67,541; symbolic 194; full order 279,840; core under symbolic profile 67,541 pass; `evidence/runs/maude-runs.json` |
| API coverage | 181 names occur directly in captured assertions; 12 extra format-query assertions pass in Julia and Maude; `inventory/operations.tsv` |
| Provenance | 122 pinned inputs, 163 dispositions, 1,010 rule/instance mappings, 193 public names; `evidence/runs/audit.txt` |
| Generation and capture | Julia generator `--check` and optional source capture `--check` pass |
| Examples | Three core and five symbolic checks pass |
| Source cleanup | Eight revised load-only scripts pass; YAML/JSON realization check passes; `evidence/runs/source-cleanup.json` |
| Harness and hygiene | Nine source-tool and nine YAML-tool regression tests pass; no package ambiguities; structured records, links and diff whitespace checks pass |
| Performance | Warmed codec/projection/FMA/block-reduction timings and allocations recorded; `evidence/runs/benchmarks.toml` |

The final package test runs from `/tmp/p3109-standalone-final` with no sibling
Maude tree. Its source/test bytes match the delivered files. The case report's
implementation, input-manifest and dependency-manifest hashes match delivery.

## Remaining obligations

No conversion action remains unfinished. Stable Julia 1.13 validation is a
release follow-up: current evidence uses the release candidate. Concrete external
codecs, certified irrational projection and universal proof claims remain open
as documented in `evidence/obligations.tsv`. Full source Lean compilation was
not established. The historical source inventory discrepancy
`BASELINE-PLAN-HASH: Source hash changed: planmaude.md` remains recorded; the
historical source manifest was not rewritten. These limits are not hidden passes.

Maintain the manifests, generated-file checks and affected semantic tests when
changing the implementation. Actions A00–A17 and their evidence are recorded in
`evidence/actions.tsv`.

## Progress log

1. Planning review: simplified module/file organization, explicit package
   selection criteria, source-versus-Julia invalid-input boundary, and RC
   validation policy. No scope reduction or proof claims introduced.
2. Core implementation: shared exact carrier and arithmetic formulas written.
   Source baseline is clean except the named historical hash discrepancy.
   Package workspace created; JSON.jl selected for tooling simplification.
3. Shared operations and symbolic syntax implemented. Runtime archive SHA-256:
   `a66e5b87876cc1316f170014315b22e3b717dd952c74a23634bda629ad2c2b68`.
   Next: conformance data, inventory-backed API and full source fixture adapter.
4. Conformance records/algorithms, contract interfaces and all 193 source API
   adapters written. Generator runs successfully. Captured 67,541 core, 194
   symbolic and 279,840 full-order source assertions with hashes and unique IDs.
   JSON.jl 1.7.1 and CodecZlib handle tooling data; first fixture comparison runs.
   Initial generator syntax error was corrected before successful generation.
5. First full fixture comparison: codecs 2,660; projection 11,016; scalars
   33,760; ordering 6,112; blocks 140; conformance 13,748; symbolic 194 all pass.
   Domains passed 38/40; added explicit external-next rejection for the two
   failures. Next: rerun domains, exhaustive ordering, independent boundary
   and interface review, provenance/tooling and documentation.
6. Exhaustive ordering complete; ambiguity check returns no ambiguities.
   Review outside supplied fixtures found external classification must remain
   unresolved. Added residual propagation, symbolic domain protection and an
   explicit backend binding interface. Full rerun follows new interface tests.

7. Captured 347,584 source assertions including nine standalone examples.
   Four legacy standalone assertions use stale bare-rational syntax; their
   explicit `fin` adaptations are recorded by the capture script. All 873
   independent interface tests pass. Workspace dependency resolution succeeds;
   JuliaFormatter is selected to keep generated and handwritten code consistent.

8. User correction: omit the four stale standalone assertions entirely.
   Removed all four adaptation rules. Retain only the five unaffected standalone
   assertions; expected final fixture count is 347,580. Regeneration and final
   validation are underway.

9. Full package tests pass: 347,580 source assertions and 881 additional
   interface checks on Julia 1.13.0-rc4. User then authorized removal of stale
   source assertions: removed four in each Maude tree, corrected their suite
   counts to zero, and refreshed corresponding YAML/JSON records and manifests.
   Updated conversion input hashes; source-cleanup validation follows.

10. Provenance audit passes: 122 source inputs, 163 dispositions, 1,010
    rule/instance mappings and 193 public operations. Source cleanup passes
    all eight load-only scripts; YAML/JSON check and fixture recapture check pass.
    Added seven fixture-corruption tests (888 additional checks then passed).
    Final review replaced repeated random-sequence lookup with a single paired
    traversal, preserved unresolved infinite-scale normalization, and made the
    backend next-value rejection consistent. Two regression checks added.
    Rerunning affected validation and refreshing reports/benchmarks.

11. Final coverage review maps all 193 names to concrete checks: 181 appear
    directly in the captured corpus; twelve format-query assertions were added
    and independently confirmed by fresh Maude reductions. Expected additional
    interface checks: 902. Examples pass (three core, five symbolic), source and
    YAML test harnesses each pass nine regressions, and deterministic generation
    passes. Final package validation now runs in an isolated copy under /tmp;
    this confirms no dependency on sibling sources or excluded repository code.

12. Final isolated package run passes all 347,580 corpus assertions and 902
    additional checks. Delivered source/test files match the isolated copy;
    detailed case-report hashes match current implementation and manifests.
    Completed action/evidence records and final documentation review. Conversion
    complete; stable-release, source-history, backend and proof limits remain
    explicitly recorded above.
