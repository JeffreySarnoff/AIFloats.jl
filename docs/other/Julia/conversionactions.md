# Maude to Julia conversion: governing actions

Status: governing record for the implemented conversion. Action states are in
[evidence/actions.tsv](evidence/actions.tsv); refinements are in [improvedconversion.md](improvedconversion.md).
Read [conversionplan.md](conversionplan.md) before further changes. Action
IDs and rules in this document are stable references for conversion reviews.

## 1. Scope and working rules

**MUST** denotes an acceptance requirement. **SHOULD** denotes the default;
departures require a concrete reason and evidence in the change record.
These rules guide implementation within the user's authorized scope. They
do not create additional permission requirements for routine reversible work.
User instructions and applicable `AGENTS.md` take precedence.

- MUST write conversion outputs under `docs/other/Julia/`, including its own
  `src/` and `test/`. Preserve the Maude input tree and unrelated user changes.
  The existing Julia implementation, its tests, and its related documentation
  MUST NOT be used as design references, reusable code, or validation oracles.
  Do not follow Maude documentation links into that excluded material.
- Other Julia packages and their documentation are explicitly permitted,
  including runtime dependencies. Select suitable packages within the
  conversion scope without requesting permission again for ordinary dependency
  choices. The exclusion above concerns the existing repository implementation.
- SHOULD use suitable package APIs to simplify the resulting Julia code.
  Before implementing substantial custom machinery, assess available packages;
  prefer an existing interface when it reduces total complexity, including
  adapters, while preserving source behavior. Dependency count alone is not
  a reason to reimplement a well-suited package capability.
- MUST identify the exact input snapshot and actual Julia executable. A
  successful run on Julia 1.12 is not acceptance evidence for Julia 1.13.
- MUST preserve valid source semantics and explicitly record interface
  adaptations. No silent numerical corrections, missing-operation stubs
  presented as implementations, or skipped residual cases.
- MUST preserve proof status. A test, a declaration, a backend interface, a
  type annotation, and a historical proof log are different kinds of evidence.
- SHOULD keep changes bounded by a coherent semantic family and its tests.
  Update API documentation with each public behavior change.

## 2. Required records

Maintain these records as the conversion changes. Prefer
TOML for Julia-owned structured records, TSV for reviewable tables, and JSON
for interoperable fixtures. Paths are relative to this directory.

| Record | Required contents |
| --- | --- |
| `inventory/inputs.toml` | Repository commit plus relevant working-tree state; every input path and SHA-256; guide title/path/hash; current versus recorded historical hashes; Maude/Julia/Python tool identities when used. Commit ID alone is insufficient for dirty inputs. |
| `inventory/files.tsv` | Source path, category, disposition (`ported`, `adapted`, `retained_evidence`, `excluded_generated`), target/reference, reason, action ID, status. Planned disposition and completed status are separate. |
| `inventory/operations.tsv` | Primary/wrapper name, profile, source parameter and operand order, result kind, target qualified callable/signature, public/export decision, source clause, test IDs, status. |
| `inventory/rules.tsv` | Module plus equation/membership/contract ID, source clause/page where supplied, target function or retained obligation, relevant guards/priority, tests/evidence. Include generated instance labels and dependencies on native Maude operations. |
| `inventory/cases.tsv` | Source case ID, profile, translated case ID, expected outcome category, oracle ancestry, source location, suite and disposition. |
| `inventory/dependencies.toml` | Selected Julia packages, purpose and environment, custom responsibilities/boilerplate replaced, adapter complexity and selection rationale, version/compat bounds, primary documentation, interfaces used, semantic adapter tests, and any shared implementation/oracle ancestry. |
| `evidence/actions.tsv` | Action ID, state, prerequisites, inputs, changed files, tests, review reference, blocker or exception, next step. |
| `evidence/deviations.md` | Named discrepancy/adaptation, source behavior, Julia behavior, rationale, affected IDs, resolution and residual risk. |
| `evidence/obligations.tsv` | Original proof/contract ID, claim and scope, original evidence/status, Julia law check if any, remaining obligation and disposition. |
| `evidence/runs/` | Small structured run summaries with command/cwd, runtime/build, dependency manifest hash, source/output hashes, case counts, failures/skips, seed or explicit random inputs, exit code and logs/artifact references. |
| `evidence/reviews.md` | Semantic and idiom review findings, corrections, evidence and decisions. |

Use cryptographic SHA-256 over bytes for durable identity, not Julia `hash`.
Do not include secrets, absolute transient paths as the sole artifact locator,
or enormous process logs in source control. Keep temporary logs outside the
package; retain durable summaries and retrievable failure artifacts. Runtime
package code must not create these records automatically during import.

States are `pending`, `in_progress`, `implemented`, `verified`, `blocked`.
`implemented` means code exists; `verified` requires all applicable gates and
review evidence. A blocked action records a specific missing prerequisite
and next step; independent actions may continue. A phase exits only when its
required actions are verified. An explicit retained-evidence disposition may
be verified while the underlying mathematical obligation remains open.

## 3. Ordered action register

All actions below initially have state `pending`.

| ID | Phase/dependencies | Required action and completion evidence |
| --- | --- | --- |
| A00 | P0 | Read applicable instructions, plan and the actual `IdiomaticJulia.md`; record guide identity, working-tree baseline, source boundary and target-version assumption. |
| A01 | P0; A00 | Enumerate all source content, 89 primary operations, 52 block plus 52 scaled names, rules, native dependencies and evidence. Reconcile every file with a disposition; exclude generated build products explicitly. |
| A02 | P0; A01 | Run read-only Maude baseline checks. Preserve the existing plan-hash failure as finding `BASELINE-PLAN-HASH`; capture current hashes and exact diagnostics. Establish fresh suite counts/case IDs; verify oracle independence using permitted Maude material, independently derived exact cases, or suitable independent Julia packages. Record exclusion of existing repository Julia code/tests/documentation. |
| A03 | P1; A02 | Select an actual Julia 1.13 executable without changing global defaults; record build/prerelease status. Create P3109Reference package, test workspace, compat bounds and pinned environment. Evaluate useful Julia dependencies, record selections and verify their interfaces/compatibility; extend the record as later phases need packages. Verify clean import/test discovery. |
| A04 | P1; A03 | Define exact values, validated format/policy representations, public validity predicates, native-vs-symbolic decisions, exception/residual protocol and API map. Test invariants including invalid raw arguments and large exact integers. |
| A05 | P1; A04 | Establish structured fixture conversion and normalized result transport. Preserve IDs, exact rational/code payloads and source assertions. Test the comparator with deliberately missing, duplicate, incorrect and residual outcomes. |
| A06 | P2; A05 | Port datum membership, codecs, format metadata/names and bound queries. Pass exact independent four-bit/eight-bit tables, reserved-code and nonrepresentable-value tests. |
| A07 | P2; A06 | Port rounding, saturation and projection. Pass all nine-by-three policy families, P=1 parity, directed overflow, N=0 and small exhaustive random-input tests. Verify guard priority and exact large arithmetic. |
| A08 | P2; A07 | Port predicates, rank/order and next-value operations; check mathematical versus structural equality and NaN successor precedence. Pass source full ordering/adjacency scope. |
| A09 | P3; A08 | Port exact arithmetic/extrema and shared scalar pipelines; independently verify FMA/FAA and operation-specific exceptional rows. Implement core adapters with one final projection and correct operand order. |
| A10 | P4; A09 | Port block/scaled representation, normalization, wrappers, conversion, reductions and dot products. Check supplied/computed scales, random sequence alignment, singleton behavior, axes/dimensions and aliasing. |
| A11 | P5; A10 | Port symbolic syntax, membership knowledge, exact reductions, comparison decisions and scalar/block/scaled paths. Match every symbolic fixture and residual contract; ensure combined loading does not overwrite core methods. |
| A12 | P5; A11 | Port external and real interface declarations, metadata and unsupported outcomes; map every law and unimplemented view to obligations. Test missing capabilities without supplying invented backends. |
| A13 | P6; A12 | Port conformance identity/requirement/declaration/partition/κ algorithms and inventory-derived arity tables. Verify finite coverage counts and evidence-category distinctions. |
| A14 | P6; A13 | Complete proof/Lean/native-axiom accounting and source deviations. Preserve the exact scope of historical results, unverified modules and pending universal claims. |
| A15 | P7; A14 | Finish Julia CLIs, deterministic wrapper/fixture generation, examples and documentation. Run source/JULIA traceability checks and all parity suites; verify every required source case/name is covered. |
| A16 | P7; A15 | Perform semantic and idiom reviews, package hygiene and targeted inference/benchmark checks. Correct findings and rerun affected checks; record measured optimization tradeoffs. |
| A17 | P7; A16 | Validate in a clean process on pinned Julia 1.13, audit all manifests and source integrity, publish the final evidence summary and remaining mathematical/backend obligations. Mark complete only when all required gates pass. |

These dependencies define acceptance order. Supporting fixtures, documentation
and inventory tooling should evolve alongside their semantic action; do not
defer test creation until A15. Splitting an action is allowed if child IDs,
coverage and completion conditions remain traceable.

## 4. Per-change execution loop

1. Select an action with satisfied prerequisites. Read its source equations,
   memberships, callers, fixtures and documented deviations. Record the exact
   signature, preconditions, priority rules and expected result categories.
2. Write the target interface and semantic cases before implementing a kernel.
   Check the operation map and guide sections relevant to this design. Assess
   whether a package can simplify the implementation; compare the package API
   plus necessary adapters with the proposed custom code. Identify which
   expected results come from an independent oracle.
3. Implement ordinary Julia functions with bounded responsibilities. Add tests
   for changed behavior, including at least the meaningful boundary/invalid/
   residual cases for that family. Update docstrings and mappings together.
4. Run the focused Julia tests and matching Maude cases with identical exact
   inputs. Compare normalized results; retain the smallest failing example.
5. Review both semantics and idiom using sections 5 and 6 below. Correct
   findings, then run the affected dependent suites. Broaden to the full
   acceptance set at phase exits, not repeatedly without a reason.
6. Record commands, counts, hashes, results and review disposition. Advance to
   `verified` only when evidence supports the claim; record incomplete work
   plainly and continue independent authorized actions where possible.

## 5. Mandatory semantic rules

| Rule | Requirement and rejection condition |
| --- | --- |
| S01 — exact arithmetic | Finite reference values use `Rational{BigInt}` as the baseline; exact package representations require explicit losslessly tested adapters. Form large operands before arithmetic, audit negative division/remainder semantics, and reject intermediate Float64/BigFloat approximation in the exact core. |
| S02 — representation | Preserve single-zero/single-NaN semantics and source format/code domains. Do not use an IEEE host float as the representation of all source values. |
| S03 — domain guards | Public validation precedes execution. Invalid application, specified NaN, unresolved semantics, and absent backend are distinct observable outcomes. Broad exception catching cannot turn implementation faults into expected residuals. |
| S04 — projection | Decode operands, evaluate the exact kernel/composition, project once. Reject intermediate rounded operations in FMA, FAA, block reductions and dot products. |
| S05 — case priority | Preserve exceptional-value and ordered saturation behavior. A translated dispatch set must be unambiguous and have tests for overlapping cases; source textual order alone does not prescribe Julia dispatch. |
| S06 — stochastic inputs | Random integers/sequences are explicit, validated, and reused identically for corresponding source/target calls. No hidden draws, global RNG dependence or float-based probability approximation. |
| S07 — blocks | Preserve positive block size, sequence lengths/order, positional random pairing, scale semantics and per-operation normalization. No silent broadcasting across mismatched blocks or change to reduction order without equivalence evidence. |
| S08 — symbolic knowledge | AST existence is not domain membership. Unknown guards remain unknown. Different syntax is not mathematical inequality. Residual projection must preserve its expression and reason. |
| S09 — source API | Preserve source names and argument/result contracts through SpecAPI, including y-before-x ArcTan2 and flattened blocks; record all ergonomic adaptations explicitly. |
| S10 — conformance | Keep observed κ, declared bounds, finite-universe coverage and whole-domain proof separate. Never promote an evidence label into a verified certificate. |
| S11 — proof boundary | Link and catalogue Lean/Maude proofs and axioms. Julia tests do not replace CRC/SCC conclusions or establish universal theory/model correctness. |
| S12 — evidence integrity | Missing/duplicate cases, diagnostics, timeouts, truncated output, unexpected residuals and unsupported syntax fail validation. No regenerated expected values from the implementation under test without a separately recorded oracle basis. |

Known source decisions MUST remain regression cases: exclusion of K=2;
the P=1 tie-parity rule; NaN-first next-value rows; infinite-scale normalization;
the §5.5.3 NOTE 2 finite-scale/infinite-element discrepancy; and the warning
that equal projected enclosure endpoints alone cannot certify an interval
containing incompatible results.

## 6. Idiomatic Julia review rules

Use the local guide sections indicated below. These are conversion review
criteria, with concrete exceptions recorded rather than blanket stylistic bans.

| Rule | Required review question | Guide |
| --- | --- | --- |
| J01 — generic behavior | Does each argument restriction express dispatch or a real contract? Can an appropriate new type use the method without source edits? | §§5–6, 62 |
| J02 — stored representation | Are hot fields concrete or parametrically concrete, including callables/containers? Is deliberate AST heterogeneity contained? | §7, 19–20, 63 |
| J03 — bounded specialization | Are widths, lengths and random samples ordinary data? Any `Val`, value parameter, generated function or forced specialization needs measured benefit and compilation-cost evidence. | §§21–23 |
| J04 — interfaces | Are clients using documented query/iteration/array methods rather than another component's fields? Are Base methods extended only where their contracts fit and owned types participate? | §§8–11, 26 |
| J05 — numerical intent | Are `zero`, `one`, `oneunit`, `similar` and conversions chosen to preserve the actual algebra? Do constructors, `convert`, promotion and explicit projection have distinct roles? | §§12–14, 64 |
| J06 — mutation | Do argument-mutating APIs end in `!`, put destinations appropriately, validate dimensions before writes, and document aliasing/partial-write behavior? Are allocating wrappers supplied when useful? | §§15–17, 27 |
| J07 — indexing | Are iteration, `eachindex` and `axes` used correctly? Is source position separated from storage index? Are views/nonstandard axes tested wherever supported? | §§9–11, 65 |
| J08 — API boundary | Are names lowercase for functions and UpperCamelCase for types/modules? Are `public`, exports, qualified SpecAPI names and explicit imports deliberate? Are public docstrings complete? | §§24–28, 33 |
| J09 — packages | Have suitable package APIs replaced unnecessary custom machinery? Is the total solution clearer after accounting for adapters, with no redundant wrappers? Are dependencies purposeful, compatible with Julia 1.13, explicitly recorded and placed in the correct environment? Are package defaults checked against source semantics, tests in a workspace, optional integrations in native extensions, and installed source free of writes? | §§29–32, 67 |
| J10 — control flow | Are expected decisions predicates/result values rather than broad try/catch? Are specific exceptions reserved for invalid calls? Do functions suffice instead of macros or `eval`? | §§34–36 |
| J11 — measured performance | Is hot work in functions, dynamic setup behind a function boundary, and optimization supported by warmed measurements plus latency/allocation information? | §§18–23, 66 |
| J12 — concurrency if added | Is scratch state owned by a task/chunk, shared mutation synchronized, and no state indexed by an assumed stable `threadid()`? Keep stochastic input ordering deterministic. | §§37–39, 68 |

Use four-space indentation and signature-led docstrings from the specified
idiom guide; apply repository instructions without consulting the excluded
Julia implementation or its documentation. Generic loops are idiomatic; rewriting
them as broadcast is not an acceptance goal. New 1.13 conveniences are optional
and must be verified against the actual runtime before use. Macros, custom
broadcast styles, `@inbounds`, `@simd`, `@fastmath`, atomics and generated
specializations are not baseline requirements; `@fastmath` is unsuitable for
this exact/exception-sensitive reference path.

## 7. Generation and fixture governance

The operation inventory controls wrapper membership and source signatures;
shared Julia kernels control behavior. Generate only repetitive thin adapters,
tables or fixture data. Keep arithmetic, guard precedence, domain rules and
symbolic reductions handwritten and reviewable.

Generators MUST have a non-writing `--check` mode that computes outputs in
memory or a temporary directory, compares bytes, and exits nonzero on drift.
They MUST use deterministic ordering and source/inventory hashes. Generation
is an explicit developer action, never an import/build side effect. A generated
file's header identifies its generator and inputs; edit the generator or input
instead of hand-editing generated regions. `--check` must not rewrite its
baseline to make itself pass.

For each source assertion string, preserve the original text for traceability
and provide a structured Julia case. A parser must recognize the exact needed
grammar, validate full input consumption and reject unknown constructs.
Malformed fixture input is a tooling error, not a symbolic residual. Integer
and rational transport must remain exact even beyond JSON consumer safe-integer
ranges. Maintain source-to-target case IDs when splitting one assertion into
multiple Julia checks.

## 8. Commands and acceptance gates

All commands below are run from the repository root unless specified. Existing
source commands can run now; Julia commands and paths are templates for after
the package is implemented. Do not report these templates as executed checks.

Baseline tools (read-only; `-B` avoids Python bytecode writes):

```sh
python3 -B docs/other/Maude/tools/check-inventory.py
python3 -B docs/other/Maude/tools/generate-wrappers.py --check
python3 -B docs/other/Maude/tools/check-loads.py
python3 -B -m unittest discover -s docs/other/Maude/tests -p 'test_*.py'
python3 -B docs/other/Maude/tools/run-tests.py --suite core
python3 -B docs/other/Maude/tools/run-tests.py --suite symbolic
python3 -B docs/other/Maude/tools/run-tests.py --suite core --profile symbolic
python3 -B docs/other/Maude/tools/run-tests.py --suite order-full
```

The first command currently fails solely with the recorded plan-hash mismatch.
Keep its raw failure visible. A conversion baseline may classify that exact
known diagnostic separately after confirming the current bytes; all additional
diagnostics fail the baseline. Never use blanket `|| true`, suppress all stderr,
or edit the historical manifest merely to manufacture a passing result.

After provisioning/selecting the intended runtime, set `JULIA_113` to the
absolute executable path and record it. This is a task-specific variable,
not a change to Juliaup defaults. Example commands:

```sh
"$JULIA_113" --startup-file=no -e 'using InteractiveUtils: versioninfo; versioninfo(); @assert VERSION.major == 1 && VERSION.minor == 13'
"$JULIA_113" --startup-file=no --project=docs/other/Julia -e 'using Pkg; Pkg.instantiate()'
"$JULIA_113" --startup-file=no --project=docs/other/Julia -e 'using P3109Reference'
"$JULIA_113" --startup-file=no --project=docs/other/Julia -e 'using Pkg; Pkg.test()'
```

P1 must verify these commands discover workspace test dependencies on the
selected 1.13 build. Document any required workspace instantiation option
based on that runtime's Pkg documentation. Use a writable task-specific depot
if necessary; do not mutate user startup files. Record prerelease status
separately, since the major/minor assertion alone does not establish stability.

At A15, document concrete commands for the new Julia inventory checker,
generator `--check`, case exporter, differential runner and example runner.
Their names are implementation choices; their required exit behavior is not.
Every runner must propagate failures, enforce bounded subprocess execution,
validate completion and expected case sets, and retain failure evidence.

Acceptance gates:

- **G0 — provenance:** every semantic input/disposition is recorded, baseline
  discrepancies classified narrowly, no source mutation concealed.
- **G1 — execution:** clean package import, tests, examples and public adapters
  run on the recorded Julia 1.13 runtime; no load-time generation or method
  overwrite warnings; dependency/manifest identity recorded.
- **G2 — parity:** all applicable source suites/cases match exact values or
  documented invalid/residual outcomes; independent oracle checks also pass.
- **G3 — coverage:** all 89 primary and 104 generated operation names are
  mapped; every in-scope rule/native dependency/contract and source fixture has
  a target or justified evidence disposition; generated outputs are current.
- **G4 — idiom:** semantic and Julia design reviews have no unresolved required
  findings; interface/ownership tests and targeted package QA pass. Tool
  incompatibility requires an equivalent concrete check, not a silent skip.
- **G5 — claims:** final documentation distinguishes implemented core behavior,
  symbolic partiality, absent backends, finite tests and open proofs; no broader
  conformance assertion than the evidence supports.

Run tests against the standalone conversion project. The existing Julia
implementation's test suite is excluded and cannot serve as G1/G2 evidence.

## 9. Findings, exceptions, and final handoff

For a semantic mismatch, capture the smallest exact input and both outcomes;
identify source guard/label and oracle ancestry; decide whether it is a port
defect, fixture defect, baseline defect or deliberate interface adaptation.
Fix port defects before accepting the action. Do not change an oracle simply
because the new code disagrees with it.

A source ambiguity or desired semantic improvement gets a named deviation,
the source-compatible behavior, a proposed alternative and its tests. Preserve
source-compatible behavior for this conversion where it is determined. Ask
for missing direction only when competing interpretations materially prevent
faithful implementation; continue unaffected work. Routine design refinements
within the plan need a recorded rationale, not another permission request.

Before A17 is verified, confirm every action's evidence, required test status,
source/output hash consistency and documented public API. The final handoff
MUST contain exact commands and environment identity, case counts with scope,
all remaining failures or skipped requirements, expected residual/unsupported
capabilities, and unresolved mathematical obligations. A blocked required
runtime check or missing executable operation means the conversion is still
incomplete, even when most files have been translated.
