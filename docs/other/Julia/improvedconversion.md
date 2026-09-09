# Improved conversion: implementation design and review

Reviewed 2026-09-08. This document refines [conversionplan.md](conversionplan.md)
and [conversionactions.md](conversionactions.md) for execution. Progress and
actual validation are recorded in [checkpoint.md](checkpoint.md).

## Outcome and scope

Implement `P3109Reference` in this directory from `../Maude/`, ignoring the
existing repository Julia implementation, its tests and related documentation.
Use other Julia packages where they simplify the complete implementation.
Preserve exact rational behavior, all 193 inventory-derived operation names,
explicit stochastic inputs, symbolic residuals and external contract boundaries.
The `/docs/other/Julia/` paths in the request are interpreted relative to this
repository, consistently with the earlier conversion documents.

## Priorities and implementation choices

1. **Correctness and clarity:** use named generic functions and small value
   types. Keep exceptional cases visible; distinguish invalid calls from NaN,
   unknown predicates and missing backends. Do not mimic Maude inheritance.
2. **Shared approaches:** one decode/evaluate/project scalar path and one
   block traversal for unary, binary and ternary functions. Generate only thin
   named adapters and inventory tables, never semantic arithmetic bodies.
3. **Performance:** arbitrary-precision rationals are the exact baseline.
   Compute integer log2 from bit lengths and a final comparison instead of
   repeated scaling; use arithmetic codec/rank formulas rather than enumerating
   formats. Validate once at public boundaries; reuse decoded values within
   operations and iterate without cons-list allocation. Measure before adding
   caches, mutation, specialization or parallelism.
4. **Conciseness:** use Base rational arithmetic, integer square root, tuples,
   vectors, iteration and finite-set operations. Use JSON.jl for structured
   inventory/fixture tooling rather than a new JSON parser. Source assertion
   parsing remains a bounded test-tool responsibility, not a runtime interpreter.
5. **Package fit:** general symbolic algebra can apply identities that are
   unsound for these domain guards and NaN rules. Use a small owned residual
   representation and only the source's supported reductions. Revisit package
   adoption if it removes more code than its semantic adapters introduce.

JSON.jl's documented parsing/writing interface is the basis for the tooling
choice ([primary source](https://github.com/JuliaIO/JSON.jl)). Keep it in the
tool/test environment unless runtime use becomes necessary. Record resolved
versions and compatibility. Runtime arithmetic does not need a third-party
number package to improve upon Base's exact `Rational{BigInt}` operations.

## Reviewed corrections to the earlier plan

| Issue | Execution refinement |
| --- | --- |
| A stable Julia 1.13 executable was assumed as an eventual gate. | The official downloads page currently lists 1.13.0-rc4. Validate on that available 1.13 runtime if obtainable; label results as prerelease evidence and retain a stable-release rerun obligation. A missing runtime must not stop independent implementation work. |
| Strict action dependencies could block all development on a historical manifest discrepancy. | Pin current source bytes, retain `BASELINE-PLAN-HASH`, and proceed when fresh semantic checks pass. Never alter the historical source manifest. |
| A module/subdirectory per source concern would add navigation overhead. | Group cohesive behavior into a modest set of Julia files; retain separate qualified SpecAPI, Symbolic and Contracts interfaces where they establish useful boundaries. Traceability permits many-to-one file mapping. |
| Constructor validation conflicts with tests that inspect invalid raw Maude constructors. | Public Julia constructors validate; the test adapter retains raw source syntax long enough to test validity or classify invalid applications. |
| Generic array support can obscure positional block semantics. | Define block inputs as ordered sequences, explicitly align operands/random values by position, and keep storage indices local to iteration. Do not infer broadcasting or array ownership promises. |
| Wrapper counts alone could falsely imply parity. | Check names/signatures separately from behavioral cases, including all source fixture IDs and residual expectations. Mark implemented and verified separately. |
| Shared code can become its own oracle. | Use source Maude reductions plus the existing independent Python exact calculations; no comparison with excluded repository Julia code. |
| Source proof material is not executable Julia. | Retain file-level provenance and claim-level obligations. Port finite law checks where meaningful; never mark universal claims proved from tests. |

The runtime observation is based on the
[official downloads page](https://julialang.org/downloads/manual-downloads/).
The RC does not become a stable release because compatibility bounds accept it.

## Execution sequence

Follow actions A00–A17, with implementation and tests developed together:

- Establish source hashes, file/operation/rule maps, clean baseline and runtime.
- Build exact values, formats, policies, codecs, projection, predicates/order.
- Add shared scalar/block kernels and all inventory-derived adapters.
- Add source-specific symbolic reductions, unknown decisions and contracts.
- Implement finite conformance accounting and preserve proof obligations.
- Convert source fixtures, validate differential results, finish Julia tooling,
  examples, package checks and performance measurements.

Each checkpoint update must state what changed, what actually ran, any failure,
and the next work. Update at every meaningful implementation/validation boundary
and before any interruption. Never describe unrun checks as passing.

## Correctness and completeness review

The design covers all 31 semantic source files, four profiles, the 89 primary
operations and 104 block/scaled names through the earlier plan's inventory.
It retains exact single-projection arithmetic, P=1 parity, all stochastic and
saturation families, source sequence order, exceptional precedence, symbolic
membership restrictions and unsupported external codecs. The tests must cover
each of these independently; this review is not implementation evidence.

Completion requires complete file and operation accounting, documented API,
passing exact and residual cases, deterministic generation and an honest
runtime/proof status. Remaining backend implementations and universal proofs
are preserved limitations; missing core behavior or unexplained mismatches
are unfinished conversion work. The checkpoint is the authoritative account
of which gates have actually been met.

## Final review refinements

- Store per-case IDs and exact assertions once, in compressed JSONL; maintain a
  suite index and hashes rather than duplicating hundreds of thousands of rows.
- User-directed source cleanup removes four stale standalone assertions from
  both Maude trees and their supporting YAML/JSON copies. They are not adapted
  or ported. Pin the resulting source bytes and retain five current assertions.
- Keep the Python oracle capture as an optional migration adapter; normal Julia
  tests, generation and execution require no Python or Maude process.
- Use JuliaFormatter for deterministic generated layout, CodecZlib for compact
  fixtures and BenchmarkTools for measured latency/allocation evidence.
- Confirm explicit external binding, missing-backend classification, malformed
  fixture rejection and borrowed-random validation with independent tests.

The completed implementation is organized as documented in `api.md`. Review
findings and resolutions are in `evidence/reviews.md`; remaining formal/backend
and stable-release obligations remain explicit. The original action IDs still
apply, with these recorded scope and artifact-layout refinements.
