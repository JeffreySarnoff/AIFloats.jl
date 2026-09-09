# Maude to idiomatic Julia 1.13: conversion plan

Status: original plan implemented with the refinements in [improvedconversion.md](improvedconversion.md).
Current validation and remaining obligations: [checkpoint.md](checkpoint.md). Reviewed 2026-09-08.
Execution is governed by [conversionactions.md](conversionactions.md).

## 1. Objective and authority

Convert the semantics and supporting material in `docs/other/Maude/` into a
standalone, executable Julia reference package under `docs/other/Julia/`,
with suitable Julia package dependencies where useful.
Interpret the requested “v1./13” as **Julia 1.13**. Preserve exact results,
domain restrictions, symbolic partiality, operation signatures through an
adapter, and the distinction between executable checks and mathematical proofs.
Organize the implementation around Julia functions and interfaces rather than
reproducing the Maude module graph or Lean term encoding mechanically.

The requested idiom guide was found at
[`IdiomaticJulia.md`](</home/jas/Documents/Julia/Julia Praxis/IdiomaticJulia.md>),
not at the supplied spelling `Idomatic-Julia.md`. Its title is *Idiomatic Julia
for Julia v1.13+*, research cut 2026-09-08; the reviewed file's SHA-256 is
`e0965e09354e365a0d90d508d95584236c2bbf7d457d6cbfbf001771fff9d92b`.
Section references below refer to that document. Implementation must record
its source identity so another contributor can identify the same guidance
without needing this machine's absolute path.

Apply authority in this order:

1. The user's instructions and applicable repository `AGENTS.md`.
2. The actual Maude sources, inventories, fixtures, and documented deviations
   as the behavior being converted. Preserve contradictions as findings.
3. The idiom guide for Julia design; official documentation for exact language
   and package-manager behavior on the selected runtime. Selected third-party
   Julia packages and their documentation may supply implementation machinery
   and independently validated reference calculations.

**Source exclusion:** per the user's refinement, ignore the existing Julia
implementation and all documentation related to it. Do not consult them for
design, naming, algorithms, expected results, reuse, or differential validation.
This exclusion concerns the existing repository implementation and its related
documentation; it does not exclude other Julia packages or their documentation.
The applicable repository instructions still govern the work; choose Julia
conventions from the specified idiom guide and official documentation.

Historical source restrictions inside Maude reports describe earlier work;
they do not impose a new approval workflow for this conversion. If a source
conflicts with the IEEE draft, record the conflict and proposed disposition;
do not silently repair the source semantics while calling the result a port.

## 2. Inspected baseline and scope

The source tree has **122 tracked files**, including **49 Maude files**.
Its executable library comprises 23 `lib/`, five `symbolic/`, and three
`contracts/` files. Four loaders define core, symbolic, contracts, and combined
profiles. Build products also exist under `Lean/.lake/`; these are not source
conversion inputs.

[`operations.json`](../Maude/inventory/operations.json) contains **89 primary
operations: 59 core and 30 symbolic**. Of these, **52** request both block and
scaled wrappers, giving **193 inventory-derived public operation names**
before counting lower-level helpers. The inventory's SHA-256 at review is
`ebb8032d469a051dcee21389ea8461ad8f03b32900a9e94f426b4db64a5adc77`.
These counts are baseline checks, not substitutes for enumerating the names,
signatures, equations, memberships, and contract obligations.

Observed limitations affecting execution:

- `julia --version` reports **1.12.7**. No Julia 1.13 execution was verified
  during planning. `juliaup status` could not create its lockfile in the
  read-only depot. Select and verify an actual 1.13 executable before accepting
  implementation tests; do not change the user's default Julia channel.
- `python3 -B docs/other/Maude/tools/check-inventory.py` exits 1 with
  `Source hash changed: planmaude.md`. Preserve the original manifest and
  record current bytes and the discrepancy in new conversion evidence.
- The source README/coverage reports an earlier 55,476-check core run, while
  `shortening.md` reports 67,541 after wrapper refactoring. Neither count was
  rerun here. Establish fresh counts and case IDs for the pinned snapshot.
- External codecs and the full real-number contract have no implementation
  views. Symbolic evaluation intentionally leaves some calls residual.
- Lean foundational compilation is recorded as passing; full compilation
  remains unverified. CRC/SCC evidence covers specific slices, not all code.

Every tracked source file must receive a disposition in the conversion
manifest. Newly discovered, non-generated source files must also be reviewed;
do not ignore them solely because they are untracked.

| Material | Conversion disposition |
| --- | --- |
| `lib/`, `symbolic/`, `contracts/`, loaders | Implement behavior or explicit partial interfaces in Julia; map every declaration and labelled rule. |
| `tests/*.maude`, `tests/vectors/*.json`, examples | Translate cases and examples, preserving case IDs, exact inputs, outcomes, and residual assertions. |
| Nine Python tools and two Python test files | Port necessary inventory, generation, fixture, and validation functionality to Julia; retain the Python harness as a pinned migration oracle. Do not require Python or Maude for ordinary package use. |
| `inventory/` | Preserve source identity and create source-to-Julia mappings; keep original artifacts readable from their existing location. |
| `proofs/`, `spec2.lean`, `Lean/` source/configuration | Catalogue and link evidence, axioms, and open obligations. Translate applicable laws to executable checks, explicitly labelled as checks rather than proofs. Do not pretend Lean proof terms become Julia certificates. |
| README, installation, plans, shortening, enhancements, Lean reports | Write Julia usage/architecture/evidence documentation; link historical material and record whether each item was adapted or retained as evidence. |
| `.lake/`, compiled objects, caches, temporary output | Exclude with a recorded reason; never copy these as Julia source or validation evidence. |

A retained-evidence disposition is a completed accounting action, not a claim
that its proof obligation has been discharged. Implementing new external
codecs, a certified real evaluator, or new universal proofs is follow-on work.

## 3. Package boundary and layout

Use the working package name **P3109Reference**, with its own UUID and
`Project.toml`. Keep all new implementation, tests, tools, documentation, and
evidence under this directory. Build an independent exact reference directly
from the Maude material. The existing Julia implementation, its tests, and
its related documentation are excluded inputs. Do not import its modules,
reuse its algorithms, copy its API, or compare results against it. Leave files
outside the conversion directory unchanged.

Initial proposed layout; the refined implementation layout is documented in `api.md`:

```text
Julia/
  conversionplan.md
  conversionactions.md
  Project.toml
  Manifest.toml                 # reproducible conversion workspace
  README.md
  src/
    P3109Reference.jl           # API declarations and ordered includes
    values.jl                  # exact values and special datums
    formats.jl                 # validated metadata and queries
    policies.jl                # rounding/saturation and explicit random inputs
    codec.jl
    projection.jl
    arithmetic.jl
    predicates.jl
    ordering.jl
    scalar.jl                  # generic decoded-operation/project pipeline
    blocks.jl                  # block representation, normalization, traversal
    block_operations.jl
    conformance.jl
    symbolic/                  # explicit Symbolic submodule
      Symbolic.jl
      expressions.jl
      domains.jl
      elementary.jl
      operations.jl
    contracts/                 # explicit Contracts submodule
      Contracts.jl
      real.jl
      external.jl
    spec_api.jl                # qualified SpecAPI compatibility submodule
  test/
    Project.toml
    runtests.jl
    test_*.jl
    support/                   # typed cases and independent oracle adapters
    vectors/                   # exact, normalized fixture data
  tools/                       # Julia inventory/generation/differential CLIs
  examples/
  docs/                        # architecture, API map, semantic differences
  inventory/                   # inputs, files, rules, API map, case coverage
  evidence/                    # reviews, deviations, obligations, run summaries
  benchmark/                   # add a workspace member when measurements begin
  ext/                         # add only for actual optional integrations
```

Start with a workspace containing `test`; add `benchmark` and a documentation
build project only when needed. Use `[compat] julia = "1.13"` as the intended
minimum, with acceptance pinned to a recorded **1.13.x** runtime. This compat
entry also allows later 1.x versions; it does not pin the executable. Record
the exact version, prerelease status, build identity, and dependency manifest.
A prerelease run is provisional evidence, to be rerun on the selected stable
release. Resolve any prerelease compatibility behavior explicitly in P1.
Workspaces and native extensions follow the
[Pkg package guidance](https://pkgdocs.julialang.org/dev/creating-packages/).

**Julia package dependencies are explicitly permitted**, including runtime
dependencies. Use established packages when their documented interfaces fit
the conversion and reduce custom implementation or maintenance. There is no
standard-library-only requirement. Evaluate candidates during the relevant
phase; this plan does not select or install additional packages.

**Prefer package-backed simplification when it makes the resulting Julia code
clearer.** Before writing custom collection helpers, parsers, symbolic machinery,
numeric utilities or tooling, check whether a suitable package already provides
the needed interface. Compare the complete solution, including adapters and
configuration: choose the package when it removes meaningful boilerplate or
algorithmic complexity without obscuring source semantics. Do not retain a
handwritten subsystem solely to minimize dependency count, or add layers of
wrappers around an API that already fits. Record what custom code each selected
package replaces; use a small semantic adapter only where behavior differs.

Record each selected package's purpose, supported interface, chosen version,
Julia 1.13 compatibility, and relevant semantic tests. Check current primary
documentation before adoption. For numerical or symbolic packages, verify
exactness, exceptional-value behavior, domain assumptions and simplification
rules against Maude; a package's defaults do not define the reference semantics.
Retain `Rational{BigInt}` as the baseline exact carrier; alternative exact
package representations may be used behind an explicit, losslessly tested
boundary. Package reuse does not supply a proof of conformance or authorize
silently evaluating expressions that must remain residual.

Place required execution dependencies in `[deps]`; use weak dependencies and
extensions for optional integrations. Keep JSON parsing used only by tools,
BenchmarkTools, Aqua, JET, and array-testing helpers in the appropriate
tool/test/benchmark environment, with verified compatible versions. A package
used by the implementation cannot also be the sole independent oracle for
that same behavior. Loading the package must not invoke Maude, generate files,
install dependencies, or write into source.

## 4. Source-to-Julia implementation map

Paths in the first column are relative to `../Maude/`. File grouping expresses
ownership; it does not prescribe one Julia module per source file.

| Source | Julia destination and responsibility |
| --- | --- |
| `lib/xreal.maude`, `lib/rational-math.maude` | `values.jl`, `arithmetic.jl`: exact rational carrier, special values, guarded rational helpers. |
| `lib/format-core.maude`, `lib/format-queries.maude`, `lib/format-names.maude` | `formats.jl`: constructor invariants, metadata, bounds, naming; query/codec dependencies must remain acyclic where source guards require it. |
| `lib/sequences.maude` | Standard tuples/vectors and iteration; helper adapters only for source indexing and term serialization. |
| `lib/projection-spec.maude` | `policies.jl`: deterministic and stochastic policy objects and validity. |
| `lib/external-signature.maude`, `contracts/external-format.maude`, `contracts/external-bridge.maude` | `contracts/external.jl`: metadata, backend protocol, explicit unimplemented capability results, contract tests. |
| `lib/codec.maude` | `codec.jl`: code validity, exact datum membership, decoding and encoding. |
| `lib/rounding.maude`, `lib/saturation.maude`, `lib/project.maude` | `projection.jl`: ordered round → saturate → encode pipeline. |
| `lib/omega-arithmetic.maude`, `lib/omega-extrema.maude` | `arithmetic.jl`: exact scalar kernels and exceptional-value precedence. |
| `lib/predicates.maude`, `lib/order-next.maude` | `predicates.jl`, `ordering.jl`: mathematical comparisons, classification, ranks and adjacent codes. |
| `lib/scalar-templates.maude`, `lib/scalar-ops.maude` | `scalar.jl`, `spec_api.jl`: three arity pipelines and thin operation wrappers. |
| `lib/block-core.maude`, `lib/block-ops.maude`, `lib/block-templates.maude`, `lib/block-wrappers.maude` | `blocks.jl`, `block_operations.jl`, `spec_api.jl`: shared-scale behavior, block/scaled families, reductions. |
| `lib/conformance.maude` | `conformance.jl`: identities, requirements, declarations, finite partitions, observation κ and declaration κ. |
| `symbolic/real-expressions.maude`, `symbolic/omega-elementary.maude` | `symbolic/expressions.jl`, `domains.jl`, `elementary.jl`: syntax, membership knowledge, exact special reductions and residuals. |
| `symbolic/scalar-ops.maude`, `symbolic/block-ops.maude`, `symbolic/block-wrappers.maude` | `symbolic/operations.jl`: symbolic scalar, scaled and block paths using shared traversal without overwriting core methods. |
| `contracts/real.maude` | `contracts/real.jl`: interface laws and unresolved obligations; no claim to construct all reals. |
| Four `load-*.maude` files | Main entry point plus qualified `Symbolic`, `Contracts`, and `SpecAPI`; independent profile tests and documented availability. |

## 5. Semantic design decisions

### Exact values and representation

Use `Rational{BigInt}` for finite reference arithmetic. Construct powers,
numerators, denominators, and wide code bounds with arbitrary-precision
integers **before** performing operations that can overflow. Never compute
`2^k` in machine `Int` and convert the already-overflowed result afterward.
Match Maude division, quotient/remainder, floor, and parity semantics explicitly
for negative operands. Neither `/` on ordinary integers nor machine floats
are substitutes for exact rational construction.

Define owned immutable types for finite values, NaN, and positive/negative
infinity, with one zero and one NaN datum. A small union or dispatch hierarchy
is appropriate. Do not declare these types subtypes of `AbstractFloat` or
translate Maude `Real` directly to Julia `Real`: their contracts differ.
Support large valid formats through exact arithmetic; distinguish practical
resource exhaustion from an invalid format, rather than silently imposing a
new machine-word limit. Machine-sized lengths and indices require checked
conversion at allocation boundaries.

Use constructor checks for `K > 2`, `P > 0`, signed `P < K`, unsigned `P <= K`,
code ranges, positive block lengths, and stochastic ranges. Keep public
validity predicates able to inspect invalid raw inputs without first needing
to construct a validated object. Only internal code may bypass checks with
documented caller invariants.

### Partiality, errors, and symbolic truth

Distinguish four observations in adapters and evidence:

| Source observation | Julia contract |
| --- | --- |
| Valid reduction to a value/code/Boolean | Exact corresponding result. |
| Specified exceptional result such as NaN | Owned semantic NaN, never an argument-error substitute. |
| Invalid public call left unreduced | Idiomatic entry point throws a documented `ArgumentError`, `DomainError`, `DimensionMismatch`, or `BoundsError`; adapter records an invalid-application outcome. |
| Valid expression, unresolved comparison/projection, or absent backend | Typed residual/undecided/unsupported outcome retaining the operation, inputs and reason; never guessed `false`, NaN, or a float approximation. |

These error mappings are deliberate interface adaptations and require
source-to-target tests. Private guarded helpers need not accept malformed
terms, but their preconditions must be documented and tested through callers.

Represent symbolic syntax independently of knowledge that an expression lies
in a domain. Julia construction of a node must not imply Maude sort `Real`
membership. Use an explicit decision result for symbolic predicates; require
confirmed truth before firing a conditional reduction. Structural equality,
mathematical equality, `isequal`/`hash`, and total sorting are separate contracts.
Do not make Julia `==` return a symbolic expression or call two distinct
expression trees mathematically unequal merely because their syntax differs.

### Dispatch and projection

Use semantic policy types for rounding/saturation families. Keep bit widths,
precisions, block lengths, stochastic bit counts, and random integers as
ordinary values by default. Parametrize fields for concrete storage and
callables; specialize runtime values only after measurements justify it.

Factor unary/binary/ternary operations into shared validation, decode, exact
kernel evaluation, and a **single final projection**. FMA, FAA, reductions,
dot products, and composed elementary special cases must not call rounded
scalar wrappers internally. Preserve source-specific NaN/infinity precedence
and ordered saturation guards. Julia method specificity is not a replacement
for source case priority; overlapping semantic cases need explicit guards
and ambiguity tests.

Stochastic behavior remains a pure function of explicit `(N, R)` or an ordered
random sequence. Enforce `N >= 0` and `0 <= R < 2^N`. No core routine draws from
an RNG or uses global rounding state. An eventual RNG convenience layer is
separate and cannot change reproducibility of the reference API.

### Collections and public API

Use vectors/tuples and standard iteration instead of cons-list recursion.
Treat source sequence index `j = 0` as the first **position**, not necessarily
Julia storage index `1`. Map positions through iteration/`eachindex`; align
random inputs by position. Elementwise mutating kernels require compatible
axes or an explicitly documented positional policy. Use `similar` with the
actual result element type, validate dimensions before mutation, and document
aliasing. Test views and nonstandard axes for APIs that claim to support them.
Do not introduce a custom `AbstractArray` subtype unless its interface is needed.

The ergonomic API uses lowercase function names, owned types, explicit
projection, narrow exports, and `public` for qualified supported names.
`SpecAPI` preserves the inventory's names, arities, parameter-first order,
flattened block operands, result categories, and `ArcTan2(..., y, x)` ordering.
Keep it qualified to avoid collisions with Base and client namespaces. All 193 derived
names must map to an ergonomic function or an explicit symbolic/contract path;
aliases must not duplicate arithmetic. Spec projection is explicit and must
not be hidden in automatic `convert` or promotion. Extend Base only on owned
types where the standard contract genuinely holds.

### Symbolic and external profiles

Use an explicit symbolic entry point or evaluation context so enabling
symbolic behavior does not redefine existing core signatures during loading.
Small semantic node families are useful; an intentionally heterogeneous AST
is acceptable outside hot rational kernels. Avoid a type parameter for every
expression tree shape and avoid `Expr`/`eval` as an evaluator.

Translate external theories into documented generic functions with a backend
argument and contract checks. Supply metadata and an explicit unsupported
default. Optional implementations belong in extensions when an actual backend
dependency exists. Passing interface tests is finite evidence; it does not
prove the full real or external theory. A certified-enclosure evaluator is
outside the parity milestone; in particular, endpoint projection agreement
alone must not be treated as certification across discontinuities or NaN regions.

## 6. Dependency-ordered phases and exit gates

Phases are pending. Each phase runs the per-change workflow in the companion
actions document; exits require evidence, not merely completed source files.

| Phase | Work | Exit evidence |
| --- | --- | --- |
| P0 — freeze and reconcile | Enumerate source files/rules/operations, hash current bytes, capture existing status, classify all content, record the stale historical plan hash and exclusion of existing Julia material; establish fresh Maude baseline. | Complete input/disposition manifest; exact baseline diagnostics and case counts; no unclassified semantic input. |
| P1 — package and semantic model | Verify Julia 1.13, establish workspace/test runner, public surface, values/formats/policies, residual/decision/error contracts, structured fixture format. | Clean-process import, constructor and invalid-input checks, exact large-integer/rational cases, documented API map and adapter result protocol. |
| P2 — codec and projection | Implement membership, codecs, queries, all nine rounding and three saturation families, predicates and ordering. | Independent small-format tables and round trips; boundary/stochastic/saturation cases; exact comparison with Maude. |
| P3 — rational scalars | Implement omega kernels, shared arity functions, core `SpecAPI` wrappers. | All applicable scalar/domain/order fixtures; FMA/FAA independent oracles; name, operand-order and single-projection checks. |
| P4 — blocks and scaled operations | Implement shared scale, normalization, block policies, reductions, conversions and generated wrapper families. | Matching source blocks, stochastic position tests, singleton scaling, aliasing/axes contracts, zero/NaN/infinite-scale regressions. |
| P5 — symbolic and contract boundaries | Translate symbolic syntax, exact special cases, guarded decisions and residual behavior; expose external/real protocols. | All symbolic fixtures, unresolved-domain/projection tests, unsupported backend behavior, fresh core tests through combined loading without method replacement. |
| P6 — conformance and evidence | Implement identity tables, requirements, declarations, partitions, observation/declaration κ; catalogue Lean and Maude proof obligations. | Finite-universe tests, seven external-format subsets, counts 341/443/549 per subset size, NaN-before-infinity κ precedence, complete obligation mapping. |
| P7 — tools, docs and final parity | Finish Julia tooling, deterministic generation, examples, full coverage reports, package QA and measured kernel review. | All required suites pass on pinned 1.13; source and operation coverage complete; no unexplained mismatches; explicit residual/proof limitations. |

P3 depends on P2; P4 on P3; P5 on P4 for symbolic blocks. P6 depends on the
value, ordering, block and contract schemas. Fixture and evidence work starts
in P0 and continues with each phase. P7 is not a late substitute for testing.

## 7. Validation design

Maintain three distinct comparisons: Julia against Maude normal forms for
the same inputs; Julia against independent exact fixture/oracle calculations;
and Julia interface/property tests. Use the Maude tree's Python reference
calculations and independently derived exact cases; do not use the existing
repository Julia implementation or its tests. Other Julia packages may provide
independent exact oracles when their semantics and independence are verified.
If an oracle shares the translated
algorithm, label the shared ancestry and
retain another independent check for the affected behavior.

Use structured cases with stable IDs, input terms, expected outcome category,
exact payload, source rule/fixture link, and profile. Existing JSON often
contains Maude assertion strings; it is not directly executable Julia data.
Translate those with a bounded parser or explicit reviewed mappings. Reject
unknown syntax and missing IDs; never `eval` translated strings or implement
an unbounded general-purpose Maude interpreter to avoid designing Julia APIs.
Normalize rationals as decimal-string numerator/denominator pairs, codes as
exact integers, special values as tags, and residuals as structural terms.
Compare outcomes and exact payloads rather than printed formatting alone.

Minimum semantic coverage:

- Every valid four-bit format and code; required eight-bit codec tables;
  reserved values, P=1, unsigned negatives, nondyadic membership and wide codes.
- Nine rounding modes × three saturation modes over source boundary grids;
  both signs, ties, subnormal/normal transitions, finite overflow and infinities.
  Exhaust the source's small stochastic ranges, including N=0.
- Source scalar suites and full ordering/adjacency suite; first-match NaN
  successor behavior and all documented FMA/FAA/ArcTan2 source cases.
- Block lengths and mismatches, explicit random sequence order, supplied versus
  computed result scale, exact reductions, and the §5.5.3 NOTE 2 regression.
- Every symbolic fixture, including exact roots and residual irrational roots,
  non-real domain terms, undecided comparisons, and missing backend calls.
- Conformance schemas, finite partitions, declaration presence, and κ
  precedence; never infer whole-domain accuracy from observed samples.

Rerun all applicable source case IDs. Historical counts can change only with
a recorded explanation; overlapping suites are not summed into a count of
distinct facts. Fail on missing, duplicate, unexpected, timed-out, malformed,
or unresolved results when the case requires a value. An expected residual
passes only if its reason and retained structure match the case contract.

Quality review uses guide §§62–68: meaningful genericity tests; load and
precompilation checks; Aqua or equivalent ambiguity/API/dependency checks;
targeted inference inspection/JET for concrete rational and array kernels.
Do not demand zero allocations from `BigInt` arithmetic or uniform concrete
returns from the symbolic layer. Benchmark after warm-up and report compile
latency separately. Optimize only after semantic parity, with exact regressions
retained. New concurrency is unnecessary for the initial implementation.

## 8. Review and refinement record

The first-pass approach was dependency-ordered translation of Maude files,
followed by fixture execution. Two review passes refined it before this plan
was written.

| Review finding | Refinement incorporated |
| --- | --- |
| File-for-file translation would duplicate imports and recursive sequence plumbing. | One reference package with cohesive files, shared kernels, standard collections and deliberate submodules. |
| Maude subsorts and partial operators do not map directly to Julia inheritance and exceptions. | Separate exact values, symbolic syntax, domain knowledge, invalid applications and undecided outcomes. |
| Treating all elementary operations as host math would discard exactness and partiality. | Exact special reductions plus residual terms; certified evaluation remains a separately evidenced extension. |
| An idiomatic rename alone would lose source-call traceability. | Qualified `SpecAPI` preserving 193 inventory-derived names and argument order over lowercase Julia functions. |
| Generating one body per operation would repeat the source's removed boilerplate. | Three shared arity paths and checked thin wrappers; handwritten semantic kernels. |
| The user excluded the existing Julia implementation and related documentation. | Remove reuse, API comparison and differential validation against that material; derive the independent reference from the Maude sources and the specified idiom guide. |
| The user expressly permits other Julia packages to simplify the result. | Prefer suitable package APIs over unnecessary custom machinery; compare total code clarity including adapters, record replaced responsibilities and compatibility, and validate semantics and oracle independence. |
| Old test counts and a stale source hash prevent a clean provenance claim. | Fresh baseline, current input hashes, named discrepancy and separate historical/current evidence. |
| “Convert all content” could be mistaken for translating proofs into tests and declaring them proved. | Per-file dispositions and explicit law/axiom/proof-status accounting. |
| Applying every 1.13 feature would add unnecessary mechanisms. | Use public API declarations/workspaces; verify new APIs only when needed; defer custom broadcast, macros, atomics and concurrency. |
| A checklist without completion semantics would permit silent skipping. | Required action IDs, phase gates, evidence records, narrow exception handling and final acceptance rules in conversionactions.md. |

The idiom review applies guide §§5–7 and 18–23 to dispatch/storage, §§8–11
and 15–17 to collection/ownership boundaries, §§12–14 to exact arithmetic,
§§24–33 to APIs/packages, and §§34–36 to errors and generation. This is a
project-specific design decision; language details remain subject to the
[official style guide](https://docs.julialang.org/en/v1.13-dev/manual/style-guide/)
and the selected runtime's
[1.13 release notes](https://docs.julialang.org/en/v1.13-dev/NEWS/).

## 9. Completion definition

The conversion is complete when every in-scope source item is accounted for,
all executable behavior and expected partial outcomes have matching Julia
coverage, the public API is documented, all required acceptance gates pass on
the recorded Julia 1.13 runtime, and the Julia package operates without Maude
or Python. Source comparison tooling may still invoke the pinned Maude engine.

The delivery must state remaining external/real implementation obligations
and proof limitations separately from conversion completeness. A missing core
operation, unexplained mismatch, skipped required test, or unverified 1.13 run
prevents final acceptance. Historical proof evidence and intentionally
preserved symbolic residuals do not prevent semantic parity when correctly
mapped and tested. The subsequent user request authorized implementation and
source cleanup; see `improvedconversion.md` and `evidence/deviations.md`.
