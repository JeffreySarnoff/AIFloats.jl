# Implementation plan: a modular Maude specification of P3109/D1

## 1. Purpose, authority, and delivery boundary

Implement the requirements and acceptance criteria in
[asspec.md](../other/asspec.md) as a collection of readable, independently
testable Maude modules under `docs/Maude/`. That document governs arithmetic
semantics and identifies the authoritative IEEE PDF. Maude documentation
governs the language and tooling choices below; it does not supply additional
floating-point semantics.

This document is the implementation plan. The files listed below, other than
this plan, are deliverables to create during implementation, not files claimed
to exist already.

Deliver three clearly distinguished capabilities:

1. **Executable rational core:** exact P3109 codecs, projection, rational
   arithmetic, comparisons, classification, order, and applicable block and
   scaled operations.
2. **Symbolic extension:** the remaining operations and general real
   compositions, with executable special cases and explicit residual terms
   when an exact decision has not been established.
3. **Contracts and evidence:** external-format interfaces, mathematical real
   obligations, conformance accounting, source traceability, and proof records.
   Loading these artifacts does not establish full conformance.

A reader must be able to load the core, evaluate a documented example, locate
the equation responsible for its result, and follow its source reference.
Large tables, proof-tool sessions, and experimental real evaluators must not
be prerequisites for that first use.

## 2. Toolchain and documentation baseline

Research date: **2026-09-08**. The official download and documentation pages
identify **Maude 3.5.1** as the current release/manual. The local executable
`/usr/local/bin/maude --version` also returned `3.5.1`. Keep semantic modules
compatible with this stable Core Maude version. Use the installed Maude++/MFE
stack for development proof checks; MFE's internal use of Full Maude does not
make Full Maude syntax a requirement for the semantic modules.
[Official downloads](https://maude.cs.illinois.edu/get-maude),
[official documentation](https://maude.cs.illinois.edu/documentation).

The official **Maude Manual 3.5.1, July 2025** was downloaded and consulted.
Relevant sections are §§3.3–3.8, 4.3–4.7, 7.1, 7.4, 8.1, 8.7, 8.14,
21.1, 21.3.8, and Appendix A. These cover sorts/kinds, conditions, evaluation,
imports, theories/views, rational arithmetic, containers, debugging, and
commands. Use this manual rather than old Maude 1 examples returned by search.
[Versioned manual](https://github.com/maude-lang/maude-lang.github.io/releases/download/maude/Maude3.5.1-manual.pdf).

For proof-tool planning, consult the current
[MFE installation instructions](https://github.com/maude-team/MFE/wiki/How-to-install-the-tool),
[MFE tools](https://github.com/maude-team/MFE/wiki/Tools-available), and
[SCC description](https://maude.cs.illinois.edu/tools/scc/).
MFE's current SCC requires Maude++ with CETA; ordinary Maude can run its CRC
and coherence checker. The required local proof stack is now installed and
has been exercised, so installation is no longer a pending implementation task.

| Component | Verified local entry point | Observed identity and role |
|---|---|---|
| Core Maude | `/usr/local/bin/maude` | 3.5.1; portable semantic execution baseline |
| Maude++ | `/usr/local/bin/maude++` → `/opt/maude++-3.5.1/maude` | 3.5.1; proof-session engine with the working SCC extension |
| MFE launcher | `/usr/local/bin/mfe` | Launches Maude++ and `/opt/mfe-3.5.1/src/mfe.maude`; banner reports MFE 3.0 |
| MFE implementation | `/opt/mfe-3.5.1/src/FM/full-maude351.maude` | Full Maude 3.5.1a, Nov 12 2025; loaded internally by MFE |
| CRC / ChC | `/opt/mfe-3.5.1/src/CRChC/crchc3u.maude` | Both report 3t, Feb 14 2026 |
| SCC | `/opt/mfe-3.5.1/src/SCC/scc.maude` | Reports 2b, Feb 14 2026 |

Record component banners as well as installation-directory names: the latter
are not reliable component version identifiers. The earlier general Maude++
SCC caveat is resolved for the MFE route: MFE's SCC works through its embedded
Full Maude on the same Maude++ 3.5.1 binary. As reported for this installation,
raw `/opt/maude++-3.5.1/scc.maude` remains broken when loaded standalone;
do not use that entry point. This update exercised the working MFE route,
not the standalone checker.

The existing `maude-scc` launcher selects the older Maude-ceta 2.3 installation.
It is redundant for this plan's 3.x modules and is neither a required dependency
nor a fallback proof profile. Keep all planned SCC sessions on Maude++ 3.5.1
through MFE; no removal of the older installation is part of this plan.

The `mfe` convenience launcher adds `-no-advise`. For auditable automated runs,
invoke `maude++` directly with the MFE entry file and retain diagnostics. Use
configurable executable and MFE paths so the repository does not depend on
this machine's `/opt` layout.

A constructor-only finite test passed CRC and SCC. CRC reported joined
critical pairs, local confluence, and sort decrease. SCC reported completeness
and soundness, but explicitly did not prove ground weak termination or ground
sort decrease. The same test with implicitly imported BOOL was rejected by
CRC as using unsupported built-ins and caused an SCC assertion abort. Treat
these as observed tool-scope limitations: screen proof inputs and never send
an unchanged unsupported target to SCC after CRC's rejection. Section 9
defines the proof workflow and treatment of built-in arithmetic. That input-
dependent MFE failure is distinct from the reported standalone SCC problem;
it does not negate the successful MFE check on the eligible constructor module.

Keep the baseline version fixed during implementation. A later upgrade needs
a recorded version change and rerun of affected parsing, reduction, and proof
checks. No installation or upgrade is part of writing this plan.

## 3. Proposed directory structure

Use one principal module per semantic file. A small, tightly related view or
test module may share that file when separating it would obscure its purpose.
Use cohesive operation families instead of one file per operation.

```text
docs/Maude/
  planmaude.md
  README.md
  load-core.maude
  load-symbolic.maude
  load-contracts.maude
  lib/
    xreal.maude
    rational-math.maude
    format-core.maude
    sequences.maude
    projection-spec.maude
    external-signature.maude
    codec.maude
    format-queries.maude
    rounding.maude
    saturation.maude
    project.maude
    omega-arithmetic.maude
    omega-extrema.maude
    predicates.maude
    order-next.maude
    scalar-ops.maude
    block-core.maude
    block-ops.maude
    conformance.maude
  symbolic/
    real-expressions.maude
    omega-elementary.maude
    scalar-ops.maude
    block-ops.maude
  contracts/
    real.maude
    external-format.maude
    external-bridge.maude
  optional/
    enclosure-evaluator.maude
  inventory/
    source.json
    operations.json
    traceability.tsv
  tools/
    generate-wrappers.py
    check-inventory.py
    run-tests.py
    run-proofs.py
  tests/
    support.maude
    smoke.maude
    domains.maude
    codec.maude
    projection.maude
    scalar.maude
    order-next.maude
    blocks.maude
    symbolic.maude
    conformance.maude
    vectors/
      tables-3-7.json
      behavior-cases.json
      regressions.json
  proofs/
    toolchain-smoke.maude
    obligations.tsv
    coverage.md
    deviations.md
    slices/
    sessions/
  examples/
    core.maude
    symbolic.maude
```

Generated wrapper files carry a generated-file header. Handwritten semantic
kernels do not. Temporary extractions, rendered pages, timing output, and
large test logs go in a configurable build/temp directory, not the committed
semantic tree. Commit compact proof session inputs and reviewed summaries.

## 4. Module ownership and dependency order

All module names begin with `P3109-`. File paths are lowercase with hyphens;
module names are uppercase with hyphens; view names use simple CamelCase
identifiers. Use explicit module names in reductions so load order cannot
silently change the selected module.

The table specifies direct semantic dependencies; built-in imports are omitted.
“Values” means `xreal`, and “formats” means `format-core`.

| File under lib/ | Principal module | Responsibility and direct dependencies |
|---|---|---|
| xreal.maude | P3109-XREAL | Rat/Real/XReal hierarchy, exceptional constructors, shared value vocabulary |
| rational-math.maude | P3109-RATIONAL-MATH | Exact powers, positive floorLog2, parity and square-root helpers; values |
| format-core.maude | P3109-FORMAT-CORE | Syntactic formats, validity, names, integer/enumeration metadata |
| sequences.maude | P3109-SEQUENCE{E :: TRIV} | Ordered nil/cons sequences, length and structural traversal |
| projection-spec.maude | P3109-PROJSPEC | Modes, scalar/block random operands, validity, indexing and singleton lift; sequences |
| external-signature.maude | P3109-EXTERNAL-SIGNATURE | Shared external operation declarations without invented implementations; values, formats |
| codec.maude | P3109-CODEC | P3109 decoder, full datum guard, encoder, external dispatch; rational math, external signature |
| format-queries.maude | P3109-FORMAT-QUERIES | Code-valued bounds and normal/subnormal queries; codec |
| rounding.maude | P3109-ROUND | Rational evaluator and shared signature for precision rounding; rational math, projection specs |
| saturation.maude | P3109-SATURATE | Ordered saturation cases; values, formats, projection specs; receives finite bounds as arguments |
| project.maude | P3109-PROJECT | Round–saturate–encode composition; queries, rounding, saturation |
| omega-arithmetic.maude | P3109-OMEGA-ARITHMETIC | Convert, Abs, Negate, CopySign, arithmetic, Recip, FMA, FAA; rational math |
| omega-extrema.maude | P3109-OMEGA-EXTREMA | Ten extrema and Clamp; values and exact comparisons |
| predicates.maude | P3109-PREDICATES | Five comparisons, eight predicates, Class; codec, queries |
| order-next.maude | P3109-ORDER-NEXT | TotalOrder and Next; predicates, codec, queries |
| scalar-ops.maude | P3109-SCALAR | Generated core numeric wrappers; project, omega families |
| block-core.maude | P3109-BLOCK-CORE | Encoded block shapes, decode/project, indexing; sequences, codec, project, omega arithmetic |
| block-ops.maude | P3109-BLOCK | Conversions, seeded reductions, dot product, generated core elementwise/scaled wrappers; block core, omega families |
| conformance.maude | P3109-CONFORMANCE | Required-set/declaration checks and finite κ helpers; formats, projection specs, predicates and ordered finite-value support |

Expose `P3109-CORE` as the final façade module in `load-core.maude`, importing
the public scalar, predicate/order, block, and conformance modules. Helpers
are implementation interfaces even though Maude imports make them visible.

Dependency invariants:

- Format metadata never imports codecs or value queries.
- Decoder-image membership never calls the encoder or extrema queries.
- Saturation receives bounds; only projection obtains and decodes them.
- Numeric ω kernels never call projected public wrappers.
- Conformance does not import tests or a candidate implementation by default.
- Tests and proof sessions sit above semantic modules; semantic modules never
  import their expected answers.

The symbolic files extend these modules with real-expression support,
elementary ω operations, and their scalar/block wrappers. They do not define
another decoder, saturation function, or block-projection algorithm.

The `contracts/` files declare mathematical obligations as functional theories
and a parameterized external bridge. They do not import a theory directly into
an ordinary functional module: theories enter modules through parameters and
views. The external bridge supplies equations for the shared external
signature only after a concrete backend and its view obligations are available.
It is excluded from the executable façade while uninstantiated.

## 5. Representation and Maude discipline

### 5.1 Values, kinds, and partiality

Follow asspec's `Real < XReal` hierarchy with the rationals embedded by
`fin : Rat -> Real` rather than declared as a subsort, so that the built-in
numeric kind and the kind of `XReal` stay separate (see README, Values and
calls). Declare exceptional
constructors using unambiguous ASCII names such as `nan`, `posInf`, and
`negInf`; map them explicitly to the draft notation. Keep numeric ω operation
names distinct from built-in RAT operators, for example `omegaAdd` rather
than overloading RAT's `_+_` on XReal.

The core supplies rational reductions. Merely declaring `Real` does not
implement all mathematical reals. The symbolic layer supplies expressions
and sound selected reductions, with an explicit interpretation described in
the real contract. Raw domain-restricted functions must not manufacture a
finite Real result for an invalid argument. Use guarded definitions and,
where needed, kind-level declarations for partial functions.

Use `validFormat`, `validCode`, `datum`, projection validity, and block-shape
predicates consistently. Distinguish a specified NaN result from an invalid
application left unreduced. Parameterize format terms by integers or naturals
as appropriate and check the draft's bounds; do not use membership axioms to
pretend that an unconditional Format constructor did not already assign a sort.

For intentionally partial helpers returning built-in sorts, consider Maude's
`~>` kind-level declaration and refine the result through valid reductions.
This avoids silently adding stuck ground values to protected Nat, Rat, or
Bool sorts. Because Rat, Real, and XReal share a kind, a stuck term may print
with a kind name such as `[XReal]`; its spelling is not a new numeric error
value. The harness checks the expected application/domain status, not just
the printed kind name. [Manual §§3.3–3.8, 7.1](https://github.com/maude-lang/maude-lang.github.io/releases/download/maude/Maude3.5.1-manual.pdf).

### 5.2 Imports and theories

Audit each import instead of applying one keyword everywhere. `protecting`
asserts preservation of existing values and equalities; Maude does not prove
that assertion merely by loading a file. Use it where justified, particularly
for unchanged built-in data. Use `extending` when adding values without
identifying old ones, and `including` when deliberately adding equations or
when the stronger assertion has not been established. Account for transitive
imports as well as direct edges. Do not weaken built-in numeric semantics
just to silence an import-design problem.

The real contract must not acquire a purported implementation view into RAT
or rational intervals that cannot satisfy its axioms. Keep syntactic expression
representation, mathematical interpretation, and executable certification
distinct. Successful view parsing checks mappings, not their semantic proof
obligations. [Manual §§7.1, 7.4](https://github.com/maude-lang/maude-lang.github.io/releases/download/maude/Maude3.5.1-manual.pdf).

### 5.3 Equations, guards, and evaluation

Use `fmod`, `eq`, and `ceq` for deterministic operations. Do not use rewrite
rules, search strategies, or equation order to implement source priority.
Each effective guard includes its complete source match and exclusions of
earlier matches, as required by asspec. Separate NaN/infinity cases first,
then finite sign/range cases, to keep the exclusions small and reviewable.

Conditions must be executable left to right: bind helper results with matching
conditions before using them, and never introduce an unbound candidate by
asking Maude to solve an arbitrary equation. Use named helpers for the draft's
`where` expressions. Put cheap validity checks before logarithms, division,
large powers, or list traversal. Ordinary Boolean conjunction is not a
short-circuit guarantee; use guarded helpers or EXT-BOOL operations when
evaluation order matters.

Do not use a failing symbolic test as evidence that its negation is true.
In particular, built-in equality of normal forms is not an oracle for
mathematical equality of symbolic real expressions. Define dedicated real
comparison predicates with exact rational cases and sound symbolic cases;
leave other comparisons unresolved. Restrict `owise` to audited decidable
constructor cases, never as the fallback for an unknown real comparison.

Use default evaluation strategies initially. Introduce `strat` only with a
specific performance/termination argument and regression check. `frozen`
controls rewriting by rules and is not the mechanism for suppressing
equational evaluation in these functional modules.

Give every equation a stable label, for example `p3109-4-7-5-unsigned-low`;
attach clause/page metadata and retain a separate field for the source's
ordered row number. Proven lemmas may be stored as `nonexec` statements in
proof-oriented modules, with their proof status recorded. `nonexec` does not
mean the equation has no semantic consequences.
[Manual §§4.3–4.7, 8.1](https://github.com/maude-lang/maude-lang.github.io/releases/download/maude/Maude3.5.1-manual.pdf).

### 5.4 Containers and abstraction size

Use the small `P3109-SEQUENCE{E :: TRIV}` nil/cons container for ordered
element and random sequences. Instantiate it through named views for XReal,
code points, and random integers; identify code points versus datums at the
operation boundary. The shared container owns length/traversal, while the
numeric modules own seeded folds.

Implement the three required folds as named first-order helpers for Add,
Multiply, and MaximumFinite. Do not treat a Maude operator as a runtime
function argument. The wrapper generator likewise substitutes a concrete
operator into each block schema; no higher-order interpreter is needed.

This deliberately avoids associative matching and membership complications
for block shapes. Do not mark a floating-point reduction associative or
commutative to simplify traversal. Do not use an associative-commutative set
for an ordered operand sequence. Built-in LIST remains an alternative if a
later measured benefit warrants its matching and proof obligations.
[Manual §§7.4, 8.14, 21.3.8](https://github.com/maude-lang/maude-lang.github.io/releases/download/maude/Maude3.5.1-manual.pdf).

Use runtime Format terms for K/P/signedness/domain; avoid one parameterized
module instance for every bitwidth and projection mode. Reserve theories/views
for actual interchangeable interfaces, principally containers and external
backends. Introduce no reflective DSL for the core arithmetic.

## 6. Loading, public use, and generated wrappers

Each loader explicitly loads files once in topological order. Semantic leaf
files contain declarations and imports, not nested loader commands or test
reductions. Use fresh Maude processes in automated checks. Avoid `sload` for
generated or rapidly changed files because timestamp-based reuse can obscure
changes. Force at least one reduction in each concrete module to expose lazy
compilation warnings. [Manual Appendix A](https://github.com/maude-lang/maude-lang.github.io/releases/download/maude/Maude3.5.1-manual.pdf).

Document `docs/Maude/` as the working directory for loader-relative paths.
The runner computes that directory from its own path so it also works when
invoked from the repository root. Keep the distributed prelude available;
do not modify the user's global Maude startup files or require global settings.

Intended commands once implemented:

```sh
cd docs/Maude
maude -no-banner -no-ansi-color load-core.maude
maude -no-banner -no-ansi-color load-symbolic.maude
python3 tools/run-tests.py --suite smoke
python3 tools/run-tests.py --suite core
python3 tools/run-tests.py --suite symbolic
python3 tools/check-inventory.py
python3 tools/run-proofs.py --suite smoke
python3 tools/run-proofs.py --suite eligible
```

`run-tests.py` defaults to Core Maude and accepts an engine override for a
Maude++ compatibility run. `run-proofs.py` defaults to Maude++ 3.5.1 with the
installed MFE entry file, loads the target modules before MFE, and feeds MFE
commands through stdin. It creates a fresh process and temporary working
directory for each proof target, with a timeout and captured stdout/stderr.
It does not invoke the advisory-suppressing convenience wrapper.

The locally tested MFE command sequence is:

```text
(select tool CRC .)
(ccr MODULE-NAME .)
(select tool SCC .)
(scc MODULE-NAME .)
quit
```

Here `ccr` is the actual CRC command, not a spelling error. The runner parses
and screens the CRC result before scheduling SCC; the command sequence above
is for an eligible target. The phase-A toolchain smoke target contains two
constructors and a total flip operation, with implicit BOOL import disabled
for its declaration and restored afterward in that isolated process.

`load-symbolic.maude` loads the core before its extension; users choose it
instead of loading both entry points sequentially. `load-contracts.maude`
loads shared declarations, theories, and uninstantiated bridge declarations,
and makes no claim of a working external backend. No library loader exits
the interactive session; batch test scripts finish with `quit`.

The operations inventory records name, arity, source clause/pages, parameter
and operand order, result category, valid block/scaled substitutions, and
execution profile. It is extracted from normative definitions, not Annex F.
The generator emits repetitive scalar/elementwise/scaled wrappers only.
Special-value equations, rounding, saturation, and conformance requirements
remain handwritten and reviewed against their source.

Generation is deterministic and has a check mode that compares temporary
output against committed files. Keep independent expected-case fixtures;
do not generate both an implementation and its expected result from the same
expression. Explicitly preserve ArcTan2's operand order, Softplus spelling,
RoundOf/SatOf, nonnumeric results, and supplied result scales.

For conformance evaluation, represent specialization identities as ordinary
data. Feed the finite κ evaluator explicit observations containing operands,
defined results, and candidate results, supplied by a test adapter. Keep
coverage evidence separate: a maximum over a sampled batch is not the κ over
all valid operands. No candidate callback or external execution is hidden in
the mathematical conformance module. Exact specializations and nonnumeric
results retain the separate obligations specified in asspec.

## 7. Implementation phases and exit criteria

| Phase | Work | Exit evidence |
|---|---|---|
| A — Freeze interfaces | Source/tool manifests, installed CRC/SCC smoke target, inventory skeleton, shared sorts, partial operators, container views, loader conventions | Tiny concrete modules parse and reduce on Core Maude and Maude++; CRC/SCC smoke results reproduced; proof eligibility and import/guard decisions recorded; no unsupported real/backend view |
| B — Deliver a usable numeric slice | Format metadata, rational helpers, decoder, guarded encoder, queries, all modes, project; one scalar Convert example | All 14 four-bit codec round trips, source tables, invalid-domain cases, and projection boundaries pass |
| C — Complete rational scalar families | Arithmetic, extrema, predicates, Class, order/Next, generated wrappers | Asspec scalar coverage, original FMA/FAA case comparisons, mixed-format order and exact adjacency checks pass |
| D — Complete rational block families | Shapes, stochastic indexing, block decode/project, conversions, reductions, elementwise/scaled wrappers | Unit-scale equivalences, malformed-shape checks, all specified special-scale cases and NOTE regression dispositions pass |
| E — Add symbolic semantics | Real expressions/contracts, elementary special cases, exact rational Sqrt, remaining wrappers | Special/domain cases pass; unknown results stay visibly unresolved; rational-core results remain unchanged |
| F — Account for conformance | Required specialization inventory, exact/approximate records, κ and partitions, external interface obligations | Required-set fixtures and negative declarations pass; reports distinguish proofs, failures, and pending contracts |
| G — Close evidence and documentation | Coverage arguments, installed CRC/SCC sessions on eligible targets, source findings, runnable examples, README | Every asspec criterion has evidence or an explicit pending obligation; no unexplained proof-tool rejection or abort; clean independent loads and tests |

The optional enclosure evaluator follows Phase E and is not required to
finish the exact rational core. It accepts only checked value-containment
and constant-projection-region certificates for a fixed format/mode/random
operand tuple. Keep the `[-100,100]` equal-endpoint/NaN counterexample as a
negative test. No fixed enclosure width is a universal completion criterion.

Run CRC/SCC incrementally on eligible modules or justified proof slices as
phases B–F complete, rather than postponing all mechanical checks to phase G.
Installation does not make every RAT-based or symbolic module eligible; record
unsupported targets and their alternative evidence when first encountered.

External finite encodings remain contracts under asspec's source restriction.
They are not implemented from the Maude manual. Before adding a concrete
backend, establish an authorized semantic source and discharge its datum,
canonicalization, quiet-NaN, finite-value counting, and bridge obligations.
The implementation phase must report the remaining external dependency rather
than silently treating coverage declarations as full P3109 conformance.

## 8. Validation design and throughput

The runner launches plain Maude subprocesses; no language-binding dependency
is necessary. It captures diagnostics and checks structured test summaries.
Process exit status alone is insufficient: an unreduced assertion, missing
test sentinel, parser warning, timeout, or unexpected advisory fails the
applicable executable suite. Intentional invalid/symbolic terms have explicit
expected classifications and must not be counted as successful numeric results.

Implement a simple TestResult constructor carrying case ID and pass/failure
details, and a suite summary with expected and executed counts. Tests compare
NaN by its intended representation or classification rather than IEEE numeric
equality. Do not suppress warnings with `-no-advise` to make a run look clean.

| Area | Required validation |
|---|---|
| Domains | K/P restrictions, unsupported datums, code bounds, scalar/block random bounds, exact block lengths, B≥1 |
| Codec/queries | Full four-bit tables and bijection; F4/F8/Fs; 240 rejected in Binary8p4se; code-valued extrema and P=1 |
| Projection | All nine modes and three saturation modes; 21 ordered cases; ties, both underflow signs, directed clipping; explicitly bounded stochastic fixtures |
| Scalar | Unary/binary coverage, FMA's 17 initial NaN rows, original FAA cases, one final projection, exact rational square roots |
| Ordering | Same- and mixed-format TotalOrder; Class partitions; immediate neighbors for Next and explicit NaN/endpoints |
| Blocks | Separate scale/element formats and modes, NaN-before-zero, infinity signs, left-fold order, singleton lift, unit-scale equivalences |
| Real/symbolic | TanPi half-integer poles, 17 ArcTan2 rows, finite results from exceptional inputs, composed real expressions, unresolved comparisons |
| Declarations | Full §4.5 parameter combinations, exact/approximate distinction, NaN/Inf κ precedence, partitions, multi-result κ, pending external obligations |
| Informative material | §5.4.2 NOTE 2 passes; §5.5.3 NOTE 2's 224/+Inf counterexample is retained; D.1 analytical count and D.2 declaration fixture are distinguished |

Use exact rational fixture generation where appropriate. Approximate decimal
table entries carry their documented display tolerance; all other expected
values stay exact. Include the source's subnormal annotations explicitly.

Throughput choices:

- Start each change with the affected suites and their dependents; run the
  full core suite at phase boundaries and before recording completion.
- Enumerate the full four-bit input spaces. Use focused eight-bit boundaries
  and the exhaustive scopes required by asspec; do not add arbitrary cubic
  eight-bit tests. Mixed-format TotalOrder over F4∪F8 has 528² pairs and can
  be batched by ordered format pair.
- Reuse an independently decoded/sorted datum list for order, adjacency, and
  finite rank checks. Keep it separate from production Next code arithmetic.
- Batch many reductions per process. Stream or chunk large products rather
  than constructing huge lists of all tuples in Maude memory.
- Partition independent test suites across a bounded number of processes
  after measuring memory. Semantic dependency checks and edits stay ordered.
- Keep proof processes separate from reduction batches. Cache eligibility
  and proof results by target/import hashes, engine/MFE hashes, and options;
  invalidate them when any dependency changes. Recheck affected eligible
  targets rather than reloading the complete proof environment per test case.
- Compute rational helpers once per operation using bound intermediates;
  introduce `memo` only after profiling a repeatedly reused bounded key space.
- Do not enumerate D.2's 442,050,625 operand tuples without an actual
  approximate implementation and a separately justified experiment.

## 9. Proof and traceability records

`source.json` records the authoritative PDF path/hash from asspec, the asspec
hash used for the implementation revision, Core Maude and Maude++ executable/
prelude versions and hashes, MFE/CRC/SCC banners and source hashes, extraction
provenance, and official documentation URLs with access dates. Record a CETA
build identifier if available; do not invent a separate version from an SCC
success. Include launcher options and the actual resolved paths used by each
session.

`traceability.tsv` maps each source requirement, behavior, formula, NOTE, and
recommendation to module/equation labels and test/proof IDs. Include both
clause and page references. Permit many source rows to one justified equation
family, and distinguish modeled semantics from executable coverage.

`obligations.tsv` contains ID, module, property, assumptions, proof method,
tool/backend version, session artifact, and status. Separate:

- termination and sort decrease/preregularity;
- confluence modulo declared operator attributes;
- sufficient completeness on valid concrete domains;
- equivalence of optimized guards to first-match semantics;
- validity of imports and views;
- symbolic interpretation and external-backend obligations.

Use the installed proof tools through the following workflow:

1. Pass parsing and concrete reduction tests first; reproduce the small
   CRC/SCC toolchain smoke test after an engine or MFE change.
2. Inspect the flattened target and its imports for built-ins, unsupported
   conditions, deliberate partiality, and uninstantiated parameters. Classify
   it as eligible, unsupported, or needing a separately justified proof slice.
   Implicit BOOL imports count: a source file with no visible numeric import
   is not necessarily free of built-ins.
3. Run CRC on eligible targets and retain its exact conclusions and critical
   pairs. Local confluence is not termination; combine it with the required
   termination argument before claiming convergence.
4. Run SCC only on a screened eligible target. Record completeness, soundness,
   and any explicitly unproved properties separately. A timeout, assertion
   abort, unavailable hook, or unsupported-input result is not a successful
   proof or a mathematical counterexample to the specification.
5. For RAT-based modules that these checkers cannot handle directly, use
   constructor-based proof slices only when a documented abstraction/refinement
   argument connects the slice to the production module. Store those modules
   in `proofs/slices/` with separate obligations. Removing a built-in import or
   replacing arithmetic with unconstrained symbols is not by itself a proof
   of the original module. Preserve concrete tests and manual arguments for
   the original semantics; leave unclosed obligations pending.

CRC and SCC checks are expected development work for eligible targets, not
optional work waiting for installation. They are separate from the portable
Core Maude execution profile. The installed MFE `show tools` output lists
CRC, ChC, and SCC; it does not establish an available automated termination
backend. Continue recording manual termination measures unless a backend is
separately configured and verified. The coherence checker is relevant only if
rewrite rules are introduced; the planned functional core has none.

Use explicit statuses such as `proved`, `counterexample`, `unsupported`,
`tool-error`, and `pending`, alongside the exact tool conclusion and assumptions.
The runner must reject missing conclusions and unexpected process termination.
Keep toolchain checks separate from ordinary execution tests.
[MFE](https://github.com/maude-team/MFE/wiki),
[SCC scope](https://maude.cs.illinois.edu/tools/scc/).

`coverage.md` holds disjoint/exhaustive case arguments, recursion measures,
and refinement explanations. `deviations.md` distinguishes source findings,
implementation choices, exclusions, and pending contracts. It must preserve
the K=2 exclusion and the confirmed §5.5.3 NOTE 2 conflict without reviving
the rejected criticism of §5.4.2 NOTE 2.

## 10. Review of the plan and incorporated improvements

| Review concern | Decision incorporated | Desired result |
|---|---|---|
| A specification that is difficult to start using | Core façade, separate loaders, early Convert example | Useful exact results before symbolic/proof work is complete |
| Excessive files or generic machinery | Cohesive operation-family files; parameterize only real interfaces | Small understandable dependencies without one module per format |
| Cyclic metadata/codec/query dependencies | Decode-image membership below query layer; explicit bounds to saturation | Acyclic loading and independently testable codecs |
| Treating a mathematical real theory as executable | Separate expression evaluation, contracts, and certificates | Exact symbolic meaning with honest unresolved results |
| Incorrect mathematical use of syntactic equality | Dedicated real predicates; unknown guards remain unknown | No false answers from distinct symbolic normal forms |
| Unjustified protecting imports and partial results | Import audit, kind-level partial helpers, view obligations | Semantically honest modules rather than merely warning-free loads |
| Container matching complicating block proofs | Structural nil/cons sequences with shared traversal | Predictable recursion and preserved operand order |
| Generated implementations validating themselves | Generate wrappers only; independent behavior fixtures | Tests that can detect transcription errors |
| Inverse Next tests missing skipped values | Independent adjacency checks | Direct validation of the required least/greatest neighbor |
| Installed tools unused or overstated | Run CRC/SCC on eligible targets; retain unsupported-input and termination obligations | Mechanical evidence from the available stack without false global proof claims |
| Proof tools blocking basic use | Separate portable Core Maude tests from installed MFE/Maude++ sessions | Runnable specification with visible proof coverage |
| Large exhaustive jobs slowing every edit | Dependency-aware suites and bounded batches | Fast feedback without weakening asspec's required coverage |

During preparation, a temporary Maude 3.5.1 probe checked the proposed
Rat/Real/XReal declarations, exact `1/3+1/6=1/2`, a guarded `Int ~> Nat`
operation retaining an invalid application, and a TRIV-parameterized nil/cons
sequence instantiated by a view. All reduced as intended without diagnostics.
This confirms those language choices only; it is not an implementation of
the listed P3109 modules or a proof of their eventual correctness.

After the recent installations, a separate Maude++/MFE probe confirmed the
versions and CRC/SCC conclusions in Section 2. Its pure-constructor variant
passed; its implicit-BOOL variant exposed the rejection/abort described there.
The updated plan therefore adds proof-input screening, reproducible sessions,
and explicit termination/refinement obligations rather than assuming that
installation proves compatibility with all proposed modules.

The plan is ready to implement when Phase A's interfaces and inventory are
concrete. Completion of the specification requires the phase exit evidence
and asspec's acceptance criteria, with external/general-real obligations
reported separately. Writing this plan does not mark any future test or
proof obligation as discharged.
