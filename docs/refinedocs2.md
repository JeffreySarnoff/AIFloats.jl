# Documentation refinement plan

## 1. Purpose and scope

Make the documentation a faithful, verifiable Interface to AIFloats.jl 0.2.x.
When this work is done, a reader can move from format definition to datum
construction, projection, scalar and array operations, packed storage, blocks,
performance policy, and conformance without meeting a spelling, default,
example, or performance claim that disagrees with the package.

**In scope:** narrative pages, examples, source docstrings, the reference and
internals split, project metadata, and the policy that keeps performance prose
tied to generated evidence.

**Out of scope:** numerical semantics. This plan authorizes no change to
rounding, saturation, table, block, or carrier behavior. If an audit exposes a
source-code defect, file it as a source issue and settle the code-versus-report
question *before* rewriting documentation around it. Never edit an algorithm so
that stale prose becomes true.

## 2. How to use this plan

Every work item has a stable ID: `P0-n` (correctness blocker), `P1-n` (public
API completeness), `P2-n` (maintainability), `PERF-n` (performance policy),
`V-n` (validation). Later sections — the page-by-page table, the gates, the
checklist — reference IDs instead of restating the work. If an item's text and
a reference disagree, the item's text wins.

Each item states **What is wrong**, **What to do**, and **Done when**. "Done
when" is the acceptance test; if it cannot be checked mechanically or by a named
probe, it is not yet written well enough.

Ordering is by gate (§9), not by ID. Within a gate, P0 precedes P1 precedes P2.

## 3. Audit baseline and re-verification

The audit that produced this backlog ran on 2026-09-01 against package version
0.2.0, `main` at `2b7893e`, plus an uncommitted constructor fast-path edit in
`src/ops/scalar.jl`.

That edit has since been committed: **the audited tree corresponds to `d68a8ba`
("perf: extend the guard ladder to the value constructor")**, which is the
baseline to cite from here on. No benchmark page committed before `d68a8ba`
describes the audited tree; see PERF-1.

Counted findings in this plan (public-binding totals, undocumented-name lists,
threshold values) are baseline observations, not invariants. Regenerate them at
Gate 2 rather than trusting the numbers printed here.

The normative report pinned for this review is the IEEE P3109 **Interim Report
on Arithmetic Formats for Machine Learning**, version 4.0.3, dated 2026-09-01,
downloaded PDF SHA-256
`7de115ed6882b7550b8fa61e81e5173857b340c3bfe30db8d4ad74b472229b9e`.

## 4. Ground truth

### 4.1 The single normative authority

Normative semantics come from exactly one document:

> <https://github.com/P3109/Public/blob/main/IEEE%20P3109%20Interim%20Report.pdf>

**No other IEEE document may be cited, consulted to settle a conflict, or used
to justify a semantic claim** — not an earlier draft, not a published IEEE
standard, not a working-group slide deck, not a local transliteration. If the
designated report is silent or ambiguous, that is a maintainer decision to
record as a package interpretation, not an invitation to import an outside
definition.

If the PDF at that URL changes, repeat the comparison and record the new cover
version, date, and digest. A mechanical text extraction may help *locate*
sections; citations and final semantic decisions must refer to the PDF itself.

### 4.2 Implementation actuality

The source tree is the sole authority on what the package actually does. A
docstring, a test expectation, `docs/other/IEEE_D1.md`, and `draft_identity()`
are all *comparison subjects* — evidence to audit, never overrides. Where source
and report disagree, the disagreement is a finding to classify (§9, Gate 0), not
a wording problem.

### 4.3 Truth hierarchy

Every statement in the documentation should make clear, at least implicitly,
which kind of truth it is:

| Tier | Kind of truth | Authority |
|:--|:--|:--|
| 1 | Normative semantics | The designated Interim Report PDF, and nothing else |
| 2 | Package contract | Exported and `public` bindings, their methods, docstrings, targeted tests. Private names are implementation details even when they carry docstrings |
| 3 | Observed behavior | Executable examples and focused Julia probes against the current tree |
| 4 | Performance | A Chairmarks result tied to commit, Julia version, thread count, CPU, inputs, and cache state |
| 5 | Motivation, general numerical advice | Externally sourced and qualified; never presented as an AIFloats guarantee |

Two rules follow. **Never launder a tier upward:** a test expectation is not
normative, a measurement is not a proof, and training folklore is not a
contract. **Never attribute a Julia extension to the report:** if AIFloats
offers something the report does not define, label it a package extension.

### 4.4 What this buys

Separating the tiers gives the documentation Module depth — the public Interface
states stable concepts and contracts while carrier selection, cache keys, proof
guards, and enclosure rungs stay behind explicit expert Seams. It also improves
Locality: each default, threshold, and operation inventory gets one
authoritative statement, and every other page links to it.

*Terms used in this plan:* **Interface** = what a user is promised; **Seam** =
a deliberate, documented entry point into deeper machinery; **Module depth** =
much behavior behind a small Interface; **Locality** = one fact stated in one
place.

## 5. Shared vocabulary

Fix these once here; every page and docstring reuses them.

### 5.1 The canonical triad

```julia
F = Binary8p4se       # format type
T = BinaryValue(F)    # concrete AbstractFloat datum type
x = F(1.5)            # datum (a value of type T)
```

Notation across all examples: `F` a format, `T` a datum type, `x` a datum, `c` a
code point, `ρ` a projection, `A` an array.

`F()` is deliberately invalid. `F(x)` consumes a numeric value. `fromcode(F, c)`
consumes a raw code point. Capitalized names such as `Binary8p4se` are **format
types**, never "datum aliases."

### 5.2 Datum versus value

In the Interim Report §3.1 a *floating-point datum* is the mathematical element
and a *floating-point value* is its code point in an associated format. In
Julia, `BinaryValue` is the concrete `AbstractFloat` object that stores that code
point and behaves numerically as the datum. Never use "value" in both senses in
one explanation; when the report sense is meant, say "code point."

### 5.3 Report names versus package names

Where AIFloats spells something differently from the report, say so explicitly
rather than implying the package spelling is quoted from the report. Maintain
one mapping table (owned by the projections page, linked from elsewhere), for
example:

| Report term | AIFloats spelling | Classification |
|:--|:--|:--|
| `NearestTiesToEven` | `RoundToEven` (`RTE`) | Package long name |
| `NearestTiesToAway` | `RoundToAway` (`RTA`) | Package long name |
| `ToOdd` | `RoundToOdd` (`RTO`) | Package long name |
| `TrailingSignificandBitwidthOf` (§4.5) | `TrailingSignificantBitsOf` | **Source/API delta to classify — not a prose fix** |

Gate 0 completes this table; each row is classified as a package long name, a
deliberate Julia extension, or a defect to file.

## 6. Backlog

### P0 — correctness blockers

**P0-1 — Reconcile the claimed draft identity with the designated report.**
*What is wrong:* `draft_identity()` names "IEEE P3109/D1, uploaded 2026-07-17"
and a local Markdown transliteration. The designated report's introduction also
uses the D1 designation, but its cover identifies the current revision as
Interim Report version 4.0.3 dated 2026-09-01. The package therefore makes an
unverified claim about which revision it implements.
*What to do:* Produce the §9 Gate 0 semantic delta covering every implemented
format, projection, scalar operation, block operation, and
conformance-declaration rule. File a source defect for each disagreement. Only
after those are resolved, update `draft_identity()` (revision, date, digest),
README, Status, and conformance output to identify the report precisely. Do not
relabel old behavior as current compliance by prose alone.
*Done when:* the delta matrix is complete and every remaining
identity/compliance sentence in the package traces to a resolved row.

**P0-2 — Repair the bit-budget derivation.**
*What is wrong:* `docs/src/20-concepts.md` correctly starts from

```text
K = S + exponent bits + (P - 1)
```

then rearranges it as `K - P - S`, dropping the `+1`. Consequently
`Binary(8,4,SIGNED,...)` is described as having 3 exponent bits and its unsigned
counterpart 4.
*What to do:* The exponent-bit count is `K - S - (P - 1)`, equivalently
`K - P - S + 1`; the correct values are 4 and 5. Fix the prose, the worked
examples, and the comparison table. Fix the same omitted `+1` in the
`PrecisionOf` docstring in `src/types/binaryformats.jl`.
*Done when:* V-3 asserts the algebra against `ExponentBitwidthOf`, so the
foundational explanation cannot drift again.

**P0-3 — State the actual default projection.**
*What is wrong:* `10-getting-started.md`, `40-projections.md`, and the `RTE_SF`
docstring call `RTE_SF` the conventional or package default.
*What to do:* `DefaultProjection()` is initially `RTE_SN` and is task-local
through `ScopedValue`. Correct all three sites and keep the distinct defaults
explicit: ordinary construction and arithmetic use `RTE_SN`; `rand` defaults to
`RTZ_SN`; `randn` defaults to `RTE_SF`. Do not infer a report-wide "default
projection" from §4.5's required specializations under `(NearestTiesToEven,
SatNone)` — `RTE_SN` is the *package's* task-local default (see P1-8).
*Done when:* V-3 asserts `DefaultProjection() === RTE_SN` and no page names a
different package default.

**P0-4 — Correct the format/datum alias description.**
*What is wrong:* Capitalized format names are described as "datum aliases," and
"value" is used in two senses.
*What to do:* Adopt §5.1 and §5.2 verbatim wherever the triad is introduced.
State that `F()` is invalid, `F(x)` takes a numeric value, and `fromcode(F, c)`
takes a code point.
*Done when:* V-3 asserts alias-is-format-type and `BinaryValue(F)`-is-datum-type,
and the terminology map appears once with links from every other page.

**P0-5 — Fix contradictory constructor docstrings.**
*What is wrong:* In `src/types/binaryformats.jl`, `Binary`'s docstring says
"Append `()` when you need a value," contradicting both the implementation and
its own next paragraph; `CodeType` and `ValueType` are documented as accepting a
`Binary` instance. In `src/types/binaryvalue.jl`, "session default" misdescribes
a task-local default, and committed phase/temporary-diagnostic comments no
longer describe the delivered Interface.
*What to do:* Remove the contradictory sentence and the instance-accepting
claims; replace "session default" with "task-local default"; delete the stale
comments.
*Done when:* doctests (V-1) pass and no docstring in those two files describes
behavior the implementation refuses.

**P0-6 — Make the saturation example distinguish the modes.**
*What is wrong:* The Intermediate example projects finite `1.0e100` under
`RTE_SF` and `RTE_SP`; both correctly clamp to the same largest finite datum, so
the example teaches nothing about the difference.
*What to do:* Use `Inf` in an extended format: `SF` clamps a genuine infinity
while `SP` propagates a representable infinity. Add a compact semantics table —
`SF` clamps all out-of-range results including infinities; `SP` propagates only
a representable input infinity and clamps finite overflow; `SN` follows rounding
direction, signedness, and domain, and can yield an extremal finite, an
infinity, or NaN.
*Done when:* the three modes produce visibly distinct printed results in the
example block.

**P0-7 — Remove the private cache call from Technical examples.**
*What is wrong:* The examples call `get_table`, which is deliberately neither
exported nor `public` in 0.2.0. The second `technical_cache` block also depends
on state from an earlier block — the one Examples block that is not
self-contained.
*What to do:* Populate a table through the exported `vmap`/`vmap!` Seam and
inspect it with `table_stats()` and `table_entries()`. Add `using AIFloats` to
the block.
*Done when:* V-3 asserts `get_table` is not public while `table_policy`,
`table_stats`, and `table_entries` are, and V-4 runs the block in a fresh module.

**P0-8 — Do not present two cache snapshots as one moment.**
*What is wrong:* Prose implies `table_stats()` and `table_entries()` observe a
single instant. Each is coherent under its own lock, but two calls can observe
different moments.
*What to do:* Say that entry bytes equal a separately obtained
`table_stats().bytes` only when the cache is not mutated between the calls.
Where one coherent count-and-byte declaration is required, point to
`conformance()`, which derives its byte total from its own captured entry vector.
*Done when:* no page claims cross-call atomicity, and the coherent path is named.

**P0-9 — Repair the table-policy description.**
*What is wrong:* `50-status.md` says signatures above the eager unary/binary band
always compute, and describes adaptivity only for ternary tables. The source has
a binary adaptive band too: `TABLE_ADAPTIVE_BITS[] == 18` and
`TABLE_BUILD_ELEMS[] == 1_000_000` (`src/tables/policy.jl`).
*What to do:* Document every outcome of `table_policy` — eager,
binary-adaptive, ternary-adaptive, byte-refusal, stochastic, and beyond-band —
without teaching private cache builders. Follow PERF-3 for the threshold
constants.
*Done when:* the documented outcome set equals the branches of `table_policy`,
and threshold values are generated or tested rather than transcribed.

**P0-10 — Correct stale block and decoding performance statements.**
*What is wrong:* `BlockReduceMultiply` is described as always using `BigFloat`;
it has a checked exact `Dyadic` fast path. A blanket "wider formats ~3 ns" claim
is contradicted by K=16 rung-2 decoding, which is materially slower.
*What to do:* Replace both with the guard/fallback contract — what is attempted,
what is checked, what it escalates to — and link to commit-specific benchmark
rows instead of quoting absolute times inline (PERF-2).
*Done when:* neither claim survives, and each replacement links to generated
evidence.

**P0-11 — Fix installation before presenting it as a release command.**
*What is wrong:* The General registry did not contain `AIFloats` at baseline, so
`Pkg.add("AIFloats")` is not a valid clean-user installation.
*What to do:* Document an explicit repository URL, and separately a local
`Pkg.develop(path=...)` workflow. Restore the short registry command only after
it succeeds in a clean depot.
*Done when:* the documented command is verified in a clean depot (Gate 4).

### P1 — public API completeness and clarity

**P1-1 — Replace the unfiltered Reference page.**
`@autodocs Modules=[AIFloats]` simultaneously exposes private machinery
(`get_table`, `table_for`, cache structs and budget helpers, `validformat`, and
similar) and omits public bindings that carry no docstring. Replace it with
curated, categorized `@docs` blocks generated or checked against
`Base.isexported` and `Base.ispublic`. Keep implementation-only carrier material
on `97-internals.md`, marked unstable.
*Done when:* V-3's public-binding assertion passes and no private name appears
in `95-reference.md`.

**P1-2 — Close the public-docstring gap.**
At baseline, 173 public bindings had `Docs.hasdoc(AIFloats, name) == false`: 51
generated scalar operation names, 102 generated `Block*`/`Scaled*` names, and 20
others (`CarrierValue`, eight `Class*` constants, `DyadicNumbers`, `FAST_ARITH`,
`FAST_ENCLOSURE`, `PACK_TILE`, `Sticky`, `formatinfo`, `kappa`,
`kappa_measured`, `round_to_precision`, `saturate`, `vmap`). Document the
operation families from registry metadata rather than writing 153 nearly
identical strings by hand. Attach docs to both `vmap` and `vmap!`. `formatinfo`'s
prose exists in source but an intervening macro detaches it from the binding —
reattach it.
*Done when:* the regenerated inventory (Gate 2) shows every public binding
documented or listed in a reviewed exemption file.

**P1-3 — Document the operation Interface as a family.**
Give the canonical scalar, same-format convenience, array, and projection-first
signatures. Explain result-format selection, accepted operand formats, `rng`/`R`,
refusal modes, and the relationship to the Julia operator veneers. Use
`operations()` and `operationinfo()` in Technical examples so the registry is
discoverable without exposing `OP_REGISTRY`.
*Done when:* V-3 asserts documented operation names and arities equal
`operations()`.

**P1-4 — Teach both permanent query vocabularies.**
The narrative favors `BitwidthOf`/`BinaryFormatOf` and barely mentions the
zero-cost Julia-style bindings `bitwidth`, `formatof`, `signedness`, `domain`,
`codetype`, `valuetype`. State once that each pair names the same generic
function object — not an Adapter, not a compatibility shim — and demonstrate
`formatinfo(F)` as the consolidated inspection API. Include the §5.3 mapping so
no reader infers that every package spelling is quoted from the report.
*Done when:* both vocabularies appear in the query section with the
same-object statement, and the §5.3 table is populated by Gate 0.

**P1-5 — Stop recommending private validation.**
`30-formats.md` tells users to call `AIFloats.validformat`, which is neither
exported nor `public`. Say instead that `Binary` validates and throws. If
non-throwing validation is genuinely required, make a deliberate public-API
decision first; do not create a de facto API in prose.
*Done when:* no page names a non-public binding as a user-facing call.

**P1-6 — Document raw-code versus numeric-value construction early.**
Show a case where results visibly differ, e.g. `fromcode(F, 0x45)` versus
`F(0x45)`. State that every `Integer`, including every `Unsigned`, has value
semantics on constructors and on `Convert`.
*Done when:* V-3 asserts the two documented semantics differ as described.

**P1-7 — Complete the stochastic contract.**
State that `N` is in `1:60`; an explicit `R` must be in `0:(2^N-1)`; `R` takes
precedence when both `R` and `rng` are supplied; omitting both resolves
`Random.default_rng()` only for a stochastic projection. Pure projections do not
touch RNG state. Arrays accept an RNG and consume one sequential stream in
`eachindex` order; they do not expose a per-element `R`.
*Done when:* each clause has an example or a refusal example (Gate 3).

**P1-8 — Qualify rounding motivation.**
Remove or source the unqualified claims that `RTO` is "unbiased," "much cheaper
in hardware," and carries "roughly twice" the error. Do not call all three
finite-budget stochastic variants exactly unbiased without stating the
quantization their formulas induce. Lead with the actual §4.7.4 predicates; put
training motivation in a cited, explicitly non-contractual note (tier 5).
*Done when:* every motivational sentence is either sourced or marked
non-contractual, and no §4.7.4 predicate is paraphrased incorrectly.

**P1-9 — Clarify domain language for unsigned formats.**
A generic `EXTENDED` row must not imply an unsigned format represents negative
reals or `-Inf`. Describe domain *after* signedness: `EXTENDED` adds the
infinities representable under the format's signedness; `FINITE` does not.
*Done when:* the concepts and formats pages order the two traits this way and
the tables agree.

**P1-10 — Document display scope.**
`set_show_style!` changes the process-wide fallback; the local, composable Seam
is an `IOContext` with `:binary_show_style`. Show both, warn library code against
mutating a global display preference, and keep this strictly separate from
task-local numerical projection state.
*Done when:* both mechanisms appear with their scopes named (see the "every
default states its scope" checklist item).

**P1-11 — Expose the recent collection contracts.**
Add concise examples for `Convert(F, A)` resolving the task default once,
portable packed serialization, and `copy`/`similar`/exact-type `copyto!` for
`PackedVector` and `BlockVector`. State axis, copying, padding-validation, and
result-type behavior — not only happy-path output.
*Done when:* each contract has an example that asserts the stated behavior,
including at least one refusal (Gate 3).

**P1-12 — Describe `conformance()` without implying certification.**
The designated report's cover says it is an unapproved draft, subject to change,
and must not be used for conformance or compliance purposes — while §4.6 is
titled "Conformance declarations." Document `ConformanceDeclaration` as a query
*shaped by* that draft section: not IEEE approval, not certification, not a
compliance determination.
*Done when:* every page mentioning conformance carries the unapproved-draft
qualification.

### P2 — maintainability, navigation, and polish

**P2-1 — Standardize notation.** Apply §5.1 across all examples. Remove
redundant calls such as `BinaryFormatOf(Binary8p4se)` and `BinaryFormatOf(T)`
where the format is already in hand; keep `formatof(x)` where genuine recovery is
being taught.

**P2-2 — Consolidate the duplicated format-display section** in `30-formats.md`;
spend the reclaimed space on alias discovery, query vocabulary, and construction
semantics.

**P2-3 — Make every example independent and outcome-checking.** Each block
imports what it uses, defines its inputs, avoids ambient cache/default/show
state, and asserts or doctests the fact it teaches. Restore any global diagnostic
switch in a `finally`.

**P2-4 — Fix README content links.** `docs/make.jl` sets `prettyurls = false`,
so content links must target explicit `.html` files; today they resolve through a
directory/index indirection that breaks locally and on deploy.

**P2-5 — Remove placeholder project metadata.** `README.md:73` still carries a
`FIXME` DOI badge and an incomplete citation claim. Finish `CITATION.cff`; delete
the badge if it tells a user nothing about AIFloats.

**P2-6 — Rewrite the Contributing/Developer pages around this repository:**
Julia 1.12, individual `test/test-*.jl` inclusion, targeted test commands, the
benchmark suites, `AIFLOATS_DOCS_BENCHMARKS=0`, docs environment setup, and the
actual CI jobs. Fix the grammar and release-step typos.

**P2-7 — Replace `docs/make.jl` page recursion with an explicit page tree.**
`recursively_list_pages` is fragile below one level of nesting, and — more
importantly — an explicit tree makes navigation reviewable and stops an internal
planning Markdown file (this one included) from being published by accident.

**P2-8 — Relocate the stray `vmap`/`vmap!` export.** They are exported from the
bottom of `src/arrays/kernels.jl` (line 298) rather than from the module's export
block in `src/AIFloats.jl`, so the module's own header understates its public
surface. Move the export and note the array Seam where the other exports are
listed. *(Source-organization change only; no behavior change.)*

**P2-9 — Make the link check runnable.** V-5 invokes `lychee --config
lychee.toml`, but no `lychee.toml` exists in the repository. Either add the
config (with the ignore rules the P3109 and registry links need) or drop the
flag; do not ship a validation step that cannot run.

## 7. Performance documentation policy

**PERF-1 — Measure a clean, identified tree.** The benchmark output at baseline
names commit `89195ba (dirty)`, which is older than the audited source; treat it
as historical evidence only. Run `benchmark/runbenchmarks.jl` from a clean
commit, only after correctness and documentation edits settle — never as part of
ordinary prose editing.

**PERF-2 — Absolute numbers live on the generated page only.** In README and
Status, prefer durable relationships ("a warm table gather avoids scalar
recomputation"; "rung-2 K=16 decode is slower than K=12") and link to exact rows.
Performance prose must never become a second, hand-maintained benchmark report.

**PERF-3 — Thresholds are named, not transcribed.** When a threshold is
justified by a measurement, name the threshold and its source constant
(`TABLE_ADAPTIVE_BITS`, `TABLE_BUILD_ELEMS`), and generate or test its value
rather than copying the number onto several pages.

**PERF-4 — Retire the packed "about 3x" claim.** The recorded Negate and Exp
ratios are about 1.22x and 1.42x on that run. Prefer "bit extraction adds cost;
measure retained size and throughput together."

**PERF-5 — Retire the stale load/first-call figures** (~57 ms; "all block
reductions sub-millisecond"). The recorded page reports 66.52 ms, and 2.04 ms for
the first block reduction on its machine. Restate under PERF-2.

**PERF-6 — State the Float128 correctness boundary prominently.**
`Quadmath.Float128` is a value/carrier type; libquadmath elementary functions are
not assumed correctly rounded. AIFloats accepts such a result only under a
proof/enclosure check and otherwise escalates to the rigorous MPFR interval
ladder. The pure-Julia `fma128`/`faa128` routines carry their own documented
guarantees and should be described separately.

## 8. Page-by-page realization

| Location | Required result | Owning items |
|:--|:--|:--|
| `README.md` | Valid installation; exact report version/digest with the unapproved-draft qualification; explicit `.html` links; performance summary linked to generated evidence; no placeholder badges | P0-1, P0-11, P1-12, P2-4, P2-5, PERF-2 |
| `docs/src/index.md` | One accurate package promise, the designated-report identity, and a task-oriented route: formats → datums → projections → operations → storage | P0-1, P0-4 |
| `10-getting-started.md` | First successful format/datum calculation; the actual `RTE_SN` default; the value/code distinction; lower-case queries introduced without overload | P0-3, P0-4, P1-4, P1-6 |
| `20-concepts.md` | Correct implicit-bit and exponent-bit algebra; signedness-aware domains; format names described as formats | P0-2, P0-4, P1-9 |
| `30-formats.md` | The canonical `F`/`T`/`x` model; aliases and `Formats`; paired queries and `formatinfo`; no private validator; one display section | P0-4, P1-4, P1-5, P2-2 |
| `40-projections.md` | Exact mode predicates and saturation outcomes; actual defaults; task-local binding; the RNG contract; qualified motivation; the §5.3 name map | P0-3, P0-6, P1-7, P1-8 |
| new operations page | Registry families; scalar and array signatures; Base veneers; conversions and refusals; the exact/enclosure correctness path | P1-3, PERF-6 |
| `50-status.md` | The supported contract and deliberate limits; correct binary/ternary table policy and block paths; volatile performance facts removed or generated | P0-9, P0-10, P1-12, PERF-2 |
| `60-benchmarks.md` | Generated only; commit, machine, environment, and cache state recorded; no hand-entered duplicate elsewhere | PERF-1, PERF-2 |
| Basic examples | Format, datum type, construction, code/value distinction, arithmetic, inspection, explicit conversion | P0-4, P1-6, P2-1 |
| Intermediate examples | Projection comparisons; a genuinely differentiating saturation case; task-local defaults; the full stochastic contract; arrays and broadcasts | P0-3, P0-6, P1-7 |
| Advanced examples | Packed wire forms and copying; different-width and different-precision block formats; exact fast-path guards versus exact fallback, without promising a specific carrier | P0-10, P1-11 |
| Technical examples | Public `formatinfo`, `operationinfo`, `table_policy`, cache snapshots, diagnostics with restoration, conformance; no private cache builder | P0-7, P0-8, P1-3, P1-12 |
| `95-reference.md` | Curated, complete public API, categorized and mechanically checked; no incidental private docstrings | P1-1, P1-2 |
| `97-internals.md` | Explicitly unstable implementation notes with provenance; not mixed into the public Reference | P1-1 |
| source docstrings | Same terminology and contracts as the narrative pages; no stale instance, default, snapshot, or performance statements | P0-2, P0-5, P1-2 |
| `docs/make.jl` | Explicit page tree; planning documents unpublishable by construction | P2-7 |

## 9. Execution gates

Gates are sequential. A gate's exit condition is its definition of done.

### Gate 0 — pin and compare the normative report

- Download the PDF from the designated P3109 Public URL; record cover version,
  date, and SHA-256 in the audit evidence.
- Build a semantic delta matrix by report section, covering at least §§3,
  4.1–4.7, 5, and every annex cited by package prose or code. Compare the PDF
  against `src/`, the tests, the current docs, and `docs/other/IEEE_D1.md`
  (as a comparison subject only, per §4.2).
- Classify each delta: documentation-only, implementation defect, unsupported
  report feature, intentional Julia extension, or report ambiguity. A Julia
  extension must be labeled as such and never attributed to the report.
- Populate the §5.3 name-mapping table from this matrix.
- Settle no ambiguity with an outside IEEE source (§4.1). Escalate it for a
  maintainer decision and record the interpretation in the package only after
  that decision.

*Exit:* every normative claim in the backlog cites a specific location in the
designated PDF, and the package makes no unverified claim to implement version
4.0.3.

### Gate 1 — one vocabulary, no false statements

- Complete every P0 item in the narrative pages and source docstrings.
- Add the operations page and update navigation explicitly (P2-7 may land here).
- Run focused Julia probes for every corrected outcome.
- Change no operation algorithm to make old prose true (§1).

*Exit:* no known statement contradicts the designated report, the
exported/`public` surface, a focused probe, or the current table and block
implementation. Every source/report disagreement is either resolved in source or
plainly listed as unsupported. `draft_identity()` is evidence, never an override.

### Gate 2 — a complete, deep public Reference

- Regenerate the inventory with `Base.isexported`, `Base.ispublic`, and
  `Docs.hasdoc`; replace the §3 baseline counts with current ones.
- Attach family-level docs to the generated operations (P1-2, P1-3) and close the
  remaining individual gaps.
- Replace the unfiltered `@autodocs` with categorized public lists (P1-1).
- Move implementation discussion to Internals rather than widening the public
  Interface. Where an expert control stays `public`, document its stability,
  scope, thread behavior, and failure modes.

*Exit:* every exported/`public` binding is documented or listed in a reviewed,
explicit exemption file, and no private binding appears in the public Reference.

### Gate 3 — rebuild the learning path and examples

- Apply the `F`/`T`/`x` convention; remove all state sharing between examples.
- Make each example prove its point with distinct results and assertions.
- Add refusal examples where they prevent silent misuse: `F()`; out-of-range
  `fromcode`; `Rational` conversion; unsigned negative input; mismatched array
  axes; packed padding; stochastic `R` bounds.
- Keep Basic shallow; policy and diagnostic controls belong only in Technical.

*Exit:* every example runs standalone in a fresh Julia 1.12 session, and every
important output is checked rather than merely printed.

### Gate 4 — consolidate performance and project metadata

- Regenerate benchmark output from the clean implementation commit (PERF-1).
- Rewrite Status and README performance prose from those results without copying
  a volatile table (PERF-2).
- Verify installation from a clean depot (P0-11), then verify every external link
  (V-5, P2-9).
- Complete citation metadata (P2-5) and developer instructions (P2-6).

*Exit:* the documented installation succeeds, generated measurements identify the
measured tree, and no placeholder or dead navigation remains.

## 10. Validation

**Do not run the full package test suite for this documentation refinement.**
`Pkg.test()` is out of scope for every gate.

**V-1 — Source docstring doctests.**

```bash
julia --project=docs -e 'using Documenter: DocMeta, doctest; using AIFloats; DocMeta.setdocmeta!(AIFloats, :DocTestSetup, :(using AIFloats); recursive=true); doctest(AIFloats)'
```

**V-2 — Docs build with benchmarks disabled.**

```bash
AIFLOATS_DOCS_BENCHMARKS=0 julia --project=docs docs/make.jl
```

Change the builder so a skipped build does not overwrite the last generated
benchmark source page.

**V-3 — Documentation-contract test.** A small test file asserting:

| Assertion | Guards |
|:--|:--|
| `DefaultProjection() === RTE_SN` | P0-3 |
| `ExponentBitwidthOf(Binary8p4sf) == 4`, unsigned analogue `== 5` | P0-2 |
| Format aliases are format types; `BinaryValue(F)` is the datum type | P0-4 |
| `fromcode(F, c)` and `F(c)` have the documented distinct semantics | P1-6 |
| `get_table` is not public; `table_policy`, `table_stats`, `table_entries` are | P0-7 |
| Every public binding has documentation or a reviewed exemption | P1-1, P1-2 |
| Documented operation names and arities equal `operations()` | P1-3 |

**V-4 — Example isolation.** Execute each Examples block in a fresh module — not
merely in Documenter's shared named block — and fail on unexpected output or
leaked global state.

**V-5 — Link check.** Run `lychee` over the repository after the `.html`, P3109
PDF, registry/install, citation, and source links are finalized. Resolve P2-9
first so the command is runnable as documented.

**V-6 — Focused source tests only.** When a docstring change is paired with a
contract test, run only the directly affected files — for example
`test-binary-format.jl`, `test-traits.jl`, `test-projection.jl`, `test-ops.jl`,
`test-tables.jl`, `test-kernels.jl`, `test-blocks.jl`.

## 11. Acceptance checklist

Answer each question "yes" before declaring the work complete.

**Ground truth**
- Does every normative P3109 claim trace to a specific location in the designated
  Interim Report PDF, with no other IEEE reference used anywhere?
- Is every package-specific spelling, extension, and interpretation labeled as
  such rather than attributed to the report?
- Does each numeric guarantee say whether it is normative, proven, tested, or
  measured?

**Concepts**
- Can a new reader distinguish a format, a datum type, a datum, a decoded value,
  and a code point after Getting Started?
- Does every default state its scope: package-wide, process-wide, task-local,
  per-IO, per-call, or RNG-local?
- Do the saturation and stochastic examples visibly distinguish the behaviors
  they claim to teach?

**Interface**
- Are the public Seams documented, and are private implementation details absent
  from the user Reference?
- Is every exported or `public` binding documented or explicitly exempted?

**Evidence**
- Does each benchmark claim identify or link to its empirical evidence?
- Are all Float128 statements compatible with libquadmath elementary functions
  not being assured correctly rounded?

**Mechanics**
- Do all examples run in isolation on the declared Julia 1.12 floor?
- Are the installation, citation, repository, source, and `.html` links live?
- Does a clean documentation build leave no unexplained source-tree changes?
