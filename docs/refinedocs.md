# Documentation refinement plan

## Purpose

Make the documentation a faithful, verifiable Interface to AIFloats.jl 0.2.x.
After this work, a reader should be able to move from format definition to
datum construction, projection, scalar and array operations, packed storage,
blocks, performance policy, and conformance without encountering a spelling,
default, example, or performance claim that disagrees with the package.

This is a documentation plan, not an authorization to change numerical
semantics. If a documentation audit exposes a source-code defect, record it as
a source issue and resolve the code-versus-draft question before rewriting the
documentation around it.

Audit baseline: package version 0.2.0, `main` at `2b7893e`, on 2026-09-01. The
working tree also contained an uncommitted constructor fast-path edit in
`src/ops/scalar.jl`; consequently, no committed benchmark page should be
described as measuring the exact audited tree. The normative report pinned for
this review is version 4.0.3, dated 2026-09-01, with downloaded PDF SHA-256
`7de115ed6882b7550b8fa61e81e5173857b340c3bfe30db8d4ad74b472229b9e`.

## Truth hierarchy

Every statement should identify, at least implicitly, which kind of truth it
is:

1. **Normative semantics:** solely the user-designated [IEEE Working Group P3109
   Interim Report on Arithmetic Formats for Machine
   Learning](https://github.com/P3109/Public/blob/main/IEEE%20P3109%20Interim%20Report.pdf).
   For this audit that is version 4.0.3, dated 2026-09-01. No other IEEE page,
   earlier draft, local transliteration, source comment, or test expectation can
   override it.
2. **Package contract:** exported and `public` bindings, their methods,
   docstrings, and targeted tests. Private names are implementation details even
   if they happen to have docstrings.
3. **Observed behavior:** executable examples and focused Julia probes against
   the current tree.
4. **Performance:** a Chairmarks result tied to a commit, Julia version, thread
   count, CPU, inputs, and cache state. Performance prose must not become a
   second, hand-maintained benchmark report.
5. **Motivation or general numerical advice:** externally sourced and qualified;
   do not present a broad claim about hardware, training, or statistical bias as
   an AIFloats guarantee.

The repository's `docs/other/IEEE_D1.md`, `draft_identity()`, implementation,
and tests are comparison subjects, not normative authorities. A mechanical text
extraction may help locate report sections, but citations and final semantic
decisions must refer to the PDF itself. If the PDF changes at the stable URL,
repeat the comparison and record the new version, date, and digest.

This separation gives the documentation Module depth: the public Interface
states stable concepts and contracts, while carrier selection, cache keys,
proof guards, and enclosure rungs remain behind explicit expert Seams. It also
improves Locality: a default, threshold, or operation inventory should have one
authoritative statement and links from every other page.

## Confirmed high-priority corrections

### P0 — correctness blockers

1. **Reconcile the package's claimed draft identity with the designated
   report.** `draft_identity()` currently names “IEEE P3109/D1, uploaded
   2026-07-17” and a local Markdown transliteration. The designated report's
   introduction also uses the D1 designation, but its cover identifies the
   current revision as Interim Report version 4.0.3 dated 2026-09-01. Before
   claiming that the package implements that revision, produce a
   section-by-section semantic delta for every implemented format, projection,
   scalar operation, block operation, and conformance-declaration rule. Open
   source defects for every disagreement. Only after those are resolved should
   `draft_identity()`, its revision/date/digest fields, README, Status, and
   conformance output be updated to identify the report precisely. Do not
   relabel old behavior as current compliance by prose alone.

2. **Repair the bit-budget derivation.** `docs/src/20-concepts.md` correctly
   starts with

   ```text
   K = S + exponent bits + (P - 1)
   ```

   but incorrectly rearranges it as `K - P - S`. The correct exponent-bit count
   is `K - S - (P - 1)`, equivalently `K - P - S + 1`. Therefore
   `Binary(8,4,SIGNED,...)` has 4 exponent bits and its unsigned counterpart has
   5, not 3 and 4. Correct the prose, examples, and comparison table. Correct
   the same omitted `+1` in the `PrecisionOf` docstring in
   `src/types/binaryformats.jl`. Add executable checks against
   `ExponentBitwidthOf` so this foundational explanation cannot drift again.

3. **State the actual default projection.** `DefaultProjection()` is initially
   `RTE_SN`, task-local through `ScopedValue`. Replace claims in
   `10-getting-started.md`, `40-projections.md`, and the `RTE_SF` docstring that
   call `RTE_SF` the conventional or package default. Keep distinct defaults
   explicit: ordinary construction/arithmetic uses `RTE_SN`; `rand` defaults to
   `RTZ_SN`; `randn` defaults to `RTE_SF`.

4. **Correct the format/datum alias description.** The capital names such as
   `Binary8p4se` are format types, not “datum aliases.” Explain the canonical
   triad once and reuse it everywhere:

   ```julia
   F = Binary8p4se       # format type
   T = BinaryValue(F)    # concrete AbstractFloat datum type
   x = F(1.5)            # datum/value
   ```

   State that `F()` is deliberately invalid, `F(x)` consumes a numeric value,
   and `fromcode(F, c)` consumes a raw code point.

   Also add an explicit terminology map. In Interim Report §3.1, a
   “floating-point datum” is the mathematical element and a “floating-point
   value” is its code point in an associated format. In Julia, `BinaryValue` is
   the concrete `AbstractFloat` object that stores that code point and behaves
   numerically as the datum. Do not silently use “value” in both senses in the
   same explanation.

5. **Fix contradictory constructor docstrings.** In
   `src/types/binaryformats.jl`, remove “Append `()` when you need a value” from
   `Binary`; it directly contradicts both the implementation and the following
   paragraph. Remove claims that `CodeType` and `ValueType` accept a `Binary`
   instance. In `src/types/binaryvalue.jl`, replace “session default” with
   “task-local default” and remove committed phase/temporary-diagnostic comments
   that no longer describe the delivered Interface.

6. **Make the saturation example distinguish the modes.** The Intermediate
   example currently projects finite `1.0e100` with `RTE_SF` and `RTE_SP`; both
   correctly clamp to the same largest finite datum. Use `Inf` in an extended
   format to show the defining difference: `SF` clamps a genuine infinity,
   while `SP` propagates a representable infinity. Add a small semantics table:
   `SF` clamps all out-of-range results including infinities; `SP` propagates
   only representable input infinity and clamps finite overflow; `SN` follows
   rounding direction, signedness, and domain and can yield an extremal finite,
   infinity, or NaN.

7. **Remove the private cache call from Technical examples.** `get_table` is
   deliberately neither exported nor `public` in 0.2.0. Populate a table through
   the public `vmap`/`vmap!` Seam and inspect it with `table_stats()` and
   `table_entries()`. The second `technical_cache` block must also include
   `using AIFloats`; it currently relies on state from an earlier block and is
   the one Examples block that is not self-contained.

8. **Do not claim two independent cache snapshots are one moment.** Each of
   `table_stats()` and `table_entries()` is coherent under its own lock, but two
   separate calls can observe different moments. Say that entry bytes equal a
   separately obtained `table_stats().bytes` only when the cache is not mutated
   between calls. Where one coherent count-and-byte declaration is required,
   point to `conformance()`, which derives its byte total from its captured entry
   vector.

9. **Repair the table-policy description.** `50-status.md` says signatures above
   the eager unary/binary band always compute and describes adaptivity only for
   ternary tables. Current source also has a binary adaptive band:
   `TABLE_ADAPTIVE_BITS[] == 18` and `TABLE_BUILD_ELEMS[] == 1_000_000`.
   Document eager, binary-adaptive, ternary-adaptive, byte-refusal, stochastic,
   and beyond-band outcomes from `table_policy`, without teaching private cache
   builders.

10. **Correct stale block and decoding performance statements.** Current
   `BlockReduceMultiply` has a checked exact `Dyadic` fast path; it does not
   “always” use `BigFloat`. K=16 rung-2 decoding is materially slower than the
   blanket “wider formats ~3 ns” claim. Replace both with the guard/fallback
   contract and link to commit-specific rows.

11. **Fix installation before presenting it as a release command.** The official
    General registry did not contain `AIFloats` at audit time, so
    `Pkg.add("AIFloats")` is not presently a valid clean-user installation.
    Until registration is verified, document an explicit repository URL and,
    separately, a local `Pkg.develop(path=...)` workflow. Restore the short
    registry command only after it succeeds in a clean depot.

### P1 — public API completeness and clarity

1. **Replace the unfiltered Reference page.** `@autodocs Modules=[AIFloats]`
   simultaneously exposes private machinery (`get_table`, `table_for`, cache
   structs and budget helpers, `validformat`, and similar names) and omits public
   bindings without attached docstrings. Replace it with curated, categorized
   `@docs` blocks generated or checked against `Base.isexported` and
   `Base.ispublic`. Keep implementation-only carrier material on
   `96-internals.md`, marked unstable.

2. **Close the public-docstring gap.** The audit found 173 public bindings for
   which `Docs.hasdoc(AIFloats, name)` is false: 51 generated scalar operation
   names, 102 generated `Block*`/`Scaled*` operation names, and 20 other names
   (`CarrierValue`, eight `Class*` constants, `DyadicNumbers`, `FAST_ARITH`,
   `FAST_ENCLOSURE`, `PACK_TILE`, `Sticky`, `formatinfo`, `kappa`,
   `kappa_measured`, `round_to_precision`, `saturate`, and `vmap`). Document
   operation families from registry metadata rather than copying 153 nearly
   identical hand-written strings. Attach docs to both `vmap` and `vmap!`.
   The `formatinfo` prose exists in source but is not attached to the binding
   because of the intervening macro; attach it correctly.

3. **Document the operation Interface as a family.** Give the canonical scalar,
   same-format convenience, array, and projection-first signatures; explain
   result-format selection, accepted operand formats, `rng`/`R`, refusal modes,
   and the relationship to Julia operator veneers. Use `operations()` and
   `operationinfo()` in Technical examples so the registry is discoverable
   without exposing `OP_REGISTRY`.

4. **Teach both permanent query vocabularies.** The narrative currently favors
   `BitwidthOf`/`BinaryFormatOf` and barely mentions the zero-cost Julia-style
   bindings `bitwidth`, `formatof`, `signedness`, `domain`, `codetype`, and
   `valuetype`. Explain once that each pair is the same generic function object,
   not an Adapter or compatibility shim. Demonstrate `formatinfo(F)` as the
   consolidated inspection API.

   Include a normative-name mapping rather than implying that every package
   spelling comes directly from the report. For example, §4.5 names
   `TrailingSignificandBitwidthOf`, while the package currently exports
   `TrailingSignificantBitsOf`; this is a source/API delta to classify, not a
   typographical difference for prose to hide.

5. **Stop recommending private validation.** `30-formats.md` tells users to call
   `AIFloats.validformat`, although it is neither exported nor `public`. Say that
   `Binary` validates and throws. If non-throwing validation is truly required,
   make a deliberate public API decision first; do not create a de facto API in
   prose.

6. **Document raw-code versus numeric-value construction near the beginning.**
   Include an example where the results visibly differ, such as
   `fromcode(F, 0x45)` versus `F(0x45)`. State that every `Integer`, including
   every `Unsigned`, has value semantics on constructors and `Convert`.

7. **Complete the stochastic contract.** Explain that `N` is in `1:60`, an
   explicit `R` must be in `0:(2^N-1)`, `R` takes precedence when both `R` and
   `rng` are supplied, and omission of both resolves `Random.default_rng()` only
   for a stochastic projection. Pure projections do not touch RNG state. Arrays
   accept an RNG and consume one sequential stream in `eachindex` order; they do
   not expose per-element `R`.

8. **Qualify rounding motivation.** Remove or source unqualified claims that
   `RTO` is “unbiased,” “much cheaper in hardware,” and has “roughly twice” the
   error. Do not describe all three finite-budget stochastic variants as exactly
   unbiased without stating the quantization induced by their formulas. Describe
   their actual Interim Report §4.7.4 predicates first; put training motivation
   in a cited, explicitly non-contractual note.

   Map AIFloats names to the report's names. For example, the report says
   `NearestTiesToEven`, `NearestTiesToAway`, and `ToOdd`; AIFloats displays
   `RoundToEven`, `RoundToAway`, and `RoundToOdd`. Label the latter as package
   long names, not verbatim report terminology. Do not infer a general report
   “default projection” from §4.5's required specializations under
   `(NearestTiesToEven, SatNone)`; `RTE_SN` is the package's task-local default.

9. **Clarify domain language for unsigned formats.** A generic `EXTENDED` row
   should not imply that an unsigned format represents negative reals or `-Inf`.
   Describe domain after signedness: `EXTENDED` adds the infinities representable
   under the format's signedness; `FINITE` does not.

10. **Document display scope.** `set_show_style!` changes the process-wide
    fallback. The local, composable Seam is an `IOContext` with
    `:binary_show_style`. Show both, warn library code against mutating a global
    display preference, and keep this separate from task-local numerical
    projection state.

11. **Expose recent collection contracts.** Add concise examples for
    `Convert(F, A)` resolving the task default once, portable packed
    serialization, and `copy`/`similar`/exact-type `copyto!` for `PackedVector`
    and `BlockVector`. State axis, copying, padding-validation, and result-type
    behavior rather than only showing happy-path output.

12. **Describe `conformance()` without implying certification.** The designated
    report's cover says that it is an unapproved draft, subject to change, and
    must not be used for conformance/compliance purposes. The report nevertheless
    contains §4.6, “Conformance declarations.” Document AIFloats'
    `ConformanceDeclaration` as a query shaped by that draft section, not as IEEE
    approval, certification, or a compliance determination.

### P2 — maintainability, navigation, and polish

1. Standardize notation across examples: `F` is a format, `T` a datum type, `x`
   a datum, `c` a code point, and `ρ`/`p` a projection. Remove redundant calls
   such as `BinaryFormatOf(Binary8p4se)` and `BinaryFormatOf(T)` when the format
   is already in hand; retain `formatof(x)` to teach genuine recovery.
2. Consolidate the duplicated format-display section in `30-formats.md` and use
   the space for alias discovery, query vocabulary, and construction semantics.
3. Make every example independent and outcome-checking. Each block should import
   what it uses, define all inputs, avoid ambient cache/default/show state, and
   include an assertion or doctested output for the fact being taught. Restore
   any global diagnostic switch in `finally`.
4. Update README content-page links to explicit `.html` targets, consistent with
   `prettyurls=false`, so local and deployed clicks open the page rather than a
   directory/index indirection.
5. Remove the `FIXME` DOI badge and incomplete citation claim until real metadata
   exists. Finish `CITATION.cff`; remove the template badge if it no longer tells
   users anything about AIFloats.
6. Rewrite the generic Contributing/Developer pages around this repository:
   Julia 1.12, individual `test/test-*.jl` inclusion, targeted test commands,
   benchmark suites, `AIFLOATS_DOCS_BENCHMARKS=0`, docs environment setup, and
   the actual CI jobs. Correct grammar and release-step typos.
7. Make `docs/make.jl` recursion robust for nesting deeper than one directory,
   or replace it with an explicit page tree. An explicit tree is preferable here:
   it makes navigation reviewable and prevents an internal planning Markdown
   file from becoming a published page accidentally.

## Page-by-page realization

| Location | Required result |
|:--|:--|
| `README.md` | Valid installation; exact Interim Report version/digest and unapproved-draft qualification; explicit `.html` links; performance summary linked to generated evidence; no placeholder badges |
| `docs/src/index.md` | One accurate package promise, designated-report identity, and a task-oriented route through formats → datums → projections → operations → storage |
| `10-getting-started.md` | First successful format/datum calculation; actual `RTE_SN` default; value/code distinction; lower-case queries introduced without overload |
| `20-concepts.md` | Correct implicit-bit and exponent-bit algebra; signedness-aware domains; format names described as formats |
| `30-formats.md` | Canonical `F`/`T`/`x` model; aliases and `Formats`; paired queries and `formatinfo`; no private validator recommendation; one display section |
| `40-projections.md` | Exact mode predicates and saturation outcomes; actual defaults; task-local binding; RNG contract; qualified motivation |
| new operations page | Registry families, scalar and array signatures, Base veneers, conversions/refusals, exact/enclosure correctness path |
| `50-status.md` | Supported contract and deliberate limits, with volatile performance facts removed or generated; correct binary/ternary table policy and block paths |
| `60-benchmarks.md` | Generated only; commit/machine/environment/cache state; no hand-entered duplicate claims elsewhere |
| Basic examples | Format, datum type, construction, code/value distinction, arithmetic, inspection, explicit conversion |
| Intermediate examples | Projection comparisons, a genuinely differentiating saturation case, task-local defaults, full stochastic contract, arrays and broadcasts |
| Advanced examples | Packed wire forms and copying; different-width/different-precision block formats; exact fast-path guards versus exact fallback without promising a specific carrier |
| Technical examples | Public `formatinfo`, `operationinfo`, `table_policy`, cache snapshots, diagnostics with restoration, conformance; no private cache builder |
| `95-reference.md` | Curated complete public API, categorized and mechanically checked; no incidental private docstrings |
| `96-internals.md` | Explicitly unstable implementation notes with provenance; not mixed into the public Reference |
| source docstrings | Same terminology and contracts as narrative pages; no stale instance, default, snapshot, or performance statements |

## Performance documentation policy

The benchmark output at audit time names commit `89195ba (dirty)`, while the
audited source is later. Treat it as historical evidence only.

1. Run `benchmark/runbenchmarks.jl` only after correctness/documentation edits
   settle and from a clean commit. Do not run it as part of ordinary prose
   editing.
2. Keep absolute values on the generated page. In README and Status, prefer
   durable relationships (“warm table gather avoids scalar recomputation,”
   “rung-2 K=16 decode is slower than K=12”) and link to exact rows.
3. If a threshold is justified by a measurement, name the threshold and its
   source constant, but generate or test the default value rather than copying
   it into several pages.
4. Replace the stale packed “about 3x” statement: the recorded Negate and Exp
   ratios are about 1.22x and 1.42x on that run. Prefer “bit extraction adds
   cost; measure retained-size and throughput together.”
5. Replace stale load/first-call values (~57 ms and all block reductions
   sub-millisecond); the recorded page reports 66.52 ms and 2.04 ms for the
   first block reduction on its machine.
6. State the Float128 correctness boundary prominently. `Quadmath.Float128` is
   a value/carrier type; libquadmath elementary functions are not assumed to be
   correctly rounded. AIFloats may accept a result only under a proof/enclosure
   check and otherwise escalates to the rigorous MPFR interval ladder. The
   pure-Julia `fma128`/`faa128` routines have their own documented guarantees.

## Implementation sequence

### Gate 0 — pin and compare the normative report

- Download the PDF from the user-designated P3109 Public URL; record its cover
  version/date and SHA-256 in the audit evidence.
- Build a semantic delta matrix by report section, with at least §§3, 4.1–4.7,
  5, and every annex cited by package prose or code. Compare the PDF to
  `docs/other/IEEE_D1.md`, `src/`, tests, and current docs.
- Classify each delta as documentation-only, implementation defect, unsupported
  report feature, intentional Julia extension, or report ambiguity. A Julia
  extension must be labeled as such and must not be attributed to the report.
- Do not use another IEEE source to settle a conflict. Escalate an ambiguity for
  a maintainer decision and record the interpretation in the package only after
  that decision.

Exit condition: every normative claim in the remediation backlog cites a
specific location in the designated PDF, and the package makes no unverified
claim to implement version 4.0.3.

### Gate 1 — establish one vocabulary and fix false statements

- Correct all P0 items in narrative pages and source docstrings.
- Add the missing operations page and update navigation explicitly.
- Run focused Julia probes for every corrected outcome.
- Do not alter operation algorithms merely to make old prose true.

Exit condition: no known statement contradicts the designated Interim Report,
the exported or `public` surface, a focused probe, or the current table/block
implementation. Any source/report disagreement is resolved in source or plainly
listed as unsupported; `draft_identity()` is evidence to audit, not an override.

### Gate 2 — make the public Reference complete and deep

- Generate an inventory with `Base.isexported`, `Base.ispublic`, and
  `Docs.hasdoc`.
- Attach family-level docs to generated operations and close the 20 remaining
  individual gaps.
- Replace unfiltered `@autodocs` with categorized public lists.
- Move implementation discussion to Internals rather than widening the public
  Interface. Where an expert control remains `public`, document its stability,
  scope, thread behavior, and failure modes.

Exit condition: every exported/`public` binding is either documented or listed
in a reviewed, explicit exemption file; no private binding appears in the public
Reference accidentally.

### Gate 3 — rebuild the learning path and examples

- Apply the `F`/`T`/`x` convention and remove state-sharing between examples.
- Make examples prove their teaching point with distinct results and assertions.
- Add negative/refusal examples where they prevent silent misuse: `F()`;
  out-of-range `fromcode`; Rational conversion; unsigned negative input;
  mismatched array axes; packed padding; stochastic `R` bounds.
- Keep Basic shallow; place policy and diagnostic controls only in Technical.

Exit condition: every example can be copied into a fresh Julia 1.12 session and
run independently, and every important output is checked rather than merely
printed.

### Gate 4 — consolidate performance and project metadata

- Regenerate benchmark output from the clean implementation commit.
- Rewrite Status/README performance prose from those results without copying a
  volatile table.
- Verify installation from a clean depot, then verify every external link.
- Complete citation metadata and developer instructions.

Exit condition: the documented installation succeeds, generated measurements
identify the measured tree, and no placeholder or dead navigation remains.

## Targeted validation only

Do not run the full package test suite for this documentation refinement.

1. Run source docstring doctests:

   ```bash
   julia --project=docs -e 'using Documenter: DocMeta, doctest; using AIFloats; DocMeta.setdocmeta!(AIFloats, :DocTestSetup, :(using AIFloats); recursive=true); doctest(AIFloats)'
   ```

2. Build the docs with benchmarks disabled:

   ```bash
   AIFLOATS_DOCS_BENCHMARKS=0 julia --project=docs docs/make.jl
   ```

   Prefer changing the builder so a skipped build does not overwrite the last
   generated benchmark source page.

3. Add a small documentation-contract test that asserts:

   - `DefaultProjection() === RTE_SN`;
   - `ExponentBitwidthOf(Binary8p4sf) == 4` and the unsigned analogue is 5;
   - format aliases are format types and `BinaryValue(F)` is the datum type;
   - `fromcode(F,c)` and `F(c)` have the documented distinct semantics;
   - `get_table` is not public while `table_policy`, `table_stats`, and
     `table_entries` are;
   - every public binding has documentation or a reviewed exemption;
   - documented operation names and arities equal `operations()`.

4. Execute each Examples block in a fresh module (not merely in Documenter's
   shared named block) and fail on unexpected output or leaked global state.
5. Run `lychee --no-progress --config lychee.toml .` after the `.html`, P3109
   Public PDF, registry/install, citation, and source links are finalized.
6. Run only directly affected focused tests, for example
   `test-binary-format.jl`, `test-traits.jl`, `test-projection.jl`,
   `test-ops.jl`, `test-tables.jl`, `test-kernels.jl`, or `test-blocks.jl`, when a
   source docstring change is accompanied by a contract test. Do not use
   `Pkg.test()` for this pass.

## Final review checklist

- Can a new reader distinguish a format, datum type, datum, decoded value, and
  code point after Getting Started?
- Does every default say whether it is package-wide, process-wide, task-local,
  per-IO, per-call, or RNG-local?
- Does each numeric guarantee say whether it is normative, proven, tested, or
  measured?
- Does every normative P3109 claim trace to the designated Interim Report PDF,
  with no other IEEE reference used as a substitute?
- Are all Float128 statements compatible with the fact that Quadmath elementary
  functions are not assured correctly rounded?
- Do saturation and stochastic examples visibly distinguish the behaviors they
  claim to teach?
- Are public Seams documented and private implementation details absent from the
  user Reference?
- Does each benchmark claim identify or link to its empirical evidence?
- Do all examples work in isolation on the package's declared Julia 1.12 floor?
- Are installation, citation, repository, source, and `.html` links live?
- Does a clean documentation build leave no unexplained source-tree changes?

The work is complete only when these questions all answer “yes.”
