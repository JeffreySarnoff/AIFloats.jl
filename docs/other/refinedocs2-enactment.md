# refinedocs2 enactment record

What was done for each item of `docs/refinedocs2.md`, and how it is checked.
`V-3` means `test/test-doc-contracts.jl`.

**Baseline:** package 0.2.0 at `d68a8ba`. Normative source: the designated
Interim Report PDF, version 4.0.3, 2026-09-01, SHA-256
`7de115ed…9b9c` — see `docs/other/p3109-delta.md`. No other IEEE document was
consulted.

## Gate 0 — pin and compare

Done. `docs/other/p3109-delta.md` records the pinned PDF, the §3 / §4.2 / §4.5 /
§4.6 / §4.7.4 / §4.7.5 comparison, and the classification of every delta.
**No implementation defects (`SRC`) were found.** One API delta —
`TrailingSignificandBitwidthOf` (report) versus `TrailingSignificantBitsOf`
(package) — is recorded and documented rather than silently smoothed over.

## Gate 1 — P0

| Item | Done | Checked by |
|:--|:--|:--|
| P0-1 draft identity | `DRAFT_IDENTITY` now carries the report's revision, date, URL, and PDF digest beside the retained transliteration; `draft_revision()` and `conformance_report` state the unapproved-draft status | V-3, `test-governance.jl` |
| P0-2 bit budget | `20-concepts.md` and the `PrecisionOf` docstring corrected to `(K - S) - (P - 1)`; tables show 4 and 5 exponent bits and the bias | V-3 (all 504 formats) |
| P0-3 default projection | `RTE_SN` stated in getting-started, projections, and the `RTE_SF` docstring; `rand`/`randn` defaults tabulated | V-3 |
| P0-4 alias description | `F` / `T` / `x` triad on `30-formats.md`, referenced from concepts and getting-started; report datum/value vocabulary explained | V-3 |
| P0-5 constructor docstrings | "append `()`" removed; `CodeType`/`ValueType` no longer claim an instance method; "session default" → "task-local default" across `src/`; the phase-diagnostic comment rewritten as durable rationale | doctests |
| P0-6 saturation example | Intermediate now shows `SF` vs `SP` on `Inf`, plus an `SN` table covering signed/unsigned/finite | V-3 |
| P0-7 private cache call | `get_table` removed from the examples; the table is built through `vmap` | V-3 |
| P0-8 cache snapshots | The cross-call coherence claim is gone; `conformance()` named as the coherent path | V-3 |
| P0-9 table policy | All seven `table_policy` states documented; the **binary** adaptive band stated | V-3 |
| P0-10 block/decode prose | `BlockReduceMultiply`'s guarded path described; the blanket "wider ≈ 3 ns" replaced by a pointer to the benchmark rows | — |
| P0-11 installation | Repository URL and `Pkg.develop`; the registry command marked as future | verified: not in the General registry |

Also found and fixed while checking: a `BinaryValue` doctest asserting `64.0`
where the projected value is `72.0`.

## Gate 2 — the public reference

| Item | Done |
|:--|:--|
| P1-1 | `@autodocs Modules=[AIFloats]` replaced by four pages generated in `docs/make.jl` from `Base.isexported`/`Base.ispublic`, with `checkdocs = :public`. Split because 154 generated family docstrings pushed one page past 700 KiB. |
| P1-2 | 173 → **0** undocumented public bindings. 51 scalar and 102 `Block*`/`Scaled*` docstrings are generated from registry rows; the other 20 hand-written. `formatinfo`'s docstring reattached across `Base.@assume_effects`. |
| P1-3 | New `45-operations.md`: the four signatures, mixed operand formats, correctness routes by registry group, veneers, refusals, `Block*`/`Scaled*`. |
| P1-4 | Both query vocabularies documented as the same function objects; report-name mapping table on the projections page. |
| P1-5 | `AIFloats.validformat` no longer recommended. |
| P1-6 | `fromcode(F, c)` vs `F(c)` shown in getting-started and basic examples. |
| P1-7 | Full stochastic contract on the projections page and in a worked example. |
| P1-8 | §4.7.4 predicates first; motivation moved into explicitly non-contractual notes. |
| P1-9 | Domain described after signedness. |
| P1-10 | `set_show_style!` (process-wide) vs `IOContext` (local), with the library-code warning. |
| P1-11 | `Convert(F, A)`, packed wire refusals, `copy`/`similar`/`copyto!` for both containers. |
| P1-12 | Conformance qualified as a query on every page that mentions it. |

Reviewed exemptions: `DyadicNumbers` and `Dyadic`, documented on
`97-internals.md` as explicitly unstable.

## Gate 3 — examples

`F`/`T`/`x` applied throughout; every block self-contained; the shared-state
`technical_cache` block split; refusal examples added for `F()`, out-of-range
`fromcode`, `Rational`, unsigned negative input, mismatched axes, packed
padding, and stochastic `R` bounds.

## Gate 4 — metadata

README rewritten to durable performance relationships with the benchmark page as
the source of absolute numbers; `.html` links to match `prettyurls = false`;
placeholder DOI badge removed; `CITATION.cff` completed with the report as a
cited reference; developer page rewritten around this repository (Julia 1.12,
per-file tests, benchmark suites, `AIFLOATS_DOCS_BENCHMARKS=0`, generated pages,
the real CI jobs).

PERF-1 done: the suite was re-run from a clean tree and `60-benchmarks.md`
regenerated. The page is tracked in git — it is a measurement, not a derivation,
and it names the commit and machine it describes. The reference listing pages
stay untracked, because those *are* derivations.

What the fresh run settled:

- **`BlockReduceMultiply` is not on a slow path.** Across runs it is 3.6–3.9x
  *faster* than `BlockReduceAdd` at `B = 16` and `B = 32`, and still ~1.4x
  faster on rung 2 — only possible if its exact `Dyadic` guard passes, because
  the `BigFloat` fallback is far slower than either. The old "always takes the
  `BigFloat` path" claim was not merely stale, it was backwards. A product
  reduction accumulates one significand where a sum aligns `B` of them, which
  is why it wins.
- **"Wider formats ≈ 3 ns" was hiding a ~4x spread.** `K = 8` decodes through
  the generated table, `K = 12` computes, and `K = 16` on rung 2 costs about
  four times `K = 12`. The three are now three rows, not one figure.
- **Packed access costs 1.42x an unpacked kernel**, identically for a cheap
  (`Negate`) and an expensive (`Exp`) operation — not the "about 3x" the status
  page claimed. That it is the same ratio for both is the point: the cost is
  the bit extraction, not the arithmetic.
- **Load is ~68 ms, not ~57 ms, and the first block reduction is ~2 ms, not
  sub-millisecond.** Both removed claims were wrong, and in the flattering
  direction.
- Threading on four threads reaches 3.5–3.9x, inside the range the status page
  already stated.

Figures above are the stable band across two runs on the same machine; the
committed page is the authority for any single number.

Prose remains free of hand-entered absolutes (PERF-2); the status page now names
the rows to compare instead.

## Corrections to the plan itself

- P2-9 said `lychee.toml` was missing. The config exists as **`.lychee.toml`**,
  which is what CI passes; the developer page named it wrongly. Fixed there,
  and the config extended with the P3109 host and timeout settings.
- P2-7 was extended: `PAGES` is now explicit *and* `check_page_tree()` fails the
  build if `docs/src` holds a page `PAGES` does not list — which is what
  actually keeps a planning document out of the site.
- `AIFLOATS_DOCS_BENCHMARKS=0` now leaves an existing benchmark page in place
  instead of overwriting it with a placeholder (V-2's "prefer changing the
  builder").

## Validation run

| | Result |
|:--|:--|
| V-1 source doctests | pass |
| V-2 docs build, benchmarks off | pass; no errors, no warnings but the expected local-deploy notice |
| V-3 `test-doc-contracts.jl` | 2043 assertions, all pass |
| V-4 example isolation | every `@example` block imports what it uses and is executed by the build |
| V-5 link check | `.lychee.toml` corrected; `lychee` is not installed on this machine, so CI runs it |
| PERF-1 benchmark regeneration | suite re-run from a clean tree at `773d5f4`; page regenerated and tracked |
| V-6 focused tests | `test-quality`, `test-binary-format`, `test-traits`, `test-governance`, `test-binaryvalue`, `test-tables`, `test-kernels`, `test-compat` — all pass |

`Pkg.test()` was deliberately not run, per the plan.
