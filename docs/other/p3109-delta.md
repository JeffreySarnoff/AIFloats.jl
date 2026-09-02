# P3109 semantic delta — designated report versus implementation

**Status:** Gate 0 evidence for `docs/refinedocs2.md`. Not a published documentation page.

## 1. Pinned normative source

| Field | Value |
|:--|:--|
| Document | IEEE Working Group P3109 Interim Report on Arithmetic Formats for Machine Learning |
| URL | <https://github.com/P3109/Public/blob/main/IEEE%20P3109%20Interim%20Report.pdf> |
| Cover revision | Version 4.0.3 |
| Cover date | 1 September 2026 |
| PDF SHA-256 | `7de115ed6882b7550b8fa61e81e5173857b340c3bfe30db8d4ad74b472229b9e` |
| Cover qualification | "DRAFT DOCUMENT … This document is subject to change. USE AT YOUR OWN RISK! … Because this is an unapproved draft, this document must not be utilized for conformance / compliance purposes." |

This PDF is the **sole** normative authority for this audit. No other IEEE
document — earlier P3109 draft, published standard, or working-group material —
was consulted, and none may be used to settle an ambiguity. Where the report is
silent, the package records a maintainer *interpretation*, labeled as such.

The report's own introduction still carries the "D1" designation; the cover
carries the revision. Both are facts about the same document.

**Compared tree:** AIFloats.jl 0.2.0 at `d68a8ba`.

## 2. Classification key

| Code | Meaning |
|:--|:--|
| **OK** | Implementation agrees with the report |
| **DOC** | Documentation-only defect; implementation is correct |
| **API** | Package spelling differs from the report's term; semantics agree |
| **EXT** | Deliberate Julia extension the report does not define |
| **INT** | Package interpretation where the report leaves a choice |
| **SRC** | Implementation defect — a source issue, not a wording change |

No **SRC** rows were found in this pass.

## 3. §3 Floating-point formats

| Report | Implementation | Class | Note |
|:--|:--|:--|:--|
| §3.1 four format-defining parameters K, P, Σ, ∆ | `Binary{K,P,S,D}` | OK | `S`, `D` are `Bool` after `resolve_fields` canonicalization |
| §3.1 `K > 2` | `KMIN = 3` | OK | |
| §3.1 `0 < P < K` signed, `0 < P ≤ K` unsigned | `validformat`: `P > 0`, `P <= K - S` | OK | Same predicate |
| §3.1 bias `B = 2^(K−P−1)` signed, `2^(K−P)` unsigned | `ExponentBiasOf` | OK | Verbatim |
| §3.1 exponent bits (derived) | `ExponentBitwidthOf = (K − S) − (P − 1)` | OK | Consistent with the bias rule: `B = 2^(E−1)` under both signednesses |
| §3.1 trailing significand `S mod 2^(P−1)` | `TrailingSignificantBitsOf` returns the **width** `P − 1` | API | The report's §4.5 name is `TrailingSignificandBitwidthOf`; see §6 below |
| §3.1 single NaN, no negative zero | one NaN code, one zero | OK | |
| §3.1 `Rω := R ∪ {−∞, +∞, NaN}` | `Rounded` kinds `KIND_FIN`/`KIND_PINF`/`KIND_NINF`/NaN | OK | |
| §3.2 naming `Binary⟨K⟩p⟨P⟩⟨s\|u⟩⟨f\|e⟩` | 504 generated aliases, `Binary8p4se` etc. | OK | Capitalized because they are Julia **types** |
| §3.2 name is a *format* | — | DOC | `20-concepts.md` calls them "datum aliases" |

**Documentation defect found:** `20-concepts.md` rearranges
`K = S + exponent + (P − 1)` into `K − P − S`, dropping the `+1`, and its table
prints 3 and 4 exponent bits where the implementation and the report's bias rule
both give 4 and 5. Same omission in the `PrecisionOf` docstring. → P0-2.

## 4. §4.2, §4.7.4, §4.7.5 — projection

### Rounding modes (§4.2 names, §4.7.4 predicates)

| Report `RoundAway(µ)` | Implementation (`src/projection/round.jl`) | Class |
|:--|:--|:--|
| `TowardZero` → False | `_roundaway(::ρRTZ, …) = false` | OK |
| `TowardPositive` → `ν > 0 and X > 0` | `_νgt(ν, νs, 0) && sign > 0` | OK |
| `TowardNegative` → `ν > 0 and X < 0` | `_νgt(ν, νs, 0) && sign < 0` | OK |
| `NearestTiesToAway` → `ν ≥ 0.5` | `_νge(ν, νs, 0.5)` | OK |
| `NearestTiesToEven` → `ν > 0.5 or (ν = 0.5 and not CodeIsEven)` | same, with `_codeiseven` | OK |
| `ToOdd` → `ν > 0 and CodeIsEven` | `_νgt(ν, νs, 0) && _codeiseven(…)` | OK |
| `StochasticA_{N,R}` → `⌊ν·2^N⌋ + R ≥ 2^N` | `_νfloorscaled(ν, νs, N) + R >= 1 << N` | OK |
| `StochasticB_{N,R}` → `⌊ν·2^(N+1)⌋ + (2R+1) ≥ 2^(N+1)` | `_νfloorscaled(ν, νs, N+1) + (2R+1) >= 1 << (N+1)` | OK |
| `StochasticC_{N,R}` → `RNITE(ν·2^N) + R ≥ 2^N` | `_νrnite(ν, νs, N) + R >= 1 << N` | OK |
| `CodeIsEven = IsEven(⌊S̃⌋)` if `P > 1`, else `(⌊S̃⌋ = 0) or IsEven(Q + B)` | `_codeiseven(Sfl, Q, B, P)` | OK |
| — | the sticky companion `νs ∈ {−1, 0, +1}` carried beside `ν` | EXT | Represents "ν is exact / ν is a shade above / below" when the carrier cannot hold the exact fraction. Every predicate above is evaluated on the exact fraction `ν + νs·ε`, so this **implements** the report's predicate on inexact carriers rather than altering it |
| §4.7.4 Details: `0 ≤ R < 2^N` | `R in 0:(2^N − 1)`, `N in 1:60` | INT | The `N ≤ 60` ceiling is a package limit; the report bounds `R` but not `N` |

### Rounding-mode names

| Report | Package short | Package long | Class |
|:--|:--|:--|:--|
| `NearestTiesToEven` | `RTE` | `RoundToEven` | API |
| `NearestTiesToAway` | `RTA` | `RoundToAway` | API |
| `TowardPositive` | `RTP` | `RoundTowardPositive` | OK |
| `TowardNegative` | `RTN` | `RoundTowardNegative` | OK |
| `TowardZero` | `RTZ` | `RoundTowardZero` | OK |
| `ToOdd` | `RTO` | `RoundToOdd` | API |
| `Stochastic[A,B,C]` | `RSA`/`RSB`/`RSC` | `StochasticA/B/C` | OK |

The three **API** rows are package long names, not report terminology. → §5.3 of
the plan; the projections page must say so.

### Saturation modes (§4.7.5 `ωSaturate`)

| Report row | Implementation (`src/projection/saturate.jl`) | Class |
|:--|:--|:--|
| `SatFinite(+∞) → M_hi`, `(−∞) → M_lo`, out-of-range clamps | `_saturate(::ρSF, …)` | OK |
| `SatPropagate(+∞, Extended) → +∞`, else `M_hi` | `is_extended(F) ? posinf_code : _maxfinite_code` | OK |
| `SatPropagate(−∞, Signed, Extended) → −∞`, else `M_lo` | `(is_signed(F) && is_extended(F)) ? neginf_code : _minfinite_code` | OK |
| `SatPropagate` finite overflow clamps | `over`/`under` → extremal finite | OK |
| `SatNone` with `TowardZero`/`TowardNegative` and `X > M_hi`, `X ≠ +∞` → `M_hi` | `over && RM <: Union{ρRTZ, ρRTN}` under `KIND_FIN` | OK |
| `SatNone` with `TowardZero`/`TowardPositive` and `X < M_lo`, `X ≠ −∞` → `M_lo` | `under && RM <: Union{ρRTZ, ρRTP}` under `KIND_FIN` | OK |
| `SatNone(±∞ / overflow, Extended)` → the infinity; unsigned `−∞` → NaN | `is_extended(F)` branch, `is_signed(F) ? neginf_code : nan_code` | OK |
| `SatNone(∗, Finite)` → NaN | trailing `nan_code(F)` | OK |
| NOTE: rounding mode is supplied to `ωSaturate`; saturation does not round | `saturate(F, ρ::Projection{RM,SM}, r::Rounded)` passes `μ` | OK |

**Documentation defect found:** the Intermediate saturation example projects a
finite `1.0e100` under `SF` and `SP`, which the report requires to clamp
identically. The modes differ only on a genuine infinity. → P0-6.

### Default projection

The report defines **no** default projection. §4.5 requires the listed
specializations at `ρ = (NearestTiesToEven, SatNone)`. AIFloats' task-local
`DefaultProjection()` is initially `RTE_SN`, which is the same pair — but as a
**package** choice, not a report mandate. Class: **INT**.

**Documentation defect found:** three sites call `RTE_SF` "the conventional
default". → P0-3.

## 5. §4.5 Conforming implementations

| Report requirement | Implementation | Class |
|:--|:--|:--|
| `F8 = {Binary8p4se, Binary8p3se}` | both aliases exported | OK |
| `F4 = {Binary4p2sf}` | exported | OK |
| `FX ⊆ {binary32, binary16, BFloat16}`, non-empty, choice implementation-defined | `binary16`, `binary32`, `bfloat16` (also `binary64`, `binary128`) | OK |
| `Fs = {Binary8p1uf}` for scaled operations | exported; used by `Scaled*` | OK |
| `Convert`, `Negate`, `Abs`, `Recip`, `Add`, `Subtract`, `Multiply`, `FMA`, `FAA` | all in `operations()` | OK |
| The 10 `MinmaxOp` names | `Minimum`…`MaximumFinite`, all present | OK |
| `CompareLess`, `CompareLessEqual`, `CompareEqual`, `CompareGreater`, `CompareGreaterEqual` | Julia `<`, `<=`, `==`, `>`, `>=` on same-format datums | API |
| `IsZero`, `IsOne`, `IsNaN`, `IsInfinite`, `IsFinite`, `IsSignMinus`, `IsNormal`, `IsSubnormal` | Julia `iszero`, `isone`, `isnan`, `isinf`, `isfinite`, `signbit`, `Class(x) === ClassPosNormal`/`ClassNegNormal`, `issubnormal` | API |
| `NextGreaterThan`, `NextLessThan` | exported under the report's names | OK |
| Format-level: `BitwidthOf`, `PrecisionOf`, `SignednessOf`, `DomainOf`, `ExponentBitwidthOf`, `ExponentBiasOf`, `MaxFiniteOf`, `MinFiniteOf`, `MinPositiveOf`, `MaxSubnormalOf`, `MinNormalOf` | all exported under the report's names | OK |
| Format-level: `TrailingSignificandBitwidthOf` | exported as `TrailingSignificantBitsOf` | **API** |
| `ScaledAdd`, `ScaledSubtract`, `ScaledMultiply` | generated `Scaled*` forms for every register operation | OK (superset) |
| — | `bitwidth`, `precision`-style lower-case aliases; the same generic function objects | EXT |
| — | 504 formats `3 ≤ K ≤ 16`, well beyond `F4 ∪ F8` | EXT |

### The one naming delta

`TrailingSignificandBitwidthOf` (report) versus `TrailingSignificantBitsOf`
(package). "Significant bits" and "significand bitwidth" are different words;
the semantics are identical (both return `P − 1`). Classified **API**, not a
typographical matter for prose to smooth over.

**Resolution recorded:** keep `TrailingSignificantBitsOf` as the 0.2.x exported
spelling, document the report's name beside it, and treat an alias or rename as
a deliberate API decision for a later minor release. It is not a **SRC** defect:
the value returned is correct under either name.

## 6. §4.6 Conformance declarations

| Report | Implementation | Class |
|:--|:--|:--|
| An implementation supplies a *subset* of specializations | `conformance()` derives the list live from `OP_REGISTRY` | OK |
| Supplied specializations shall compute the defined result for all operand values | verified against an independent `BigInt` reference | OK |
| Approximate implementations shall declare κ (§4.4) | `register_approx!`/`measure_kappa`; understatement rejected | OK |
| An implementation *should* let a user query a specialization by string | `conformance_report`, `conformance_dict` | OK |
| Cover: the draft "must not be utilized for conformance / compliance purposes" | — | DOC |

**Documentation defect found:** the Status page calls `conformance()` "the
draft-§4.6 declaration" without the unapproved-draft qualification. A reader can
take it for a compliance determination. → P1-12.

## 7. Package identity

`draft_identity()` reports:

```julia
(designation = "IEEE P3109/D1", uploaded = "2026-07-17",
 retained_source = "docs/other/IEEE_D1.md",
 transliteration_sha256 = "820cb500…")
```

That names a **retained transliteration** and its upload date, not the cover
revision of the designated report. Since no **SRC** row was found in §§3–5, the
identity may now be extended to carry the designated report's revision, date,
and PDF digest alongside the retained transliteration — the transliteration
stays as provenance for the material the package was built against, and the
report fields state what the package is measured against.

Class: **DOC** (identity reporting), resolved by P0-1.

## 8. Sections not re-derived in this pass

§§4.8–4.16, §5 (block operations), and the annexes were checked for *name and
shape* agreement with `operations()`, `src/arrays/blocks.jl`, and the exported
surface, and no disagreement surfaced. Their per-operation result expressions
were not re-derived symbolically. Anything a documentation page asserts about
those sections must cite the PDF location before it is published.
