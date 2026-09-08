# Validation of asspec.md against the September 7 PDF

## Result and scope

The plan's central arithmetic and conformance corrections agree with the PDF.
Two definite textual defects remain: an incorrect criticism of §5.4.2 NOTE 2,
and the spelling of Softplus. Three acceptance-check gaps and a provenance
improvement are described separately below. A genuine conflict in §5.5.3 NOTE 2
was also confirmed; it is a PDF finding, not an error in the plan's equations.

This is validation of a specification-development plan, not proof of a Maude
implementation. General statements to transcribe source clauses are treated
as coverage commitments, not as already implemented equations or tests.

Inputs:

- `/home/jas/github/AIFloats.jl/docs/other/asspec.md`, 488 lines.
  SHA-256: `52973296cd7c332d987a5d98fb0ed68f6229f7c570fde7ab418c073f2dcb61d9`.
- `/home/jas/github/AIFloats.jl/docs/other/IEEE_D1_2026_09_07.pdf`, 85 pages.
  SHA-256: `53c217cf225f82fa173aa1e23f7a4134f740cbdcec423311ea4a92a8ac04d299`.

The PDF was the only comparison source. IEEE_D1.md, repository implementation,
external standards, and Maude documentation were not consulted. PDF pages and
printed page numbers coincide for the cited evidence. Normative pp. 12–70 and
informative pp. 71–85 were read; front matter was not used for arithmetic rules.
Rendered pages inspected: 21, 25–27, 29–30, 44–45, 54, 58, 63, 66, 76–77, 79.

## Defects to correct

### F1 — The alleged deficiency in §5.4.2 NOTE 2 is incorrect

Location: asspec.md lines 363–366. Severity: medium.
Evidence: PDF p. 63, §5.4.2, behavior and NOTE 2; pp. 27, 29, rounding/saturation;
p. 70, exact representation of one in conforming formats.

The NOTE already restricts its assertion to nonzero, non-NaN result elements.
For an infinite scale, the pre-projection element is one of -1, 0, 1, or NaN.
Signed P3109 formats represent both units exactly. In unsigned formats, -1
projects to zero or NaN, both excluded by the NOTE's own qualification. Thus
the inability of unsigned formats to represent -1 does not refute the NOTE.

General reasoning: all rounding modes leave the exact units unchanged. For
unsigned output, SatFinite and SatPropagate clip -1 to zero; SatNone either
clips it to zero under TowardZero/TowardPositive or yields NaN. Positive one,
zero, and NaN retain their respective values. Every nonzero, non-NaN output
is therefore a unit. No exhaustive stochastic-parameter enumeration is needed
for that argument because the fractional remainder is zero.

Independent checks: 73,440 format/mode/saturation/intermediate-value combinations
across all 120 valid P3109 formats with 3≤K≤8; stochastic fixtures exhaust N=0..3.

Correction: remove the asserted limitation, retain the projection equations,
and require the NOTE property to pass for P3109 formats. This corrects a
mistake introduced by the earlier review, rather than a discrepancy in the PDF.

### F2 — SoftPlus does not match the defined operation identifier

Location: asspec.md line 270. Severity: low.
Evidence: PDF p. 45, §4.10.13 signature and behavior; p. 69, §5.7 substitutions.

The PDF uses `Softplus` and `ωSoftplus`, not `SoftPlus`. This matters if the
plan's names become case-sensitive inventory or generator inputs.

Correction: use `Softplus` consistently, with `BlockSoftplus` and
`ScaledSoftplus` when listing the corresponding derived operations.

## Acceptance-check gaps and improvements

### V1 — Underflow acceptance omits the negative half-neighborhood

Location: asspec.md lines 226–228.
Evidence: PDF p. 26, §4.7.3 NOTE 2; p. 27, §4.7.4.

The PDF states the zero result in terms of magnitude. Restricting this part
of acceptance to nonnegative values leaves the corresponding negative inputs
unchecked. This is incomplete test coverage, not a wrong rounding formula.

Suggested replacement: test `abs(X)≤m/2 → 0` for the smallest positive
subnormal m, both signed endpoints, zero, and points immediately on either
side of the thresholds. Retain the positive `(m/2,m)` check and its signed
counterpart where appropriate. Formats without subnormals need separate
P=1 tests. For Binary4p2sf, m=1/4 and both ±1/8 project to zero under nearest-even.

### V2 — TotalOrder acceptance covers one format at a time

Location: asspec.md lines 317–321 and 327–329.
Evidence: PDF p. 54, §4.12.1, independently parameterized input formats fx and fy.

The per-format rank check correctly establishes the stated order laws on each
format's value set, but does not test the defined mixed-format specializations.
For example, one in Binary4p2sf (code 4) and one in Binary8p4se (code 64) must
compare True in both directions. A one-format implementation could pass the
listed acceptance checks while mishandling format parameters.

Improvement: retain per-format antisymmetry checks and add mixed-format pairs
using decoded numeric values with NaN first. Do not demand antisymmetry over
distinct format-tagged representations of the same datum. Include equal datums
with different codes, unequal datums, NaN pairs, and supported infinities.

### V3 — Next inverse laws do not establish immediate adjacency

Location: asspec.md lines 327–329.
Evidence: PDF p. 59, §4.16's least-greater/greatest-less requirement.

Mutually inverse successors/predecessors can traverse the wrong permutation
of interior values while preserving all inverse laws, endpoints, and the
transitions next to zero. For example, swapping 0.5 and 0.75 inside the
positive Binary4p2sf traversal preserves invertibility but can make the
successor of 0.25 equal 0.75 instead of 0.5.

Improvement: reuse the independent numerically ordered datum list already
created for TotalOrder. Require NextGreaterThan/NextLessThan to return its
immediate neighbors for every non-NaN code, with the specified boundary and
NaN behavior. This adds linear work per format and makes inverse checks
largely redundant. The plan already calls for implementing the right rules;
the defect is the weakness of this particular acceptance criterion.

### P1 — Record the authority actually validated

Location: asspec.md lines 3–5 and 41–42.

The plan declares IEEE_D1.md as its authority. This review establishes agreement
with the PDF only; it does not establish that the Markdown rendering matches
the PDF. Therefore this is a provenance improvement, not a demonstrated
semantic contradiction between the two reference files.

Improvement: make the PDF filename and hash the authoritative source for a
PDF-validated revision. Treat any text extraction as a derived navigation aid
and preserve page references for evidence. Do not imply the Markdown source
was validated in this review.

## Confirmed PDF finding to record

### S1 — §5.5.3 NOTE 2 can produce infinity, outside its stated result alternatives

Relevant plan location: lines 361–366 and 406. PDF p. 66, §5.5.3 NOTE 2.

Concrete specialization and operands:

- B=1; input element, scale, and result formats all Binary8p4se.
- Input element +Inf.
- Scale projection: (NearestTiesToEven, SatFinite).
- Element projection: (NearestTiesToEven, SatNone).

The maximum absolute finite reduction on [NaN,+Inf] returns +Inf (p. 51).
Scale projection yields 224, the maximum finite datum. Block projection then
divides +Inf by 224, giving +Inf (p. 37), and element projection preserves it
(p. 29). NOTE 2 instead restricts elements to ±1 or ±MaxFiniteOf(fr).

This is a concrete conflict in an informative NOTE. Preserve the normative
behavior and log this example as the finding. The plan's general mechanism
for failed NOTEs already accommodates it; it should replace the false F1
example when the plan is revised.

## Computational evidence

The independent Fraction-based script is `/tmp/asspec-validation/check.py`.
It was transcribed from the rendered PDF, not from package code.
Results are in `/tmp/asspec-validation/check-results.json`. These temporary
validation artifacts are separate from this report; the evidence and results
needed to assess the findings are included above and below.

| Check | Result |
|---|---|
| P3109 formats, 3≤K≤8 | 120 valid parameter combinations |
| Decoder uniqueness and encode-after-decode | 13,296 code points passed |
| PDF Tables 4–7 | All 224 entries passed; six approximate entries use absolute tolerance 0.00005 |
| One encoding location | Passed in all 120 formats |
| Binary8p4se 240 counterexample | Integer significand, naive code 127, not a datum; maximum finite 224 |
| §3.1 NOTE 2 | 2 encodes to 0x48; +Inf to 0x7F |
| Binary4p2sf extrema | Minimum/maximum finite codes 15/7 |
| Enclosure counterexample | Projection of [-100,0,100] gives [NaN,0,NaN] |
| D.2 restricted operands | 145 values each; 145^4=442,050,625 tuples |
| Negative/positive half-smallest-subnormal | Both -1/8 and +1/8 project to zero in Binary4p2sf |
| §5.4.2 NOTE 2 | 73,440 checks passed; general unit-value argument above |
| §5.5.3 NOTE 2 | Counterexample confirmed: scale 224, result +Inf |

These are checks of PDF-derived mathematics used in the plan. They are not
tests of a Maude implementation, exhaustive tests of all stochastic N, or
proofs for all bitwidths. The PDF's 21 saturation rows, 17 initial FMA NaN rows,
17 ArcTan2 rows, 10 extrema, and 14 four-bit formats agree with the plan.

## Forward coverage ledger

Each row groups related claims sharing evidence. “Supported” means the
asserted semantics agree with the PDF at plan level. “Choice” means an
engineering or validation policy not established by the PDF; it is not
misrepresented here as a standard requirement. Referenced future tests and
proofs remain work to perform during implementation.

| asspec lines | Claims | PDF evidence | Disposition |
|---|---|---|---|
| 1–11 | Authority; rational/symbolic/external scope | pp. 13, 18, 31, 58 | Choice; provenance P1 |
| 13–22 | Normative/recommendation/informative distinction | p. 12; annex labels; pp. 26, 63 | Supported; conflict policy is a choice |
| 23–37 | Logs, traceability, exactness, first match | pp. 18–20, 24 | Supported semantics; artifact design is a choice |
| 39–54 | Source hash, inventory, Annex F cross-check | §§1–5; pp. 58, 82–84 | Choice; RoundOf/SatOf absent from Annex F |
| 56–83 | Module order, contracts, no side effects/random generation | pp. 18, 28, 31, 58, 61 | Choice; source restriction explicitly acknowledged |
| 85–108 | Reals, exceptional values, formats, code and block domains | pp. 13–16, 28, 61 | Supported; guard representation is a choice |
| 109–113 | Unreduced invalid/symbolic applications | Operand restrictions throughout | Choice; not prescribed by PDF |
| 115–122 | Rational core, Boolean results, real composition, signum | pp. 15–16, 33–43, 53–56, 63 | Supported/derived; evaluator technique is a choice |
| 124–129 | Valid parameters and external metadata | pp. 16, 58 | Supported |
| 130–133 | Decoder-image datum characterization | pp. 16, 25, 30 | Derived characterization; equivalence remains an implementation obligation |
| 134–141 | Code-valued queries, no subnormals at P=1, symmetry | pp. 16, 25, 58, 76 | Supported |
| 142–145 | Names and K=2 exclusion | pp. 16–17, 78 | Supported |
| 147–150 | emax checks, external query contracts | pp. 58, 74 | Supported; sample/proof scope explicit |
| 152–165 | Modes, random bounds, block indexing, singleton lift | pp. 18, 27–28, 58, 61, 70 | Supported; constructor design is a choice |
| 167–181 | Codecs, full encode domain, 240 example | pp. 25, 30, 73 | Supported; example independently checked |
| 183–191 | External exceptional cases and abstract finite codecs | pp. 31, 58 | Supported; concrete quiet-NaN selection is a choice |
| 193–199 | Rounding formula, parity, stochastic cases | pp. 27–28 | Supported |
| 201–206 | Saturation count and priorities | p. 29 | Supported |
| 208–210 | Projection returns code; pipeline | pp. 16, 26, 30 | Supported; datum-output obligation applies to pipeline |
| 212–225 | Codec/table/boundary acceptance | pp. 16, 25–30, 75–77 | Supported mathematics; validation scope is a choice |
| 226–228 | Underflow acceptance | p. 26 | Incomplete coverage, V1 |
| 230–243 | Effective guards and coverage partitions | pp. 18–20 | Equivalent translation strategy; Maude feasibility not established by PDF |
| 245–248 | Rational-core operation inventory | pp. 32–40, 49–56 | Supported |
| 250–259 | FMA/FAA compositions and independent cases | pp. 38–39 | Supported |
| 261–265 | Finite exhaustive fixtures | pp. 37–40, 76 | Choice; sizes and special results supported |
| 267–274 | General real families and composition | pp. 40–48 | Supported except Softplus spelling F2 |
| 276–282 | ArcTan2 count, poles, exceptional-input results | pp. 40–44, 47 | Supported |
| 284–287 | Rational square-root evaluator | p. 40 | Correct derived optimization; implementation choice |
| 289–303 | Enclosure certificate requirements and example | pp. 26–29, 76 | Sound derived criterion; theory/tool claims remain obligations |
| 305–308 | Real evaluator acceptance | pp. 40–48 | Choice; no guaranteed fixed-width termination asserted |
| 310–316 | Wrapper generation and Class | pp. 19–20, 32–58 | Supported schema; generator is a choice |
| 317–321 | TotalOrder and rank checks | p. 54 | Supported within one format; mixed-format gap V2 |
| 322–325 | Next rules and external limitation | pp. 59–60 | Supported P3109 rules; external scope explicitly unresolved |
| 327–329 | Class/order/Next acceptance | pp. 54, 57, 59 | Choices with gaps V2, V3 |
| 331–348 | Encoded/decoded blocks, fold, block equations | pp. 61–63 | Supported |
| 349–352 | NaN before zero; infinite-scale intermediate units | p. 63 | Supported |
| 354–359 | Block conversion/reduction/elementwise/scaled schemas | pp. 64–70 | Supported coverage commitment |
| 361–366 | NOTE acceptance and alleged unsigned exception | pp. 63, 66 | General policy sound; definite defect F1; source finding S1 |
| 368–371 | B=1 unit-scale equivalences | pp. 35–36, 62–63, 68, 70 | Supported derivations |
| 373–390 | Termination/confluence/completeness obligations | No Maude tooling specified in PDF | Choice; no tooling certification performed |
| 392–409 | Property inventory, annex roles | pp. 16, 37–39, 47, 58–59, 63, 66, 74–81 | Supported; particular NOTE disposition corrected by F1/S1 |
| 411–417 | D.1 limitation, D.2 assumed κ and workload | p. 79; decoder p. 25 | Supported; numeric count independently checked |
| 419–439 | Required specialization set | pp. 22–23 | Supported; all required families mapped |
| 441–447 | Exact behavior, approximation names/attestation | pp. 21, 24 | Supported |
| 449–461 | NaN/Inf precedence, interval count, partitions, multi-result κ | p. 21 | Supported; external counting and empty-I convention explicitly pending |
| 463–467 | Conformance acceptance/status reporting | pp. 21–24, 79 | Choice respecting source obligations |
| 469–488 | Deliverables, traceability, completion limits | Source-wide | Choice; appropriately separates future proofs from execution |

## Reverse normative coverage

The following inventory was checked from the PDF toward the plan, independently
of the plan's list of claims. Parent headings without additional semantics are
grouped with their children. No required operation family is wholly absent.

| PDF clauses (pages) | Subject | Plan step(s) / disposition |
|---|---|---|
| 1.1–1.2 (12) | Scope and requirement vocabulary | 0; narrower executable scope declared |
| 2.1–2.3 (13–15) | Definitions, abbreviations, mathematical notation | 1, 3–5, 10; abbreviation material documented as needed |
| 3.1–3.2 (16–17) | Formats, encoding/datum distinction, names | 3–4, 6 |
| 4.1–4.2 (18) | Operations and projection modes | 2–3, 5 |
| 4.3.1–4.3.2.4 (19–20) | Definition schema and ordered patterns | 1, 7, 9 |
| 4.4 (21) | Approximation declarations and κ | 13 |
| 4.5 (22–23) | Required specializations | 13; table matches all families |
| 4.6 (24) | Exact results and declaration recommendations | 0–1, 13 |
| 4.7.1–4.7.2 (25) | Internal status and decoder | 2, 6; auxiliary functions not added to required public set |
| 4.7.3–4.7.6 (26–30) | Project, round, saturate, encode | 5–6; V1 acceptance gap |
| 4.8.1–4.8.2 (31) | External decode/encode | 2, 6; explicit unresolved contracts |
| 4.9.1 (32) | Convert | 7, 9 |
| 4.10.1–4.10.5 (33–37) | Abs, negate, sign, arithmetic, divide | 7, 9 |
| 4.10.6–4.10.7 (38–39) | FMA and FAA | 7, 9 |
| 4.10.8 (40) | Sqrt, Recip, RSqrt | 7–9 |
| 4.10.9 (41) | Six exponential/logarithmic operations | 8–9 |
| 4.10.10–4.10.12 (42–44) | Trigonometric, hyperbolic, π variants | 8–9 |
| 4.10.13 (45) | Softplus | 8–9; spelling defect F2 |
| 4.10.14–4.10.16 (46–48) | Hypot and two ArcTan2 variants | 8–9 |
| 4.11.1–4.11.4 (49–52) | Ten extrema and Clamp | 7, 9 |
| 4.12 (53–54) | Five comparisons | 7, 9 |
| 4.12.1 (54) | TotalOrder with independent input formats | 9; mixed-format acceptance V2 |
| 4.12.2 (55) | Optional comparison-symbol mappings | 0–1 general permission/table inventory; recommend explicit include/exclude disposition |
| 4.13–4.13.1 (56–57) | Eight predicates and Class | 7, 9 |
| 4.14 (58) | Twelve metadata/value queries | 2, 4, 13 |
| 4.15 (58) | RoundOf and SatOf | 1, 5 |
| 4.16 (59–60) | Next operations | 9; adjacency acceptance V3 |
| 5.1–5.3 (61) | Blocks, reduce, stochastic sequences | 3, 5, 10 |
| 5.4.1–5.4.2 (62–63) | Block decode/project | 10; F1 is a mistaken NOTE criticism |
| 5.5.1–5.5.3 (64–66) | Three block conversions | 10; source finding S1 |
| 5.6.1–5.6.2 (67–68) | Add/multiply reductions and dot product | 10 |
| 5.7 (69) | Elementwise schema and substitution list | 10; 31 unary, 18 binary, 3 ternary substitutions |
| 5.8 (70) | Scaled schema, exact unit scale, singleton lift | 5, 10 |

Annex disposition: A/B formulas and tables are checks (steps 4, 6, 12);
C is explicitly excluded from normative-format acceptance; D.1 is analytical
and D.2 is a declaration fixture; E is optional; F is a cross-check; G's
references are not imported. No findings were manufactured from differences
between the PDF and the unconsulted Markdown rendering.

## Remaining limits

General real-number realizations, external-format codec instances, Maude
tool compatibility, and future implementation proofs remain outside this
document-validation result. The specification file and PDF were not modified.
