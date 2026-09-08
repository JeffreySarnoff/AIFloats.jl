# Plan: IEEE P3109/D1 as a Maude specification

Authoritative source: `docs/other/IEEE_D1_2026_09_07.pdf`, IEEE P3109/D1,
September 2026. SHA-256:
`53c217cf225f82fa173aa1e23f7a4134f740cbdcec423311ea4a92a8ac04d299`.
Where this document says "the draft", it means that PDF. Extracted text is
only a navigation aid; the PDF's visible content governs. This plan does not
import semantics from other references or assume that a Markdown rendering
has been validated against the PDF.

Target: a Maude 3 specification with an executable exact rational core for
P3109 formats, symbolic specifications for general real results, and explicit
external-format contracts. Full external-format execution requires information
the draft delegates to other references; that obligation remains open under
this plan's source restriction.

## 0. Governing rules

1. **Use §§1–5 for definitions and requirements.** Preserve signatures,
   operand restrictions, formulas, normative tables, and ordered behaviors,
   as well as `shall` requirements. In particular, §4.14's table is normative.
   Distinguish requirements, recommendations (`should`), permissions
   (`may`), and statements of possibility (`can`).
2. **Use informative material as checks.** Annexes and NOTEs supply examples
   and property checks, not replacement definitions. A NOTE conflicting with
   normative behavior becomes a documented source finding. Record
   recommendations without making them mandatory equations.
3. **Expose choices and limitations.** In `deviations.md`, distinguish source
   ambiguities, implementation choices, exclusions, and unfulfilled contracts,
   each with its clause reference and reason. An unusual but explicitly
   specified behavior is not a deviation.
4. **Trace both ways.** Every semantic equation has a source reference and
   matrix entry. Each source row links to the artifacts appropriate to its
   kind: equations, tests, comments, findings, or unresolved obligations.
   Several behavior rows may map to one equivalent equation family.
5. **Preserve exactness.** Use exact rationals where possible and symbolic
   real expressions otherwise. Accept an approximation as the specified
   projected result only when a sufficient certificate establishes that result.
6. **Preserve first-match semantics.** Translate ordered behavior lists into
   mutually exclusive effective guards (Step 7). Verify coverage and source
   agreement independently of equation order.

## 1. Freeze the source and build the inventory

- Record the authoritative PDF's filename and SHA-256 in a manifest referenced
  by the modules. Record extraction tools/options for any derived text, and
  preserve PDF page numbers and printed page labels for source evidence.
  A changed source requires a reviewed revision of the specification.
- Extract requirements, signatures, operand/result domains, behavior rows,
  formulas, normative tables, recommendations, and NOTE properties from
  §§1–5. Matrix columns: `§ref`, `PDF-page`, `printed-page`, `kind`, `text`, `module`,
  `equation-id(s)`, `test-id(s)`, `status`, and `reason` where needed.
- Build the operation inventory from §§4–5, including `RoundOf` and `SatOf`
  in §4.15. Cross-check Annex F and record discrepancies; that informative
  listing is neither an exact inventory oracle nor a generator input.
- Index Annex A's formulas, Tables 3–8, and Annex D–E examples separately as
  checks. Include §3.1 NOTE 2's encoding examples in the property inventory.

**Accept when** every normative definition and behavior has a traceable row,
and each informative check has an explicit scope and disposition.

## 2. Module layout and dependencies

Use this dependency order. Real-number and external-format interfaces are
contracts; executable implementations are separate modules.

| Module | Content and dependencies | Draft §§ |
|---|---|---|
| `XREAL` | finite real signature, rational arithmetic, exceptional values, comparisons | 2.1, 2.3, 4.1 |
| `FORMAT-CORE` | syntax, validity, names, integer/enumeration metadata | 3.1, 3.2, 4.14 |
| `PROJSPEC` | scalar/block projection specifications and validity | 4.2, 4.7.4, 4.15, 5.3 |
| `EXTERNAL-CONTRACT` | external datums, codecs, value queries; uses preceding signatures | 4.8, 4.14 |
| `CODEC` | P3109 decode, datum membership, guarded encode; external dispatch through its contract | 3.1, 4.7.2, 4.7.6 |
| `FORMAT-QUERIES` | code-valued queries using codec datums and external contracts | 4.14 |
| `ROUND` | rational evaluator and symbolic real specification | 4.7.4 |
| `SATURATE` | saturation using decoded finite bounds | 4.7.5 |
| `PROJECT` | round, saturate, encode; uses preceding modules | 4.7.3 |
| `OMEGA` | numeric operations, comparisons, predicates; elementary real-function contracts | 4.9–4.13 |
| `OPS` | scalar wrappers, Class, TotalOrder, Next | 4.3, 4.9–4.16 |
| `BLOCK` | shapes, folds, block internals, conversions, reductions, elementwise and scaled operations | 5 |
| `CONFORMANCE` | required specializations, behavioral obligations, approximation declarations | 4.4–4.6 |
| `TESTS` | source-derived vectors, properties, certificate checks | §§1–5, Annex A–E |

`FORMAT-CORE` must not depend on `CODEC`. Codec datum membership must not
depend on the code-valued queries that use it. Each parameterized module
states its imported contracts and which instances are executable.

No flags, interrupts, hardware realization, or side effects are modeled.
Random values are explicit operands; the model never generates them.

## 3. Shared domains and validity

Define this vocabulary once and apply it consistently to operation guards.

- `Real < XReal`, with `Real` denoting finite mathematical reals and the
  rationals embedded by a constructor `fin : Rat -> Real` rather than declared
  `Rat < Real`; the subsort form merges the built-in numeric tower into the
  kind of `XReal`, which defeats sort-disjointness and every downstream tool.
  `NaN`, `+Inf`, and `-Inf` inhabit a separate `Exceptional` subsort of
  `XReal`. This internal name distinguishes them from the draft's term
  "special value", which also includes zero.
- `validFormat(f)` checks P3109 parameter restrictions or recognizes one of
  §4.14's four external formats. Constructors produce syntactic `Format`
  terms; validity is an explicit guard. An invalid term does not lose the
  sort assigned by its constructor.
- `validCode(f,c)` requires a valid format and integer `0 ≤ c < 2^K`.
  `datum(f,X)` means membership in the format's representable datum set,
  including only the exceptional values supported by that format.
- `validScalarProjection(ρ)` checks the mode and scalar random operand.
  `validBlockProjection(B,ρ)` also checks the random-sequence length.
- `validBlock(B,fs,f,(s,xs))` requires `B ≥ 1`, a scale code in `fs`,
  and exactly `B` element codes in `f`. A decoded sequence contains
  `XReal` values and is distinct from an encoded block.

Invalid-domain applications remain visibly unreduced; they do not acquire
an error datum or a different result sort. A symbolic application with an
undecided guard also remains unreduced, with that different reason recorded
by the test harness.

Every finite floating-point datum is dyadic. Rational inputs remain rational
under the finite branches of arithmetic, extrema, Clamp, and sign operations;
Divide and Recip may leave the dyadics. Comparisons and predicates return
Booleans. Full finite signatures must accept `Real`, so expressions such as
`ωSubtract(ωExp(1),1)` are well-formed.

Define rational `abs`, `floor`, parity, and positive-domain `floorLog2`
exactly. Use terminating power-of-two bracketing for `floorLog2`, with checks
at `1`, `3/4`, `2^(-20)`, and `2^20+1`. Real arithmetic, comparisons,
and elementary functions have explicit mathematical contracts and domain
guards. Handle exceptional operands by the draft's cases, including
`sgn(+Inf)=1`, `sgn(-Inf)=-1`, and `sgn(0)=0` needed by §5.4.2.

## 4. Formats and code-valued queries

- P3109 constructors carry `K,P,Signedness,Domain`. Validity requires
  `K>2`, `0<P<K` for signed formats, and `0<P≤K` for unsigned formats.
- Include `binary64`, `binary32`, `binary16`, and `BFloat16`. Transcribe
  all integer/enumeration metadata from §4.14, including its external columns.
  P3109 exponent bias is `2^(K-P-1)` signed and `2^(K-P)` unsigned.
- Characterize the P3109 datum set as the image of §4.7.2's decoder on valid
  codes and establish agreement with §3.1. A practical membership predicate
  may use derived bounds and significand conditions, proved equivalent to
  that image. No large datum enumeration is required in the implementation.
- `MaxFiniteOf`, `MinFiniteOf`, `MinPositiveOf`, `MaxSubnormalOf`, and
  `MinNormalOf` return codes for the datums described in §4.14. Select the
  P3109 datums using the decoder characterization, then encode them.
  `MaxSubnormalOf` returns the NaN code when no subnormals exist (`P=1`).
- Signed symmetry is
  `decode(f,MinFiniteOf(f)) = -decode(f,MaxFiniteOf(f))`, not integer-code
  negation. In `Binary4p2sf`, those codes are `15` and `7`.
  Unsigned `MinFiniteOf` is the zero code.
- Implement both §3.2 naming forms as printers; dispatch uses format terms.
  Exclude Annex C's `K=2` examples from normative-format acceptance, because
  §3.1 requires `K>2`.

**Accept when** metadata agrees with §4.14, P3109 queries select the prescribed
datums, and Annex A.5's six `emax` cases agree with
`floorLog2(decode(MaxFiniteOf(f)))` on representative valid formats.
External value queries remain contract obligations until instantiated.

## 5. Projection specifications

The six nonstochastic modes are `NearestTiesToEven`, `NearestTiesToAway`,
`TowardPositive`, `TowardNegative`, `TowardZero`, and `ToOdd`. Each
of the three stochastic modes carries integers `N≥0` and `0≤R<2^N`.
Saturation is `SatFinite`, `SatPropagate`, or `SatNone`.
`RoundOf` and `SatOf` select the pair's components (§4.15).

For a result block of size `B`, distinct stochastic constructors carry
exactly `B` random operands, each within the same bound. Indexing `ρ[i]`
selects scalar `R_i`; nonstochastic specifications satisfy `ρ[i]=ρ`.
Scalar-result reductions use scalar specifications. §5.8's singleton lift
changes stochastic `R` to `[R]` and leaves nonstochastic modes unchanged.
Test bounds, lengths, indexing, and the lift.

## 6. Decode, encode, round, saturate, and project

**Codecs (§4.7.2, §4.7.6).** Preserve `DecodeAux`'s ordered exceptional
cases and normal/subnormal formulas with `T=x mod 2^(P-1)` and
`E_biased=x div 2^(P-1)`. Codes for negative datums recurse after subtracting
`2^(K-1)`; the integer codes themselves are nonnegative.

Guard every encode branch with `datum(f,X)`, the normative operand
restriction, including for infinities. Significand integrality alone is
insufficient: in `Binary8p4se`, `X=240` has integer significand `15`,
but the naive encoding is code `127` (infinity); the largest finite datum
is `224`. Reject `240`, unsupported infinities, negative unsigned operands,
and other unrepresentable values. Preserve the zero/NaN codes, positive-value
formulas, and signed recursion on their valid domains.

**External codecs (§4.8).** Model the rules present in the source: decode
NaNs as `NaN`, preserve infinity signs, and decode negative zero as zero;
encode zero as nonnegative zero and NaN as a quiet NaN. Preferred zero
payload/sign is a recommendation. A concrete codec selects a permitted quiet
NaN consistently. Ordinary finite codecs, datum membership, and code-valued
queries remain abstract where their definitions are delegated to references
[7] and [8]. Do not invent bit layouts or claim complete external execution.
External codecs are not bijections on all codes because of NaNs and signed
zero; state the appropriate datum and canonicalization laws.

**Rounding (§4.7.4).** Preserve zero and exceptional operands. Otherwise,
`Q=max(floorLog2(abs(X)),1-B)-P+1`, `S̃=abs(X)*2^(-Q)`,
`ν=S̃-floor(S̃)`, and `S=floor(S̃)+1` if `RoundAway(μ)`, else
`floor(S̃)`; return `sgn(X)*S*2^Q`. Transcribe all nine mode conditions,
including `RNITE`, the `P=1` `CodeIsEven` branch, and the distinct
stochastic thresholds. Rational evaluation is exact; general real decisions
retain their mathematical contracts until certified.

**Saturation (§4.7.5).** Preserve all 21 ordered cases. In-range handling
precedes mode-specific cases. Directed finite clipping under `SatNone`
precedes extended overflow. Cover NaN input, unsupported infinities, and
negative finite out-of-range inputs to unsigned extended formats: the latter
can produce NaN under `SatNone` when earlier directed clipping does not
apply. Do not reduce NaN coverage to two cases.

**Projection (§4.7.3).** Return a code, including the format's NaN code for
NaN input. Otherwise round, saturate using decoded minimum/maximum finite
bounds, then encode. Establish that the saturation output satisfies the
encoder's full datum precondition.

**Accept when**

- Encode-after-decode returns the original code for all valid codes in the
  14 four-bit formats (six signed, eight unsigned), and in
  `F4∪F8∪{Binary8p1uf}`. Check the datum-set characterization as well.
- Tables 4–7 agree over 16 rows and 14 format columns, including subnormal
  annotations. Exact entries are exact checks; approximate displayed entries
  use an explicitly recorded display tolerance.
- Table 3 agrees for valid parameters at `K∈{3,4,8,16}`, treating unavailable
  values as unavailable. §3.1 NOTE 2 gives `encode(2)=0x48` and
  `encode(+Inf)=0x7F` for `Binary8p4se`.
- Every rounding/saturation branch has boundary tests. Finite exhaustive
  tests specify modes and fixed stochastic `N,R` fixtures; unbounded random
  parameters require general arguments.
- §4.7.3's nearest-even NOTE checks cover the upper finite interval and,
  for smallest positive subnormal `m`, `abs(X)≤m/2 → 0`. Test zero, both
  endpoints `±m/2`, and points immediately inside and outside those bounds.
  Retain the positive `(m/2,m)` check and its negative counterpart for signed
  results. Formats without subnormals have separate `P=1` boundary tests.

## 7. Ordered behaviors and exact operations

For each source row `i`, define `match_i` from both its pattern and
explicit condition. Its effective guard is
`match_i and not(match_1 or ... or match_(i-1))`. Simplify only with an
equivalence argument. Sort-disjoint exceptional/finite cases remove many
overlaps; finite variables use `Real`, with rational evaluators as
specializations. Wildcards range over `XReal`. Undecidable symbolic guards
remain pending. `owise` does not replace intermediate priority.

Coverage tables refine `{Real,+Inf,-Inf,NaN}^n` by sign, zero, range, and
other guard conditions. Prove that each valid concrete input selects exactly
one effective case. Record unreachable source rows as shadowed, with a
justification, rather than forcing a rule for every row.

Implement Convert, Abs, Negate, CopySign, Add, Subtract, Multiply, Divide,
Recip, the ten extrema, Clamp, five comparisons, and eight predicates.
Preserve asymmetric extrema cases and the NaN handling needed by the block
maximum-finite reduction.

Use the simpler equivalent definitions explicitly given in the draft:

- `ωFMA(X,Y,Z)=ωAdd(ωMultiply(X,Y),Z)` (§4.10.6).
- `ωFAA(X,Y,Z)=ωAdd(ωAdd(X,Y),Z)` (§4.10.7).

These operate on decoded exact values without intermediate projection.
Retain the original behavior tables as independent expected-case checks
with clause-by-clause correspondence, including FMA's 17 initial NaN cases.
Comparing an equation with itself is insufficient. Check FAA's alternative
association independently.

**Accept when** coverage and applicable confluence checks succeed; binary
rational-core operations execute on all 256 `Binary4p2sf` code pairs; and
FMA/FAA match their original cases on all triples from that format's datums
plus exceptional values. Include division by zero, reciprocal of zero, and
finite division by infinity explicitly.

## 8. General real operations and certified evaluation

Specify Sqrt, RSqrt, exponentials, logarithms, trigonometric and hyperbolic
operations, π-scaled variants, Softplus, Hypot, ArcTan2, and ArcTan2Pi using
§§4.10.8–4.10.16. Some rational inputs give rational results; others require
symbolic reals. The shared signature supports `sin(π*X)`,
`ωLog(ωAdd(1,X))`, and `ωSubtract(ωExp(X),1)`. Raw real functions have
mathematical domain restrictions; their ω wrappers supply exceptional cases.

Preserve all special cases and all 17 ArcTan2 behavior rows. Ordinary Tan
has no rational poles, but TanPi has reachable half-integer poles:
`ωTanPi(1/2)=+Inf` and `ωTanPi(-1/2)=-Inf`. Test these and retain the
general symbolic pole rules. Exceptional operands need not give exceptional
results: `ωExp(-Inf)=0`, `ωRSqrt(+Inf)=0`, `ωTanh(+Inf)=1`, and
`ωArcTan(+Inf)=π/2`. Test the specified results, mixed finite/exceptional
tuples, and domain boundaries instead of asserting one result sort.

Provide exact rational Sqrt evaluation when a nonnegative rational in lowest
terms has square numerator and denominator. Verify both with integer square
roots and return their nonnegative quotient; other roots remain symbolic.
This evaluates an existing definition and adds no new semantics.

An optional enclosure evaluator supplies two independently checked facts:

1. The exact mathematical value lies in its rational enclosure `[lo,hi]`.
2. Every real value in that enclosure projects to one code under the fixed
   format and projection specification, including fixed random operands.

Endpoint agreement alone is insufficient. For `Binary4p2sf`, nearest-even
and `SatNone`, both endpoints of `[-100,100]` project to NaN while zero
projects to zero. Certify containment in a complete constant-projection
region, accounting for ties, saturation, signs, and exceptional outputs;
otherwise refine or leave the result undecided. Document the containment
algorithm and proof obligations. An interval representation is not
automatically a valid theory instance for exact real equality or arithmetic;
use it as a certificate-producing evaluator unless those additional
obligations are discharged.

**Accept when** source-derived special/domain cases agree, exact square
cases execute, and every returned enclosure result has both certificates.
Record Exp/Log fixtures, formats, modes, bounds, and undecided results.
No fixed enclosure width guarantees termination for all cases.

## 9. Scalar wrappers, Class, TotalOrder, and Next

- Generate wrappers from the normative inventory, with explicit parameters
  and domain guards. Numeric wrappers decode, apply the ω operation, and
  project once; Boolean/enumeration results follow their own schemas. Commit
  generator inputs and generator with output for reproducibility.
- `Class` implements Table 2's eight cases and partitions valid codes.
- Restrict `TotalOrder` to P3109 formats (§4.12.1). Build an independent
  list for each format with NaN first and remaining datums in numerical order.
  Compare every same-format pair with its list ranks. Agreement establishes
  totality, reflexivity, antisymmetry, and transitivity on each format's value
  set without cubic enumeration: an eight-bit format needs 256² pair checks.
  Also test independently parameterized input formats using decoded numerical
  order with NaN first. Include equal datums with different codes, unequal
  datums, NaN pairs, and infinities. Equal datums in different formats compare
  True in both directions; do not impose antisymmetry on their distinct
  format-tagged representations.
- Implement §4.16's ordered code-point Next rules. Guard `SmallestNegative`
  to signed formats and record shadowed cases. Do not extend P3109 code
  arithmetic to external formats without a source-defined rule or an explicit
  unresolved contract.

**Accept when** wrappers match signatures and Class partitions each format in
`F4∪F8`. Check TotalOrder on every code pair for every ordered pair of formats
in that set, using per-format ranks for equal formats and decoded ordering
for mixed formats. For Next, reuse each format's independent numerical list
with NaN removed: every non-NaN code must advance to its immediate neighbor
in the specified direction, or return NaN if none exists. Test NaN propagation
separately. These adjacency checks include extrema, infinities, and zero,
and imply the inverse laws wherever both steps return non-NaN.

## 10. Blocks and scaled operations

Encoded blocks are `(s,[x_1,...,x_B])` with Step 3's formats and validity.
Decoded sequences contain `XReal` values. Check all operand/result lengths
and domains, including supplied result scales. Implement §5.2's left fold
with each caller's seed (`0`, `1`, or `NaN`); do not reassociate it.

`ωBlockDecode` computes each
`ωMultiply(decode(fs,s),decode(f,x_i))`.
`ωBlockProject` first decodes `S=decode(fs,s)`, then computes:

| First applicable condition | `Z_i` |
|---|---|
| `S` is NaN or `X_i` is NaN | NaN |
| `S=0` | 0 |
| `S=±Inf` | `sgn(X_i)*sgn(S)` |
| Otherwise | `ωDivide(X_i,S)` |

Return element codes `project(fr,ρ[i],Z_i)`. A NaN element therefore
survives a zero scale. Infinite scale and infinite non-NaN element give
`Z_i=±1` before projection, as specified; this differs from dividing
infinities and is not an ambiguity.

Implement §§5.5–5.8 from their schemas: conversions, scalar-result reductions,
dot product, listed unary/binary/ternary elementwise substitutions, and
scaled operations with `B=1`. Elementwise operations copy the supplied
result scale. Max-absolute-finite conversion uses
`S=reduce(ωMaximumFinite,[NaN,M_1,...,M_B])`, projects the scale, and passes
it to block projection. Preserve every projection's specified position.

**Accept when** shape and random-length guards are checked; special
scale/element combinations agree with the table; and all §5.4.2 and §5.5.3
NOTEs have evaluated checks or documented source findings. Require §5.4.2
NOTE 2 (PDF p. 63) to pass for P3109 formats: with an infinite scale, every
nonzero, non-NaN result element is `±1`. Unsigned projection of `-1` yields
zero or NaN, already excluded by the NOTE; it is not a counterexample.

Record the actual conflict in §5.5.3 NOTE 2 (PDF p. 66). With `B=1`, all
formats `Binary8p4se`, input `[+Inf]`, scale projection
`(NearestTiesToEven,SatFinite)`, and element projection
`(NearestTiesToEven,SatNone)`, the scale is `224` and the result element is
`+Inf`, outside the NOTE's stated alternatives `±1` and `±MaxFiniteOf(fr)`.
Preserve the normative behavior and retain this counterexample as a source
finding and regression check.

For `B=1` and unit scales, compare BlockDotProduct with exact ωMultiply
followed by one projection (equivalently scalar Multiply), and ScaledAdd
with scalar Add, over all `Binary4p2sf` pairs with matching result formats
and projection specifications.

## 11. Termination, confluence, and coverage

- Inventory every recursive definition and its measure, including
  `floorLog2`, signed decode/encode recursion, folds, and any sequence or
  enumeration helpers. Do not claim an exhaustive list before implementation.
- Apply the Maude Termination Tool, Church-Rosser Checker, and Sufficient
  Completeness Checker where supported by the actual modules and imported
  theories. Record versions, assumptions, scope, and results.
- Supply manual arguments for obligations tools cannot discharge, including
  conditional coverage. Investigate critical pairs without assuming they
  all arise from one translation scheme.
- State completeness relative to valid concrete domains. Partial encode,
  symbolic guards, uninstantiated external contracts, and undecided enclosure
  evaluations do not constitute executable-totality claims.

**Accept when** each executable component has a termination argument,
confluence evidence, and domain coverage, with other obligations explicit.
A clean test run alone does not establish these properties.

## 12. Source-derived checks and examples

Distinguish normative failures, translation errors, and informative-source
findings. Investigate failed NOTEs against normative behavior, retaining
source conflicts as findings and testing the specified behavior.

| Check | Source | Scope |
|---|---|---|
| P3109 datum/code bijection and rejection of non-datums | §3.1, §4.7; Annex B cross-check | Step 6 |
| `1` code is `2^(K-2)` signed or `2^(K-1)` unsigned | Annex A.5, Table 3 | all valid formats with `K≤8` |
| FMA/FAA original case tables and compositions | §§4.10.6–4.10.7 | Step 7 |
| Division by zero/infinity and ArcTan2 infinite pairs | §§4.10.5, 4.10.15 | direct ω tests and applicable wrappers |
| Decoded signed minimum finite is negative decoded maximum finite | §4.14 | all valid P3109 formats with `K≤8` |
| Next at maximum finite and infinity | §4.16 | `F4∪F8` |
| Block scale, NaN, infinity, max-absolute-finite properties | §§5.4.2, 5.5.3 | Step 10, with source findings |
| Exp partitions and seven positive subnormals | Annex D.1 | reproduce analytic `κ=4` count and justify cut points |
| Partitioned block-dot declaration | Annex D.2 | declaration fixture; assumed `κ=3` is not computed |
| Recommended accuracy bounds | Annex E | optional checks, not conformance requirements |

D.1's analysis is not exhaustive binary32 Exp evaluation; external
representation and exact transcendental decisions retain their obligations.
D.2 supplies no concrete approximate implementation from which to recompute
its assumed `κ=3`. Do not invent one to make the example pass. Even the
restricted four free element operands have 145 choices each:
`145^4=442,050,625` tuples. A later exhaustive experiment needs an explicit
implementation and cost assessment.

## 13. Conformance and approximation declarations

Separate required specialization coverage (§4.5), exact behavior of supplied
operations (§4.6), and approximate numeric declarations (§4.4). Declaration
presence alone does not establish conformance.

Use `F4={Binary4p2sf}`, `F8={Binary8p4se,Binary8p3se}`,
`Fs={Binary8p1uf}`, nonempty `FX⊆{binary32,binary16,BFloat16}`, and
`ρ=(NearestTiesToEven,SatNone)` for §4.5's required set:

| Operations | Required specialization constraints |
|---|---|
| Convert, Recip | input and result independently in `F4∪F8∪FX` |
| Negate, Abs | same input/result format in `F4∪F8` |
| Add, Subtract, Multiply | inputs in `F4∪F8`; result in `F8∪FX` |
| FMA, FAA | first two inputs in `F4∪F8`; third input and result share a format in `FX` |
| Ten extrema | both inputs and result share a format in `F4∪F8` |
| Five comparisons | both inputs share a format in `F4∪F8` |
| Eight predicates, NextGreaterThan, NextLessThan | each format in `F4∪F8` |
| Twelve format queries | each format in `F4∪F8∪FX` |
| ScaledAdd, ScaledSubtract, ScaledMultiply | scale formats in `Fs`; element inputs in `F4∪F8`; result in `F8∪FX` |

Every supplied exact specialization must equal the defined result on every
valid operand tuple, including supplied specializations outside the required
set. §4.6 recommends attestation; equality itself is mandatory. Approximate
implementations have separate records and different names as required by
§4.4; a name indicating approximation is a §4.6 recommendation. Exact and
nonnumeric operations do not require approximation renaming or κ records.

Implement `MatchOnInfinity`'s four cases. For an approximate numeric
specialization, check NaN matching first (`κ=NaN` on mismatch), then
infinity matching (`κ=∞` on mismatch). Otherwise use the draft's finite-result
domain `I`, finite value set `V`, and half-open interval count:

`κ=max_{x∈I} #(((â(x),ã(x)] ∪ [ã(x),â(x))) ∩ V)`.

Require approximate results on `I` to belong to `V`. P3109 finite-value
ranks give the count exactly. Do not assume P3109 Next or TotalOrder defines
external counting; discharge external value-set and ordering obligations
separately. Log unresolved cases such as empty `I` when the source gives
no maximum convention. Partition declarations require disjointness and
coverage. Multiple floating-point results use NaN precedence, then infinity,
then the maximum component κ.

**Accept when** coverage checks reproduce §4.5, including an
`FX={binary32}` fixture, and malformed/missing specialization and declaration
fixtures are rejected. D.2 checks structure only. Reports distinguish proved,
failed, and pending behavioral/κ obligations. Pending external or real
contracts prevent a fully verified conformance claim.

## 14. Final review and deliverables

Deliver the source manifest, modules/contracts, reproducible generators where
used, traceability matrix, tests, `coverage.md`, and `deviations.md`.
Use statuses such as `modeled`, `tested`, `recommendation`,
`source-finding`, `excluded`, and `pending-contract`, with appropriate
artifact links and reasons. A symbolic definition can be modeled while its
execution obligation remains pending; report these separately.

Review every source behavior against its equation family, every equation
against its source, and every acceptance criterion against its evidence.
Retain the K=2 exclusion, external limitations, enclosure obligations, NOTE
findings, and D.2's assumed κ. Encoder partiality and infinite block-scale
handling are specified behaviors, not optional choices.

**Done when** rational executable tests pass, applicable proof checks and
manual arguments are recorded, source findings have dispositions, and
unfulfilled contracts are listed. Report executable coverage separately from
symbolic specification and full conformance. Neither a single Maude run nor
an informative example closes remaining obligations.
