# Plan: IEEE P3109/D1 as a Maude specification

Source: `docs/other/IEEE_D1.md`, the September 2026 revised-draft rendering
(header comment, lines 1–7). No other input governs this plan. Where this
document says "the draft", it means that file.

Target: a Maude 3 specification — functional modules, one parameterized theory,
and a test module — that a reader of the draft can check line by line against
it, and that Maude can execute over the finite formats the draft's conformance
clause names.

## 0. Governing rules

These rules resolve every judgement the later steps call for. They are stated
once so the steps can be short.

1. **Normative is §1–§5. Annexes are checks, never sources.** §1.2 makes *shall*
   the only requirement word. Annex A–G are marked informative. Their tables
   and examples become test vectors; their prose never becomes an equation.
2. **A *should* is recorded, not modelled.** §4.8.2's preferred NaN payload,
   §4.6's query-by-string, Annex E's error bounds: each becomes a comment at
   the point it would apply, marked `should`, with no equation.
3. **The draft's text wins over its NOTEs; a NOTE that contradicts the text is
   a finding, not a rule.** NOTEs are used as executable property checks (Step 12).
4. **Ambiguity is logged, never silently resolved.** Every place the
   implementer must choose an interpretation goes into `deviations.md` with the
   §ref, the alternatives, the choice, and the reason. The spec carries the
   choice as a comment at the equation.
5. **Every equation carries its §ref.** The traceability matrix (Step 1) is the
   review instrument for the whole effort; a matrix row with no equation, or an
   equation with no row, is a defect.
6. **Exactness is preserved wherever the draft's mathematics is exact, and
   made explicit wherever it is not.** Where a value is a rational, Maude's
   `RAT` represents it exactly. Where a value is an irrational real, the spec
   does not pretend to compute it (Step 8).
7. **Ordered pattern lists are translated so that order no longer matters.**
   §4.3.2 gives "first match in document order wins"; Maude equations are
   unordered. The translation scheme (Step 7) must make the equation set
   confluent, and confluence must be checked, not assumed.

## 1. Freeze the source and build the traceability matrix

**Do.**

- Record the SHA-256 of `IEEE_D1.md` in the header of every Maude file. A
  later draft is a new revision of the spec, not an edit.
- Walk §1–§5 and extract one row per: *shall* sentence; Signature/Behavior
  block; formula in a `where` clause; NOTE stating a property. Columns:
  `§ref`, `kind` (requirement / behavior / formula / property), `text`,
  `module`, `equation-id(s)`, `test-id(s)`, `status`.
- Extract the informative material separately: Table 3–8 (Annex B, C),
  §3.1 NOTE 2 examples (`2.0_Binary8p4se = 0x48`, `Inf_Binary8p4se = 0x7F`),
  §4.14 table, A.5 `emax` cases, D.2. These populate `test-id`, never `equation-id`.

**Accept when** every Behavior block in §4.7–§4.16 and §5.4–§5.8 has a row, and
the operation inventory matches Annex F's listing exactly (Annex F is used
here only as a completeness cross-check of §4–§5).

## 2. Module layout

One file per module, loaded in this order. Names are fixed now so the matrix
can reference them.

| Module | Content | Draft §§ |
|---|---|---|
| `XREAL` | closed extended reals over `RAT` | 2.1, 2.3, 3.1 |
| `FORMAT` | formats, validity, naming, format-level ops | 3.1, 3.2, 4.14 |
| `PROJSPEC` | rounding modes, saturation modes, projection specs | 4.2, 4.15 |
| `ROUND` | ωRoundToPrecision | 4.7.4 |
| `SATURATE` | ωSaturate | 4.7.5 |
| `CODEC` | ωDecode, ωEncode, external decode/encode, ωProject | 4.7.2, 4.7.3, 4.7.6, 4.8 |
| `OMEGA-EXACT` | ω-operations closed over ℚ ∪ {±∞, NaN} | 4.9, 4.10.1–4.10.7, 4.10.8 (Recip), 4.11, 4.12, 4.13 |
| `OMEGA-REAL` (fth) + views | ω-operations with irrational results | 4.10.8 (Sqrt, RSqrt), 4.10.9–4.10.16 |
| `OPS` | `Op(x…) → ωProject(ωOp(ωDecode…))` wrappers; Class; Next | 4.3, 4.9–4.16 |
| `BLOCK` | sequences, `reduce`, ρ[i], block internals, conversions, reductions, elementwise, scaled | 5 |
| `CONFORMANCE` | κ, MatchOnInfinity, declarations, §4.5 required set | 4.4, 4.5, 4.6 |
| `TESTS` | vectors from Step 1, property checks from Step 12 | Annex B–E, NOTEs |

Modelling scope, stated once: no flags, no interrupts, no side effects
(§4.1 NOTE 3); no hardware realization; no randomness — `R` is an operand
(§4.7.4 Details), never generated.

## 3. `XREAL`: the closed extended reals

**Do.**

- `sorts Special XReal . subsort Rat < XReal . subsort Special < XReal .`
  `ops NaN +Inf -Inf : -> Special [ctor] .`
- `sgn`, `abs`, `floor`, `IsOdd`, `IsEven` over `Rat`/`Int` per §2.3.
- `floorLog2 : Rat -> Int` for positive rationals, defined by a terminating
  power-of-two bracketing (repeated doubling/halving of the comparand), not by
  any real logarithm. This is the one place §4.7.4 and §4.7.6 need a
  logarithm, and for rationals it is decidable.
- Comparisons `<`, `<=`, `=` lifted to `XReal` only where the draft uses them
  on finite operands; special operands are always matched by pattern, never
  compared (see Step 7).

**Why `RAT`.** Every datum is `S × 2^{1−P} × 2^E` (§3.1), a dyadic rational.
Add, Subtract, Multiply, FMA, FAA, CopySign, Abs, Negate, the extrema, Clamp,
and all comparisons and predicates stay in ℚ. Divide and Recip leave the
dyadics but stay in ℚ. So Group A and Group B's Divide/Recip are exact in
Maude with no approximation anywhere.

**Accept when** `floorLog2` is proved terminating (Step 11) and agrees with
hand-computed values at 1, 3/4, 2^{−20}, 2^{20}+1.

## 4. `FORMAT`

**Do.**

- `op Binary : Nat Nat Signedness Domain -> Format [ctor] .` with
  `ops Signed Unsigned : -> Signedness . ops Finite Extended : -> Domain .`
- Validity (§3.1) as a membership: `K > 2`; `0 < P < K` if Signed,
  `0 < P <= K` if Unsigned. An invalid `Binary(…)` term has kind `[Format]`
  and no equation applies to it. This is deliberate: misuse must surface as
  an unreduced term, not as a wrong number.
- `ops binary64 binary32 binary16 BFloat16 : -> Format [ctor] .`
- §4.14 table, both columns, as equations: `BitwidthOf`, `PrecisionOf`,
  `SignednessOf`, `DomainOf`, `ExponentBitwidthOf`,
  `TrailingSignificandBitwidthOf`, `ExponentBiasOf` (`2^{K−P−1}` signed,
  `2^{K−P}` unsigned, §3.1).
- `MaxFiniteOf`, `MinFiniteOf`, `MinPositiveOf`, `MaxSubnormalOf`,
  `MinNormalOf` return **code points** (§4.14: "floating-point values, in the
  format f"). Define each by its datum (largest finite `S×2^{1−P}×2^E` etc.)
  and `ωEncode`; `MaxSubnormalOf` returns `ωEncode(NaN)` when `P = 1` (no
  subnormals, §4.14). `MinFiniteOf` = `0` for unsigned formats (§4.14).
- Naming (§3.2) as a printing function `name : Format -> String` only; it is
  not used for dispatch.

**Excluded.** K = 2 (Annex C). §3.1 requires K > 2; Annex C's formats are
outside the datum-set definition and its peculiarities (`MinNormalOf = NaN`,
missing 1.0) would otherwise force equations the normative text does not
justify. Logged in `deviations.md` as an exclusion, not an interpretation.

**Accept when** the §4.14 table is reproduced for `Binary8p4se`, `Binary8p3se`,
`Binary4p2sf`, `Binary8p1uf`, and the four external formats, and A.5's `emax`
table is reproduced as `floorLog2(ωDecode(MaxFiniteOf(f)))` for one format per
row of that table.

## 5. `PROJSPEC`

**Do.**

- `RoundingMode` with constructors `NearestTiesToEven`, `NearestTiesToAway`,
  `TowardPositive`, `TowardNegative`, `TowardZero`, `ToOdd`,
  `StochasticA(N, R)`, `StochasticB(N, R)`, `StochasticC(N, R)` where
  `N R : Nat` and a membership requires `R < 2^N` (§4.7.4 Details).
- For blocks (§5.3) a second family `StochasticA(N, RList)` etc., with the
  membership `∀i. R_i < 2^N`, and `ρ[i]` selecting `R_i`. §5.8's `ρ′` is the
  singleton-list lift. These are separate constructors, not a coercion: the
  draft says the *meaning* of `R` is altered, and the spec should not let a
  scalar `R` be silently indexed.
- `SaturationMode`: `SatFinite`, `SatPropagate`, `SatNone`.
- `Projection` as the pair; `RoundOf`, `SatOf` (§4.15).

## 6. `ROUND`, `SATURATE`, `CODEC`

These three are the semantic core and the place where the draft's arithmetic
is entirely exact. They are written directly from the `where` clauses, one
equation per line of the draft, in the draft's order, with the §ref.

**`ROUND` (§4.7.4).**

- `ωRoundToPrecision(P, B, μ, X)` for `X ∈ {0, −∞, +∞, NaN}` returns `X`.
- Otherwise `Q = max(floorLog2(|X|), 1 − B) − P + 1`; `S̃ = |X| × 2^{−Q}`
  (exact in `RAT`); `ν = S̃ − ⌊S̃⌋`; `S = ⌊S̃⌋ + 1` if `RoundAway(μ)` else `⌊S̃⌋`;
  `Z = sgn(X) × S × 2^Q`.
- `RoundAway` per mode exactly as listed, including `CodeIsEven`'s `P = 1`
  branch `(⌊S̃⌋ = 0) or IsEven(Q + B)` and `RNITE`. The `P = 1` branch is a
  known subtlety; it gets its own test row.
- Stochastic modes take `R` from the constructor.

**`SATURATE` (§4.7.5).**

- Nineteen rules. Rule 2 (`Mlo ≤ X ≤ Mhi → X`) precedes every mode-specific
  rule; the translation must keep it so (Step 7's scheme handles it: every
  later finite-`X` rule carries `X < Mlo` or `X > Mhi` explicitly, as the
  draft already writes them).
- `SatNone` with `TowardZero`/`TowardNegative` on `X > Mhi, X ≠ +∞` → `Mhi`
  (and the mirror) come *before* the `Extended → ±∞` rules. Keep the
  draft's order in the source comments so a reviewer can see the priority
  being encoded.
- `Unsigned, Extended, −∞ → NaN` and the `Finite → NaN` catch-all are the two
  places a saturation produces NaN; both get test rows.

**`CODEC`.**

- `ωDecode` (§4.7.2): the `DecodeAux` cases on `(Σ, Δ, x)` in order, then the
  general case with `T = x mod 2^{P−1}`, `E_biased = x ÷ 2^{P−1}`, the
  subnormal/normal split. Negative code points recurse on `x − 2^{K−1}`.
- `ωEncode` (§4.7.6): total on `Special` and `0`; on positive `X` it computes
  `E`, `S = X × 2^{−E} × 2^{P−1}`, `T = S mod 2^{P−1}`. **`S` must be an
  integer** — the NOTE's precondition. Model it: `ωEncode` on a positive `Rat`
  is guarded by `S ∈ Nat`; a non-datum argument stays unreduced at kind
  `[Nat]`. This is the mechanism that turns a misuse of `ωEncode` into a
  visible term instead of a wrong code point, and it is why `ωProject`, not
  `ωEncode`, is the public seam.
- `ωDecodeExternal` / `ωEncodeExternal` (§4.8): external formats use the
  IEEE 754 layout — sign bit, biased exponent with all-ones reserved, `−0`,
  NaN payloads — none of which the P3109 layout has. Write a separate decoder
  over the IEEE fields; map any NaN payload → `NaN`, `−0 → 0`, exponent
  all-ones with zero significand → `±Inf`. `ωEncodeExternal` is defined only
  on datums of `f` (§4.8.2 NOTE) and returns the positive-zero code for `0`
  and *a* quiet NaN for `NaN` — the *should* about payload is a comment
  (Rule 2).
- `ωProject` (§4.7.3): `NaN → NaN`; else `Encode(Saturate(Sat, Round, RoundToPrecision(P, B, Round, X), Σ, Δ))`
  with `Mlo/Mhi = ωDecode(MinFiniteOf/MaxFiniteOf(f))`.

**Accept when**

- `ωEncode(ωDecode(c)) = c` for every `c ∈ 0..2^K−1`, for every format in
  F4 ∪ F8 ∪ {Binary8p1uf} and for all 32 valid `Binary(4, P, Σ, Δ)`. This is
  Annex B's "bijective" claim, and since the map is between finite sets of
  equal size it is the whole of it.
- Tables 4–7 reproduce exactly (16 rows × 11 formats), including which rows
  are subnormal.
- Table 3 reproduces for K ∈ {3, 4, 8, 16}.
- §3.1 NOTE 2: `ωEncode_{Binary8p4se}(2.0) = 0x48`, `ωEncode(+∞) = 0x7F`.
- §4.7.3 NOTE 1 and NOTE 2 hold under `NearestTiesToEven` for `Binary8p4se`:
  a value strictly between `Mhi` and `Mhi + ½ulp` projects to `Mhi`; a value
  strictly between the smallest subnormal and its half rounds to the smallest
  subnormal; a value at or below that half rounds to `0`.

## 7. `OMEGA-EXACT`: translating ordered pattern lists

This is the step with the highest correctness risk, and the scheme is fixed
here rather than left to each operation.

**The problem.** §4.3.2: "the first matching pattern in the order presented
defines the behavior." Maude has no rule order; `owise` marks only a final
default. A naive line-by-line transcription is unsound: `ωAdd(X, Y) → X + Y`
would also match `ωAdd(+∞, −∞)`.

**The scheme.**

1. **Sort-disjointness does most of the work.** With `NaN`, `+Inf`, `-Inf`
   as constructors of `Special` and finite values of sort `Rat`, a pattern
   `ωAdd(X:Rat, Y:Rat)` cannot match a special operand at all. Every
   "`X, Y` finite" fall-through rule in the draft becomes an equation whose
   variables are declared `Rat`. Every special-value rule becomes an equation
   on the constructors. The two classes cannot overlap.
2. **Wildcard `∗`** becomes a variable of sort `XReal` (§4.3.2.3);
   **set inclusion** `x ∈ {−Inf, Inf}` becomes two equations or a subsort
   `Infinite < Special` (§4.3.2.2). `±∞` in the draft is that subsort.
3. **Residual overlap is between `XReal`-wildcard rules and `Rat` rules, and
   between rules with `if` guards.** For each operation, list its rules in
   draft order; for rule *n*, add to its condition the negation of every
   earlier rule's pattern *that it can still match*. In practice this is
   small: e.g. `ωMultiply(+∞, Y) if Y > 0`, `if Y = 0`, `if Y < 0` are already
   exclusive; `ωClamp`'s wildcard rules need the explicit `X ≤ Hi` / `X > Hi`
   the draft already supplies.
4. **Never use `owise` for anything but the draft's own last, unguarded
   rule**, and only when that rule's variables are all `Rat`.
5. **Check, do not assume.** Run the Church-Rosser Checker on each ω-module
   and the Sufficient Completeness Checker where equations are unconditional.
   For conditional equations SCC does not decide completeness; supply a
   per-operation case-split argument in a comment: the operand sorts are
   `{Rat, +Inf, -Inf, NaN}^n`, and each cell of that product is covered by
   exactly one rule. Record the argument as a table in `deviations.md`'s
   companion `coverage.md`.

**Operations in this module** (all exact over ℚ): Convert (§4.9), Abs,
Negate (§4.10.1), CopySign (§4.10.2), Add, Subtract (§4.10.3), Multiply
(§4.10.4), Divide (§4.10.5), FMA (§4.10.6), FAA (§4.10.7), Recip (§4.10.8),
the eight extrema and Clamp (§4.11), the five comparisons (§4.12), the
predicates (§4.13). `ωLogOnePlus` and `ωExpMinusOne` are in Step 8 because
they wrap irrational functions; their *structure* (`ωLog(ωAdd(1, X))`) is
kept verbatim.

**Draft subtleties to carry as comments and test rows.**

- `ωDivide(∗, 0) → NaN` and `ωRecip(0) → NaN`, not `±∞` (§4.10.5 NOTE 2, A.3).
- `ωMinimumMagnitude(±∞, Y) → Y` but `ωMaximumMagnitude(+∞, ∗) → +∞`: the two
  are not mirror images (§4.11.2). Transcribe literally.
- `ωMinimumFinite(NaN, NaN) → NaN` but `(NaN, Y) → Y` (§4.11.3); the seed of
  `reduce(ωMaximumFinite, [NaN, M_1, …])` in §5.5.3 depends on this.
- `ωFMA(X, +∞, +∞) if X < 0 → NaN` family: fourteen NaN rules before the
  first `+∞` rule. Keep draft order in the comment block.

**Accept when** every ω-operation passes CRC; every unconditional ω-module
passes SCC; every conditional one has a coverage table; and for `Binary4p2sf`
(16 codes) every binary operation is evaluated over all 256 operand pairs
without an unreduced term.

## 8. `OMEGA-REAL`: functions the reals need and Maude cannot compute

`ωSqrt`, `ωRSqrt`, `ωExp`, `ωExp2`, `ωLog`, `ωLog2`, `ωLogOnePlus`,
`ωExpMinusOne`, all of §4.10.10–§4.10.13, `ωHypot`, `ωArcTan2`, `ωArcTan2Pi`
produce irrationals at almost every rational argument. Maude cannot represent
them, and a spec that silently substituted floating-point approximations
would violate Rule 6.

**Do.**

- A functional theory `fth OMEGA-REAL` declaring `sqrt exp log sin … : Rat -> Real`
  over a sort `Real` with `Rat < Real < XReal`, and **as axioms** every
  special-value rule the draft gives — `ωLog(0) → −∞`, `ωArcTan(+∞) → π/2`,
  `ωTanh(±∞) → ±1`, `ωArcTanh(±1) → ±∞`, the domain-restriction NaNs
  (`ωLog(X) if X < 0`, `ωArcSin(X) if |X| > 1`, `ωArcCosh(X) if X < 1`,
  `ωRSqrt(X) if X ≤ 0`), the `ωArcTan2` sixteen-rule table. These are exact
  and executable; only the final "`→ log_e X`" line is symbolic.
- `π` as a constant of sort `Real`; `π/2`, `−π`, `1/2` etc. as the draft
  writes them.
- The `ωTan(X) if cos X = 0` rules (§4.10.10, §4.10.12) are transcribed with
  the NOTE that no rational `X` satisfies them; they are axioms of the theory
  with no executable instance, exactly the draft's stance ("for documentation,
  and to support formal verification").
- The wrappers `Op(x) → ωProject(ωOp(ωDecode(x)))` therefore reduce to a
  normal form containing an unreduced `ωProject(f, ρ, exp(X))` on finite
  arguments. That is the specification: it says *which* real must be
  projected, exactly.
- **One view, for tests only**, `OMEGA-REAL-ENCLOSURE`, instantiates the
  theory with an interval enclosure `[lo, hi]` of rationals and defines
  `ωProject` on an enclosure as: the projection of `lo` if it equals the
  projection of `hi`, else unreduced. This decides the result whenever the
  enclosure does not straddle a rounding breakpoint, and refuses otherwise —
  it never guesses. The view's width parameter is a test-harness knob. This
  view is *not* part of the specification and its file says so in its header.

**Sqrt exception.** When `X` is a perfect square in ℚ, `ωSqrt(X)` is rational.
An equation `sqrt(X) = q if q × q = X` for `q` the integer-square-root
candidate makes those cases exact and executable without a view. Optional;
if included, log it as an addition that changes no defined result.

**Accept when** the special-value axioms alone reduce every operand tuple in
`Special^n ∪ (domain-violating Rat)^n` to a `Special`, checked exhaustively
over `Binary4p2sf`; and the enclosure view reproduces the finite-argument
rows of a hand-computed table for `Exp` and `Log` over `Binary8p4se` at
enclosure width `2^{−40}` with no refusals.

## 9. `OPS`: wrappers, Class, Next

**Do.**

- One equation per operation of the form the draft gives, e.g.
  `Add(fx, fy, fr, ρ, x, y) = ωProject(fr, ρ, ωAdd(ωDecode(fx, x), ωDecode(fy, y)))`.
  Operation parameters are explicit arguments (§4.3.2.4). Generate these from
  a table rather than by hand; the table is the Annex F listing, restricted to
  §4's scalar operations, and the generator output is committed, not the
  generator.
- `TotalOrder` (§4.12.1): the NaN rules, then `CompareLessEqual`. Note NOTE 2:
  undefined for external formats — make the membership exclude them.
- `Class` (§4.13.1): Table 2 as eight exclusive conditions in the order given;
  the conditions are already disjoint by construction of the predicates.
- `NextGreaterThan` / `NextLessThan` (§4.16): the `Aux(Σ, Δ, x)` rule lists in
  draft order, on code points with integer `±1`. `SmallestNegative` is
  defined only for signed formats (NOTE 1); make it a membership so an
  unsigned use stays unreduced.

**Accept when** for each format in F4 ∪ F8: `TotalOrder` is total, reflexive,
antisymmetric and transitive over all code points (exhaustive, 256³ for K = 8
is 16.7M — restrict transitivity to K ≤ 6 exhaustively and to sampled triples
for K = 8, and say so); `Class` partitions every code point into exactly one
class; `NextLessThan(NextGreaterThan(x)) = x` for every `x` where the draft
defines both as non-NaN.

## 10. `BLOCK`

**Do.**

- `Block = (s, XRealList)`; `reduce` as the left fold of §5.2, verbatim, seeded
  as each caller seeds it (`0`, `1`, `NaN`). Do not reassociate.
- `ρ[i]` (§5.3) as in Step 5.
- `ωBlockDecode` (§5.4.1): `Z_i = ωMultiply(ωDecode(s), ωDecode(x_i))`.
- `ωBlockProject` (§5.4.2): four cases on `S`, in order — NaN, zero, `±∞`
  (`sgn(X_i) × sgn(S)`), else `ωDivide(X_i, S)`; then `ωProject(fr, ρ[i], Z_i)`.
  **Flag** in `deviations.md`: when `S = ±∞` and `X_i = ±∞`, this rule yields
  `±1`, whereas `ωDivide(±∞, ±∞)` is `NaN`. The draft's text is explicit; the
  spec follows it and the test suite pins it.
- §5.5.1–5.5.3, §5.6.1–5.6.2, §5.7's schema over the listed unary/binary/
  ternary substitutions, §5.8's `ScaledOp` with `B = 1` and `ρ′`. The elementwise
  schema is one parameterized equation family, not fifty transcriptions.
- `ConvertToBlockMaxAbsFinite`'s `S = reduce(ωMaximumFinite, [NaN, M_1, …])`
  reproduces NOTEs 1–4 of §5.5.3 — each becomes a test row.

**Accept when** the §5.5.3 NOTEs hold; `BlockDotProduct` with `B = 1` and
unit scales equals `Multiply` then `Project` for every operand pair in
`Binary4p2sf`; and `ScaledAdd` with scale `1` equals `Add` over the same.

## 11. Termination and confluence

**Do.**

- Maude Termination Tool on every functional module. `floorLog2`, the
  `DecodeAux` recursion on `x − 2^{K−1}`, and `reduce` are the only recursive
  definitions; each has an obvious measure, stated in a comment.
- Church-Rosser Checker on every module. Any critical pair reported is a
  Step 7 translation error until proved otherwise.
- Sufficient Completeness Checker on the unconditional modules; coverage
  tables (Step 7.5) for the rest.

**Accept when** all three tools report clean, and `coverage.md` has a table
for every conditionally defined ω-operation.

## 12. Property verification against the draft's own claims

The draft states properties in NOTEs and in prose. Each becomes a `red` or
`search` over the finite formats. These are checks on the *translation*: if
the draft's own claim fails on the Maude spec, either the translation is
wrong or the draft is, and both are findings.

| Claim | Where | Check |
|---|---|---|
| Encoding is a bijection `D_f ↔ 0..2^K−1` | §3.1, Annex B | Step 6 |
| `1.0` encodes at `2^{K−2}` (signed) / `2^{K−1}` (unsigned) | A.5, Table 3 | all valid `K ≤ 8` |
| `ωFMA(X,Y,Z) ≡ ωAdd(ωMultiply(X,Y),Z)` | §4.10.6 | exhaustive over `XReal` tuples drawn from `Binary4p2sf` datums ∪ Special |
| `ωFAA` ≡ `ωAdd(ωAdd(X,Y),Z)` ≡ `ωAdd(X,ωAdd(Y,Z))` | §4.10.7 | same |
| `Divide(x, ±Inf) = 0` for finite `x`; `Divide(x, 0) = NaN` | §4.10.5 NOTEs | all `x` in F8 |
| `ArcTan2(±Inf, ±Inf) = NaN`, consistent with Divide | §4.10.15 NOTE 2 | direct |
| `MinFiniteOf` = `−MaxFiniteOf` (signed); `= 0` (unsigned) | §4.14 | all valid `K ≤ 8` |
| `NextGreaterThan(Inf) = NaN`, `NextGreaterThan(MaxFinite) = Inf` (extended) / `NaN` (finite) | §4.16 NOTE 2 | F4 ∪ F8 |
| Block NOTEs 1–4, §5.4.2 NOTEs 1–2 | §5 | Step 10 |
| D.2: `κ = 3` over `I_0` | Annex D | exhaustive over `I_0` (four operands, each `|·| ≤ 2` in `Binary8p4se`), requires a concrete approximate implementation — supply the simplest one that matches the example's premise, and document that the example does not fully specify it |

**Not checked, and why.** D.1's `κ = 4` partitions binary32 inputs by
irrational cut points; the count is derivable by hand from `Binary8p4se`'s
seven subnormals, but an exhaustive check over 2^32 inputs through `Exp` is
neither feasible nor exact. Record as a hand-verified note. Annex E's bounds
are recommendations (Rule 2).

## 13. `CONFORMANCE`

**Do.**

- `MatchOnInfinity` (§4.4) as four rules.
- `κ` for a specialization as: over the finite-result operand set `I`, the
  maximum count of values of `V` in the half-open interval between `â(x)` and
  `ã(x)` — computable exactly over a finite format by walking code points with
  `NextGreaterThan`. `κ = NaN` / `κ = ∞` per the two "does not match" clauses.
  Multi-result operations take `max_m κ[m]` with the NaN/∞ precedence stated.
- A `Declaration` record: specialization, identifier (must differ from the
  operation's name — §4.4 *shall*), `κ` or a partition `{I_i : κ_i}` whose
  parts are checked disjoint and covering.
- §4.5's required set as a predicate `conforms(Decls, F_X)` that checks every
  listed specialization is declared, with `ρ = (NearestTiesToEven, SatNone)`,
  `F4 = {Binary4p2sf}`, `F8 = {Binary8p4se, Binary8p3se}`, `F_s = {Binary8p1uf}`,
  and `{} ≠ F_X ⊆ {binary32, binary16, BFloat16}`.

**Accept when** D.2's declaration parses and its `κ` recomputes to 3 (Step 12),
and a declaration set matching §4.5's list for `F_X = {binary32}` satisfies
`conforms`.

## 14. Review against the matrix, and the deviations log

**Do.**

- Every matrix row has `status ∈ {modelled, tested, comment-only(should),
  excluded}` with a reason for anything but `modelled`.
- `deviations.md` lists, at minimum: K = 2 exclusion; the `ωEncode` partiality
  choice; the enclosure view's non-normative status; the `S = ±∞, X_i = ±∞`
  block case; the perfect-square `Sqrt` addition if made; any NOTE that failed
  in Step 12 and how it was resolved.
- A reader with the draft open must be able to go from any Behavior line to
  its equation by §ref, and from any equation back.

**Done when** the matrix has no empty `equation-id` for a `modelled` row and
no empty `test-id` for a `tested` row, and the Step 6–13 acceptance checks all
pass in one `maude` run of `TESTS`.

---

## Review record

The plan above is the revised version. The first draft was reviewed for
clarity, directness, accuracy, and logical consistency; these are the
changes it produced, kept here so the reasoning is auditable.

**Accuracy.**

- The draft plan said ordered pattern lists "translate to equations with
  `owise`". That is wrong: `owise` marks one final default and does nothing
  for intermediate priority. Replaced by the sort-disjointness scheme plus
  explicit exclusion conditions, with CRC as the check (Step 7).
- The draft plan placed `Sqrt` in the exact module. `√` of a dyadic is
  irrational except at perfect squares. Moved to `OMEGA-REAL`, with the
  perfect-square case as an optional exact rule (Step 8).
- The draft plan said external formats could "reuse `ωDecode` with different
  parameters". They cannot: IEEE layout has a sign bit, reserved all-ones
  exponent, `−0`, and NaN payloads, none of which §4.7.2's layout has.
  Separate decoder (Step 6).
- The draft plan promised executability for "all ω-operations". Not true of
  the irrational ones, and pretending otherwise would violate the exactness
  rule. Split into Steps 7 and 8 with the enclosure view explicitly
  non-normative.
- The draft plan checked bijectivity as "decode then encode and encode then
  decode over all datums". Enumerating datums requires the encoding already;
  over finite sets of equal size, `encode ∘ decode = id` over all code points
  suffices (Step 6).

**Logical consistency.**

- Rule 1 (annexes never sources) conflicted with a draft step that used
  Annex C's `MinNormalOf = NaN` as a rule. Resolved by excluding K = 2, which
  §3.1 requires anyway (Step 4).
- Rule 4 (log, never resolve silently) conflicted with a draft step that
  quietly chose `ωEncode` to truncate non-integer significands. Resolved by
  making `ωEncode` partial and logging the choice (Step 6).
- The D.1 example was listed as a test in the draft plan while Step 8 admitted
  `Exp` is not exactly computable. Moved to "not checked, and why" (Step 12).
- Transitivity of `TotalOrder` was to be "exhaustive for F8", i.e. 16.7M
  triples per format. Now exhaustive to K ≤ 6, sampled at K = 8, and said so
  (Step 9).

**Directness.**

- Removed a proposed "phase 0: survey Maude tooling" — the tools used are
  named where they are used (Steps 7, 11).
- Removed a proposed intermediate DSL between the draft and Maude. The
  matrix already gives traceability; a DSL would be a second thing to verify.
- Collapsed the elementwise block operations from "one module per arity" to
  one parameterized schema, which is also what §5.7 does.

**Clarity.**

- The governing rules were scattered through steps as "note that…"; gathered
  into §0 and referenced by number.
- Every step now has an explicit **Accept when** so the plan can be executed
  without re-deriving what "done" means.
- The stochastic `R` modelling was stated three different ways; now once, in
  Step 5, with the block form as a distinct constructor and the reason.

**Open, deliberately.** Whether to ship the perfect-square `Sqrt` rule, and
the enclosure width for the test view, are left as implementer choices with
the requirement that both be logged.
