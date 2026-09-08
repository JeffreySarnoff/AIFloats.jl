# A denotational core and a finite evidence layer for IEEE_D1.md

> **Status: informative design record. The Lean below has NOT been compiled or
> machine-checked** — no Lean toolchain was available when this was written, and
> `Mathlib` lemma and definition names are written from memory rather than
> resolved against a pinned version. Read it as a specification of *shape*: the
> types, the clause ordering, the totality and computability boundaries, and the
> proof obligations are the content. Expect to fix names on first `lake build`.
>
> This document describes nothing that AIFloats.jl currently implements. It is a
> recommendation about how the source standard should be represented, kept
> beside `p3109-delta.md` as a design record.

## 0. Premise and scope

`IEEE_D1.md` is treated here as **the complete formal specification**. No
upstream formal artifact is assumed to exist, and nothing outside the document
is used as evidence. §4.1 NOTE 4 does state that "Auxiliary operations are
automatically extracted from a formal specification [12]", but under this
premise that upstream is unavailable, so the arrow runs the other way: the
document is the source, and everything below is a **transcription** of it whose
fidelity is the whole of the risk.

Clause numbers throughout refer to [IEEE_D1.md](IEEE_D1.md).

## 1. What the document is, representationally

The document already defines a small purpose-built specification language and
writes its semantics in it:

| Clause | Supplies |
|:--|:--|
| §2.3 | the mathematical notation — `÷`, `mod`, `#S`, `sgn`, `IsOdd`/`IsEven`, `x_{i..j}` |
| §4.3.1 | a uniform record per operation: Signature / Parameters / Operands / Result / Behavior / Details |
| §4.3.2 | the clause form, and the disambiguation rule: *"the first matching pattern in the order presented in this document defines the behavior"* |
| §4.1 | operations as parameterized mappings; specializations as parameter values; auxiliary `ω` operations on the closed extended reals |
| §3.1 | formats as four parameters under refinement constraints, with every other quantity derived from them |

So the representation should **implement this language**, not translate it into a
foreign one. Two facts from §4.1 fix the architecture:

- **Two sorts.** NOTE 2: "Operations on floating-point values are defined via
  conversion to the closed extended reals, on which the mathematical operation
  is performed, before projection into the floating-point datum set via rounding
  and saturation." Every operation factors as `ωProject ∘ ωOp ∘ ωDecode`.
- **Operations are mappings**, i.e. total functions, not relations. That rules
  out a general term-rewriting system, which would reopen confluence and
  termination — questions §4.3.2 closes by clause ordering.

## 2. What "best practice" means here

The core below is written to seven criteria, each traceable to a clause. These
are the standard the artifact should be judged against.

| # | Criterion | Source |
|:--|:--|:--|
| C1 | **Total.** Every operation is defined on every input of its sort. | §4.1 "mapping from a tuple of operands to one or more results" |
| C2 | **Clause-ordered.** Clauses appear in source order, in source count, with first-match-wins. | §4.3.2 |
| C3 | **Two-sorted.** Code points and ℝ^ω are distinct types; `ωDecode`/`ωProject` are the only bridges. | §4.1 NOTE 2, §3.1 |
| C4 | **Parameter-indexed.** A format is a value on which types depend; D_f, B, canonical form are functions of (K, P, Σ, Δ). | §3.1, §4.14 |
| C5 | **Honestly non-effective.** Where the specification is stated over ℝ, the transcription must be `noncomputable` rather than silently approximated. | §4.7.4, §4.10.8, §4.10.9 |
| C6 | **Clause-provenanced.** Every definition carries the clause it transcribes. | §4.6 declarations cite specializations; a standard is cited by clause |
| C7 | **Round-trippable.** The representation must re-render §4.7.4 and §4.7.5 in the document's own notation, and the diff against the source must equal a **reviewed baseline** — not the empty diff. See the note below. | there is no upstream to recover lost information from |

C7 is the acceptance test. With no upstream, a transcription that cannot be
re-rendered has destroyed information irrecoverably.

The baseline is not a weakening. Gap 3 below shows the source is **already
corrupt at the sites C7 targets**: §4.7.5's own signature renders as
`ωSaturate_{*M*}^{lo}_{*,M*}^{hi}(…)`, a flattened `ωSaturate_{M^lo, M^hi}`.
A faithful model renders the *correct* signature and therefore can never
diff-match the text. Demanding an empty diff would force the model to reproduce
the corruption. So every intentional divergence is a reviewed entry carrying a
reason, the build fails on any divergence not in the baseline, and the baseline
doubles as the transliteration-defect report.

## 3. Section A — the denotational core

### 3.1 Design decisions, and why

**ℝ^ω is a bespoke inductive, not `EReal`.** §3.1 defines
`ℝ^ω := ℝ ∪ {−∞, +∞, NaN}` and NOTE 1 pins two properties: "This set contains a
single NaN value" and "There is no negative zero in this set". Mathlib's `EReal`
has the two infinities but no NaN, and `Float` has NaN payloads and a signed
zero. Neither models the document. A four-constructor inductive does, and makes
the single-NaN property hold by construction rather than by convention.

**A format is a structure carrying its constraints.** §3.1 requires `K > 2`;
`0 < P < K` for signed and `0 < P ≤ K` for unsigned. Carrying those as fields
means an ill-formed format cannot be built, so no downstream definition needs a
validity guard, and the derived quantities of §4.14 are total functions of the
structure.

**Clause order is `match` order.** Lean's `match` is first-match-wins, which is
exactly §4.3.2's rule. Every `ω` definition below keeps the document's clause
sequence and clause count, so a reviewer can read the two side by side. The
final wildcard clause of each list makes the match exhaustive, satisfying C1.

**Guards, in-pattern disjunction and `where` blocks are marked.** §4.3.2 defines
four constructs — exact pattern, set inclusion, wildcard, explicit parameters in
a result expression — and defines none of these three, yet all three are used
(see §5, Gap 1). Each site is marked `-- ⚠ UNDEFINED IN §4.3.2` so the
transcription's assumptions are visible rather than absorbed.

**`noncomputable` is load-bearing.** See §3.3.

### 3.2 The artifact

#### A.1 — the closed extended reals (§3.1)

```lean
import Mathlib

namespace P3109

/-- §3.1: `ℝ^ω := ℝ ∪ {−∞, +∞, NaN}`.
    NOTE 1 — a single NaN; no negative zero. Both hold by construction. -/
inductive Rω where
  | nan
  | negInf
  | posInf
  | real (x : ℝ)
  deriving Inhabited

namespace Rω

/-- §2.3: `sgn(X)` is −1 for X < 0, 0 for X = 0, +1 for X > 0. -/
noncomputable def sgn : Rω → ℝ
  | .nan      => 0          -- ⚠ §2.3 defines sgn only on reals; NaN never reaches it
  | .negInf   => -1
  | .posInf   => 1
  | .real x   => if x < 0 then -1 else if x = 0 then 0 else 1

def abs : Rω → Rω
  | .nan     => .nan
  | .negInf  => .posInf
  | .posInf  => .posInf
  | .real x  => .real |x|

end Rω
```

#### A.2 — formats and their derived quantities (§3.1, §3.2, §4.14)

```lean
/-- §3.1: signedness Σ ∈ {Signed, Unsigned}. -/
inductive Signedness | Signed | Unsigned
  deriving DecidableEq, Repr

/-- §3.1: domain Δ ∈ {Finite, Extended}. -/
inductive Domain | Finite | Extended
  deriving DecidableEq, Repr

/-- §3.1: the four format-defining parameters, carrying their constraints.
    "Bitwidth K, an integer greater than two"; "Precision P … strictly less
    than K (0 < P < K) for signed formats, and less than or equal to K
    (0 < P ≤ K) for unsigned formats". -/
structure Format where
  K : ℕ
  P : ℕ
  /-- §3.1's Σ. Spelled out: `Σ` is Sigma-type notation in Lean 4. -/
  sigma : Signedness
  /-- §3.1's Δ. -/
  delta : Domain
  hK : 2 < K
  hP : 0 < P
  hPK : (sigma = .Signed → P < K) ∧ (sigma = .Unsigned → P ≤ K)

namespace Format

/-- §4.14 -/
def bitwidthOf (f : Format) : ℕ := f.K
/-- §4.14 -/
def precisionOf (f : Format) : ℕ := f.P
/-- §4.14 -/
def signednessOf (f : Format) : Signedness := f.sigma
/-- §4.14 -/
def domainOf (f : Format) : Domain := f.delta

/-- §4.14: ExponentBitwidthOf — K − P signed, K − P + 1 unsigned. -/
def exponentBitwidthOf (f : Format) : ℕ :=
  match f.sigma with
  | .Signed   => f.K - f.P
  | .Unsigned => f.K - f.P + 1

/-- §4.14: TrailingSignificandBitwidthOf = P − 1. §3.1 calls S mod 2^{P−1}
    the trailing significand. -/
def trailingSignificandBitwidthOf (f : Format) : ℕ := f.P - 1

/-- §3.1 and §4.14: B = 2^{K−P−1} signed, 2^{K−P} unsigned. -/
def exponentBiasOf (f : Format) : ℕ :=
  match f.sigma with
  | .Signed   => 2 ^ (f.K - f.P - 1)
  | .Unsigned => 2 ^ (f.K - f.P)

/-- §3.2: `Binary⟨K⟩p⟨P⟩⟨s|u⟩⟨f|e⟩`. A total function of the parameters, so
    Annex B/C naming is generated, never stored. -/
def name (f : Format) : String :=
  s!"Binary{f.K}p{f.P}" ++
    (match f.sigma with | .Signed => "s" | .Unsigned => "u") ++
    (match f.delta with | .Extended => "e" | .Finite => "f")

end Format

/-- §3.1: "The encoding is a unique bijective mapping from D_f to integer code
    points 0 … 2^K − 1". The code-point side of that bijection. -/
abbrev CodePoint (f : Format) := Fin (2 ^ f.K)
```

#### A.3 — projection specifications (§4.2, §4.7.4 Details)

```lean
/-- §4.2 and §4.7.4. The stochastic variants carry N and R because §4.7.4's
    RoundAway clauses are stated in terms of both.
    ⚠ §4.7.4 **Details** constrains `0 ≤ R < 2^N` in prose, not in a behavior
    clause; §4.3.2 provides no form for a parameter side condition. Carried
    here as `hR` so the constraint is not lost. -/
inductive RoundingMode where
  | NearestTiesToEven
  | NearestTiesToAway
  | TowardPositive
  | TowardNegative
  | TowardZero
  | ToOdd
  | StochasticA (N R : ℕ) (hR : R < 2 ^ N)
  | StochasticB (N R : ℕ) (hR : R < 2 ^ N)
  | StochasticC (N R : ℕ) (hR : R < 2 ^ N)

/-- §4.2 -/
inductive SaturationMode | SatFinite | SatPropagate | SatNone
  deriving DecidableEq, Repr

/-- §4.2: "A projection specification is a pair (rounding mode, saturation
    mode)." §4.15 names the accessors RoundOf and SatOf. -/
structure Projection where
  roundOf : RoundingMode
  satOf   : SaturationMode
```

#### A.4 — ωDecode (§4.7.2)

```lean
/-- §4.7.2. Clause order is the document's and is load-bearing: the −∞ clause
    for `2^K − 1` must precede the negation clause for `2^{K−1} < x < 2^K`,
    or every negative code point would decode through the wrong branch. -/
noncomputable def ωDecodeAux (f : Format) : ℕ → Rω
  | x =>
    let K := f.K
    let P := f.P
    let B := (f.exponentBiasOf : ℝ)
    -- ωDecodeAux(Signed,   ∗,        2^{K−1}) → NaN
    if f.sigma = .Signed   ∧ x = 2 ^ (K - 1)     then .nan else
    -- ωDecodeAux(Unsigned, ∗,        2^K − 1) → NaN
    if f.sigma = .Unsigned ∧ x = 2 ^ K - 1       then .nan else
    -- ωDecodeAux(Signed,   Extended, 2^{K−1} − 1) → +∞
    if f.sigma = .Signed   ∧ f.delta = .Extended ∧ x = 2 ^ (K - 1) - 1 then .posInf else
    -- ωDecodeAux(Signed,   Extended, 2^K − 1)     → −∞
    if f.sigma = .Signed   ∧ f.delta = .Extended ∧ x = 2 ^ K - 1       then .negInf else
    -- ωDecodeAux(Unsigned, Extended, 2^K − 2)     → +∞
    if f.sigma = .Unsigned ∧ f.delta = .Extended ∧ x = 2 ^ K - 2       then .posInf else
    -- ωDecodeAux(Signed, Δ, 2^{K−1} < x < 2^K) → −ωDecodeAux(Signed, Δ, x − 2^{K−1})
    if f.sigma = .Signed ∧ 2 ^ (K - 1) < x ∧ x < 2 ^ K then
      match ωDecodeAux f (x - 2 ^ (K - 1)) with
      | .real y => .real (-y)
      | .posInf => .negInf
      | .negInf => .posInf
      | .nan    => .nan
    else
      -- ωDecodeAux(∗, ∗, x) → X   where T = x mod 2^{P−1},  E_biased = x ÷ 2^{P−1}
      let T        : ℝ := ((x % 2 ^ (P - 1) : ℕ) : ℝ)
      let Ebiased  : ℕ := x / 2 ^ (P - 1)
      if Ebiased = 0 then
        .real ((0 + T * (2:ℝ) ^ (1 - (P:ℤ))) * (2:ℝ) ^ (1 - (B:ℤ)))   -- subnormal and zero
      else
        .real ((1 + T * (2:ℝ) ^ (1 - (P:ℤ))) * (2:ℝ) ^ ((Ebiased:ℤ) - (B:ℤ)))  -- normal
  -- ⚠ TERMINATION OBLIGATION: the negation clause recurses on x − 2^{K−1},
  -- which is < x whenever 2^{K−1} < x. Discharge with `decreasing_by omega`
  -- once the guard is in scope; left unstated rather than guessed.

/-- §4.7.2, first clause: external formats route to ωDecodeExternal (§4.8).
    ⚠ §4.8's terminal clauses are English — "The extended real value encoded
    by x" — deferring to IEEE 754. See §5, Gap 4. Modelled as an opaque
    parameter so the boundary is explicit rather than silently supplied. -/
noncomputable def ωDecode (f : Format) (x : CodePoint f) : Rω :=
  ωDecodeAux f x.val
```

#### A.5 — ωRoundToPrecision (§4.7.4)

This is the clause where the whole computability question lives.

```lean
/-- §4.7.4 auxiliary: RNITE(X) — round to nearest integer, ties to even. -/
noncomputable def RNITE (X : ℝ) : ℤ :=
  if X < ⌊X⌋ + 1/2 then ⌊X⌋
  else if X = ⌊X⌋ + 1/2 ∧ Even ⌊X⌋ then ⌊X⌋
  else ⌊X⌋ + 1

/-- §4.7.4: the RoundAway table, verbatim in the document's clause order.
    `ν = S̃ − ⌊S̃⌋`; `CodeIsEven` as defined in the same `where` block. -/
noncomputable def roundAway (μ : RoundingMode) (ν X : ℝ) (codeIsEven : Prop)
    [Decidable codeIsEven] : Prop :=
  match μ with
  | .TowardZero            => False
  | .TowardPositive        => ν > 0 ∧ X > 0
  | .TowardNegative        => ν > 0 ∧ X < 0
  | .NearestTiesToAway     => ν ≥ 1/2
  | .NearestTiesToEven     => ν > 1/2 ∨ (ν = 1/2 ∧ ¬ codeIsEven)
  | .ToOdd                 => ν > 0 ∧ codeIsEven
  | .StochasticA N R _     => ⌊ν * 2 ^ N⌋ + (R:ℤ) ≥ 2 ^ N
  | .StochasticB N R _     => ⌊ν * 2 ^ (N+1)⌋ + (2 * (R:ℤ) + 1) ≥ 2 ^ (N+1)
  | .StochasticC N R _     => RNITE (ν * 2 ^ N) + (R:ℤ) ≥ 2 ^ N

/-- §4.7.4: ωRoundToPrecision_{P,B,μ}(X) → Z.

    First clause: `ωRoundToPrecision(X ∈ {0, −∞, +∞, NaN}) → X`.
    Second clause: the `where` block —
      Q  = max(⌊log₂|X|⌋, 1 − B) − P + 1
      S̃  = |X| × 2^{−Q}                (real-valued significand)
      S  = ⌊S̃⌋ + 1 if RoundAway(μ) else ⌊S̃⌋
      Z  = sgn(X) × S × 2^Q
    and
      CodeIsEven = IsEven(⌊S̃⌋)                        if P > 1
                 = (⌊S̃⌋ = 0) or IsEven(Q + B)         if P = 1

    ⚠ `where` blocks with local bindings are used throughout §4.7 and are not
    among the four constructs §4.3.2 defines. See §5, Gap 1.

    NONCOMPUTABLE, and that is the point. `Real.logb`, `Int.floor` on ℝ, and
    the comparisons `ν > 1/2` / `ν = 1/2` are not decidable for a general
    real. See §3.3 and §5, Gap 2. -/
noncomputable def ωRoundToPrecision (P B : ℕ) (μ : RoundingMode) : Rω → Rω
  | .nan             => .nan
  | .negInf          => .negInf
  | .posInf          => .posInf
  | .real X =>
    if X = 0 then .real 0 else
      let Q  : ℤ := max ⌊Real.logb 2 |X|⌋ (1 - (B:ℤ)) - (P:ℤ) + 1
      let S̃  : ℝ := |X| * (2:ℝ) ^ (-Q)
      let codeIsEven : Prop :=
        if P > 1 then Even ⌊S̃⌋ else (⌊S̃⌋ = 0 ∨ Even (Q + (B:ℤ)))
      let ν  : ℝ := S̃ - ⌊S̃⌋
      let S  : ℤ := if roundAway μ ν X codeIsEven then ⌊S̃⌋ + 1 else ⌊S̃⌋
      .real (Rω.sgn (.real X) * (S:ℝ) * (2:ℝ) ^ Q)
```

#### A.6 — ωSaturate, ωEncode, ωProject (§4.7.5, §4.7.6, §4.7.3)

```lean
/-- §4.7.5. Eighteen clauses, in the document's order.
    ⚠ Two constructs here are outside §4.3.2: guards (`if X < M^lo and X ≠ −∞`)
    and disjunction in a pattern position (`TowardZero or TowardNegative`).
    Both are transcribed as side conditions. See §5, Gap 1.
    NOTE (§4.7.5) — "Saturation does not round any value"; the rounding mode is
    supplied only to resolve the SatNone direction cases. -/
noncomputable def ωSaturate (Mlo Mhi : ℝ) (sat : SaturationMode)
    (μ : RoundingMode) (X : Rω) (Σ : Signedness) (Δ : Domain) : Rω :=
  match X with
  | .nan => .nan
  | _ =>
    let inRange : Prop :=
      match X with | .real x => Mlo ≤ x ∧ x ≤ Mhi | _ => False
    if h : inRange then X else
    match sat with
    | .SatFinite =>
        match X with
        | .posInf => .real Mhi
        | .negInf => .real Mlo
        | .real x => if x < Mlo then .real Mlo else .real Mhi
        | .nan    => .nan
    | .SatPropagate =>
        match X, Δ with
        | .posInf, .Extended => .posInf
        | .posInf, _         => .real Mhi
        | .negInf, .Extended => if Σ = .Signed then .negInf else .real Mlo
        | .negInf, _         => .real Mlo
        | .real x, _         => if x < Mlo then .real Mlo else .real Mhi
        | .nan,    _         => .nan
    | .SatNone =>
        -- The two rounding-direction clauses precede the infinity clauses:
        --   (SatNone, TowardZero or TowardNegative, X) if X > M^hi and X ≠ +∞ → M^hi
        --   (SatNone, TowardZero or TowardPositive, X) if X < M^lo and X ≠ −∞ → M^lo
        -- The `X ≠ ±∞` conjuncts are discharged by the `.real x` pattern, which
        -- already excludes both infinities.
        let clampsHigh := μ matches .TowardZero | .TowardNegative
        let clampsLow  := μ matches .TowardZero | .TowardPositive
        match X with
        | .real x =>
            if clampsHigh ∧ x > Mhi then .real Mhi
            else if clampsLow ∧ x < Mlo then .real Mlo
            else if Δ = .Finite then .nan
            else if x < Mlo then (if Σ = .Signed then .negInf else .nan)
            else if x > Mhi then .posInf
            else .real x
        | .posInf => if Δ = .Extended then .posInf else .nan
        | .negInf =>
            match Δ, Σ with
            | .Extended, .Signed   => .negInf
            | .Extended, .Unsigned => .nan
            | .Finite,   _         => .nan
        | .nan    => .nan

/-- §4.7.6. Precondition (NOTE): applied only to a value in the datum set of f. -/
noncomputable def ωEncode (f : Format) : Rω → ℕ
  | .nan    => match f.sigma with
               | .Signed   => 2 ^ (f.K - 1)
               | .Unsigned => 2 ^ f.K - 1
  | .posInf => match f.sigma with
               | .Signed   => 2 ^ (f.K - 1) - 1
               | .Unsigned => 2 ^ f.K - 2
  | .negInf => 2 ^ f.K - 1        -- via the X < 0 clause applied to +∞
  | .real X =>
    if X < 0 then ωEncode f (.real (-X)) + 2 ^ (f.K - 1)
    else if X = 0 then 0
    else
      let B := (f.exponentBiasOf : ℤ)
      let E : ℤ := max ⌊Real.logb 2 X⌋ (1 - B)
      let S : ℤ := ⌊X * (2:ℝ) ^ (-E) * (2:ℝ) ^ ((f.P : ℤ) - 1)⌋
      let T : ℤ := S % 2 ^ (f.P - 1)
      if S < 2 ^ (f.P - 1) then T.toNat
      else (T + (E + B) * 2 ^ (f.P - 1)).toNat

/-- §4.7.3: ωProject_{f,ρ}(X) → x. The single write path. -/
noncomputable def ωProject (f : Format) (ρ : Projection) : Rω → ℕ
  | .nan => ωEncode f .nan
  | X =>
    -- §4.7.3's `and` block: M^lo = ωDecode_f(MinFiniteOf(f)),
    -- M^hi = ωDecode_f(MaxFiniteOf(f)). §4.14 describes MinFiniteOf and
    -- MaxFiniteOf in prose ("Maximum finite value representable in format f")
    -- and gives no defining clause, so both are stated as obligations rather
    -- than invented here. See §8 item 2.
    let Mlo : ℝ := sorry
    let Mhi : ℝ := sorry
    let R := ωRoundToPrecision f.P f.exponentBiasOf ρ.roundOf X
    let S := ωSaturate Mlo Mhi ρ.satOf ρ.roundOf R f.sigma f.delta
    ωEncode f S
```

#### A.7 — three operation shapes (§4.10.3, §4.11.1, §4.10.8/§4.10.9)

Every operation in §4.10–§4.16 has the same schema. Three suffice to fix it;
the remainder is transcription, not design.

```lean
/-- §4.10.3, exact arithmetic. Ten clauses, in order. -/
noncomputable def ωAdd : Rω → Rω → Rω
  | .nan,    _       => .nan
  | _,       .nan    => .nan
  | .posInf, .negInf => .nan
  | .negInf, .posInf => .nan
  | .posInf, _       => .posInf
  | _,       .posInf => .posInf
  | .negInf, _       => .negInf
  | _,       .negInf => .negInf
  | .real X, .real Y => .real (X + Y)

/-- §4.10.3: Add(x, y) → ωProject_{fr,ρ}(ωAdd(ωDecode_{fx}(x), ωDecode_{fy}(y))).
    The two-sort factoring of §4.1 NOTE 2, made structural: there is no datum
    between the decode and the project, so the specification cannot be
    decomposed into two roundings. -/
noncomputable def Add (fx fy fr : Format) (ρ : Projection)
    (x : CodePoint fx) (y : CodePoint fy) : ℕ :=
  ωProject fr ρ (ωAdd (ωDecode fx x) (ωDecode fy y))

/-- §4.11.1, exact selection. Eleven clauses; the last is a conditional
    expression, `if X < Y then X else Y`, which §4.3.2 also does not define
    as a result form. -/
noncomputable def ωMinimum : Rω → Rω → Rω
  | .nan,    _       => .nan
  | _,       .nan    => .nan
  | .posInf, .posInf => .posInf
  | .negInf, .negInf => .negInf
  | .posInf, .negInf => .negInf
  | .negInf, .posInf => .negInf
  | .posInf, Y       => Y
  | X,       .posInf => X
  | .negInf, _       => .negInf
  | _,       .negInf => .negInf
  | .real X, .real Y => if X < Y then .real X else .real Y

/-- §4.10.8, algebraic but irrational-valued. `ωSqrt(X) if X < 0 → NaN` is a
    guard — again outside §4.3.2. -/
noncomputable def ωSqrt : Rω → Rω
  | .nan    => .nan
  | .negInf => .nan
  | .posInf => .posInf
  | .real X => if X < 0 then .nan else .real (Real.sqrt X)

/-- §4.10.9, transcendental. The terminal clause is `ωExp(X) → e^X`. -/
noncomputable def ωExp : Rω → Rω
  | .nan    => .nan
  | .posInf => .posInf
  | .negInf => .real 0
  | .real X => .real (Real.exp X)
```

### 3.3 What the core cannot do, and on which arguments

Every definition above is `noncomputable`. That is the encoding **reporting a
property of the specification**, but the property is narrower than the marker
suggests, and stating it loosely leads directly to a design error (§4.3).

The marker is a whole-definition attribute in Lean. Effectivity is not. It is a
property of a definition **applied to a domain**:

- §4.10.8 and §4.10.9 terminate in `√X`, `1/√X`, `e^X`, `2^X`, `ln X`. For
  `e^X` and `ln X` the result is transcendental and no exact comparison against
  it is decidable.
- §4.7.4 then decides by **exact real comparison** — `ν > 1/2`, `ν = 1/2`,
  `⌊ν × 2^N⌋` — on a `ν` derived from whatever value it was handed.
- §4.7.4 and §4.7.6 need `⌊log₂|X|⌋`.

But `⌊log₂|X|⌋` is **exact whenever `X` is dyadic**: for `X = m · 2^e` with `m`
a nonzero integer, it is `(bitlength|m| − 1) + e`, ordinary integer work. And
§4.7.2 decodes every datum to a dyadic rational. So the pipeline splits:

| Applied to | §4.7.4 / §4.7.6 | Which operations reach it that way |
|:--|:--|:--|
| a dyadic rational | **exact**; every comparison in the RoundAway table decides | `ωAdd`, `ωSubtract`, `ωMultiply`, `ωFMA`, `ωFAA`, `ωNegate`, `ωAbs`, `ωCopySign`, the whole extremum family, `ωConvert` |
| a real algebraic value | decidable in the algebraic fragment | `ωSqrt`, `ωRecip`, `ωRSqrt`, `ωHypot` |
| a transcendental value | **not decidable** | `ωExp`, `ωExp2`, `ωLog`, `ωLog2`, `ωLogOnePlus`, `ωExpMinusOne`, and the families of §4.10.10–§4.10.16 |

So the honest claim is *not* "the specification computes nothing". It is:

> The specification is **effective on the dyadic fragment**, which is where the
> exact-arithmetic operations live, and non-effective exactly where an
> operation's ω-result leaves that fragment.

Lean marks all of it `noncomputable` because the definitions are stated over ℝ
and the marker cannot be domain-relative. That is a limitation of the marker,
not a claim about the standard, and the distinction matters: a second layer is
required **only for the third row**, not universally. Anything that computed the
third row anyway would have silently inserted a working precision the document
never authorises.

That is what Section B supplies, and the reason it is scoped rather than
total.

## 4. Section B — the finite evidence layer, with an explicit enclosure obligation

### 4.1 Why a second layer is forced

§4.6 requires:

> Where an operation specialization is supplied, the implementation **shall
> compute the same result as does the defined operation specialization for all
> possible operand values.** This should be attested by any appropriate proof
> method, including direct computation.

Set beside §3.3, this is a demand to compute something the specification defines
non-effectively. The document supplies no bridge: no working precision, no
separation bound, no enclosure discipline. This is the Table-Maker's Dilemma,
and §4.6 is unsatisfiable as literally written without the missing artifact.

Two facts rescue it, and both come from the document:

1. **Every operand domain is finite.** §3.1 fixes the code points of a K-bit
   format at `0 … 2^K − 1`, and §4.5 fixes the required formats at
   `F₈ = {Binary8p4se, Binary8p3se}`, `F₄ = {Binary4p2sf}`. A specialization is
   therefore a finite function, and "for all possible operand values" is a
   finite conjunction.
2. **ωProject restricted to the rationals is computable**, even though
   `ωProject` on ℝ is not. For rational `q`, `⌊log₂|q|⌋` is computable, `S̃` and
   `ν` are rational, and every comparison in §4.7.4 is decidable. This is the
   hinge the whole layer turns on.

So: enclose the exact ω-result in a rational interval, and if both endpoints
project to the same code point, that code point *is* the specified answer.

### 4.2 The artifact

#### B.1 — specializations as finite objects (§4.1, §4.3.1)

```lean
/-- §4.1: "An operation specialization supplies values for the parameters of an
    operation." For the binary arithmetic schema of §4.3.1 those parameters are
    (f_x, f_y, f_r, ρ). -/
structure BinarySpec where
  fx : Format
  fy : Format
  fr : Format
  ρ  : Projection

/-- The denotation of a specialization: total, noncomputable, and the thing
    §4.6 measures an implementation against. -/
noncomputable def BinarySpec.denote (s : BinarySpec)
    (ωop : Rω → Rω → Rω) (x : CodePoint s.fx) (y : CodePoint s.fy) : ℕ :=
  ωProject s.fr s.ρ (ωop (ωDecode s.fx x) (ωDecode s.fy y))

/-- What an implementation actually ships: a finite function. -/
abbrev BinaryTable (s : BinarySpec) :=
  CodePoint s.fx → CodePoint s.fy → CodePoint s.fr

/-- §4.6, verbatim: "shall compute the same result as does the defined
    operation specialization for all possible operand values."
    Note this is a Prop, not a Bool: it is NOT decidable as it stands,
    because `denote` is noncomputable. B.3 is what makes it decidable. -/
def Conforms (s : BinarySpec) (ωop : Rω → Rω → Rω) (t : BinaryTable s) : Prop :=
  ∀ x y, (t x y).val = s.denote ωop x y
```

#### B.2 — rational intervals and the enclosure predicate

```lean
/-- A rational enclosure. Rational, not real: the endpoints must be objects a
    machine can project, per §4.1's hinge. -/
structure Enclosure where
  lo : ℚ
  hi : ℚ
  le : lo ≤ hi

/-- The interval contains the exact value. Non-finite ω-results are excluded:
    they take the exact clauses of §4.7.5 and need no enclosure. -/
def Enclosure.contains (I : Enclosure) : Rω → Prop
  | .real X => (I.lo : ℝ) ≤ X ∧ X ≤ (I.hi : ℝ)
  | _       => False

/-- ωProject on a rational is computable — the property §4.1's hinge relies on.
    Stated as an obligation rather than proved here. -/
axiom ωProjectQ (f : Format) (ρ : Projection) (q : ℚ) : ℕ

axiom ωProjectQ_agrees (f : Format) (ρ : Projection) (q : ℚ) :
  ωProjectQ f ρ q = ωProject f ρ (.real (q : ℝ))
```

#### B.3 — the enclosure obligation

This is the artifact the document lacks. It has three parts: a **separation**
predicate, a **soundness** theorem, and a **certificate**.

A certificate is **generated, never authored**. An enclosure-narrowing loop
produces it from the operation's own definition, and it is then checked against
the core. It is build output that happens to be normative evidence, so there is
no hand-written artifact here that could drift from the specification it
attests.

```lean
/-- SEPARATION. An enclosure separates when every real inside it projects to
    the same code point. Decidable by two rational projections and an equality,
    given monotonicity of ωProject on an interval containing no rounding
    boundary. -/
def Separates (f : Format) (ρ : Projection) (I : Enclosure) (r : ℕ) : Prop :=
  ∀ X : ℝ, (I.lo : ℝ) ≤ X → X ≤ (I.hi : ℝ) → ωProject f ρ (.real X) = r

/-- The decidable witness for `Separates`: both endpoints project alike.
    Sound only together with `ωProject`'s monotonicity on boundary-free
    intervals, which is the proof obligation attached to this definition. -/
def separatesCheck (f : Format) (ρ : Projection) (I : Enclosure) : Bool :=
  ωProjectQ f ρ I.lo == ωProjectQ f ρ I.hi

/-- SOUNDNESS. Enclosure plus separation determines the specified result.
    This is the bridge between Section A and Section B, and the sentence the
    document is missing. -/
theorem enclosure_sound
    {f : Format} {ρ : Projection} {I : Enclosure} {X : Rω} {r : ℕ}
    (hEnc : I.contains X) (hSep : Separates f ρ I r) :
    ωProject f ρ X = r := by
  cases X with
  | real x => exact hSep x hEnc.1 hEnc.2
  | _      => cases hEnc

/-- CERTIFICATE. What discharges §4.6 for one specialization: the finite
    table, and for every operand pair an enclosure of the exact ω-result that
    separates onto the tabled entry. Produced by the narrowing loop of B.4 and
    checked here; not written by hand. -/
structure Certificate (s : BinarySpec) (ωop : Rω → Rω → Rω) where
  table : BinaryTable s
  encl  : ∀ x y, Enclosure
  sound : ∀ x y, (encl x y).contains (ωop (ωDecode s.fx x) (ωDecode s.fy y))
  sep   : ∀ x y, Separates s.fr s.ρ (encl x y) (table x y).val

/-- A certificate discharges §4.6. -/
theorem Certificate.conforms {s : BinarySpec} {ωop : Rω → Rω → Rω}
    (c : Certificate s ωop) : Conforms s ωop c.table := by
  intro x y
  exact (enclosure_sound (c.sound x y) (c.sep x y)).symm
```

#### B.4 — where the obligation is partial, and why

`separatesCheck` can fail. It fails exactly when the exact ω-result lies **on** a
rounding boundary of the result format — a tie under `NearestTiesToEven`, or a
datum boundary under a directed mode. No interval of positive width separates
such a point, so narrowing does not help there.

Two claims must be kept apart, and keeping them apart is the whole content of
this subsection.

**Soundness is unconditional.** `enclosure_sound` and `Certificate.conforms`
carry no number-theoretic hypothesis. Any certificate that validates discharges
§4.6 for the operand tuple it covers — whatever the operation, whatever the
operand. Nothing below weakens that, and nothing below is needed for it.

**Termination of the search is the part that needs an argument.** Whether the
narrowing loop that *produces* a certificate always succeeds depends on whether
any operand's exact ω-result sits on a boundary:

| ω-result | Boundary hits | How the search behaves |
|:--|:--|:--|
| rational (`ωAdd`, `ωMultiply`, `ωFMA`, `ωFAA`) | occur, and are ordinary | decide exactly in ℚ; no narrowing needed |
| algebraic (`ωSqrt`, `ωRecip`, `ωRSqrt`) | occur — √4 = 2 is a datum | decide exactly in the algebraic fragment |
| transcendental (`ωExp`, `ωLog`, and the families of §4.10.10–§4.10.16) | provably do not occur | narrowing terminates |

For the transcendental families, the reason boundary hits do not occur is a
transcendence result: §4.7.2 decodes every datum to a dyadic rational, and for
nonzero rational `X` the value `e^X` is transcendental, hence never dyadic. The
boundary case is therefore vacuous and a sufficiently narrow enclosure always
separates.

That argument justifies *expecting* the loop to finish. It is not part of the
soundness proof and must not be presented as one. A builder who cannot supply it
still has a correct system, with a weaker completion guarantee. Hence:

> **Narrowing runs under an explicit budget. Budget exhaustion is reported as an
> unresolved obligation for that operand tuple — never as success, and never as
> a defect in the specification.** A tool that has failed to separate an
> enclosure has learned nothing about the standard and must not report as
> though it had.

Three outcomes, and exactly three: **certified**, **refuted** (the enclosure
separates onto a code point other than the one tabled), and **unresolved**.
Collapsing the third into either of the other two is the failure mode this
subsection exists to prevent.

The honest statement of the gap is therefore narrower than it first appears:
§4.6 is discharged by finite enumeration plus a per-tuple enclosure certificate,
and the document supplies neither. Transcendence enters only as the reason the
certificate search can be expected to terminate.

#### B.5 — κ, and the required-specialization set

```lean
/-- §4.4: κ over a specialization. The document's own conditions come first —
    "Where an approximate implementation does not match on NaNs … it shall
    declare κ = NaN"; "matches on NaNs but does not match on infinities …
    κ = ∞" — before the counting definition:
      κ = max_{x∈I} #(((â(x), ã(x)] ∪ [ã(x), â(x))) ∩ V). -/
inductive Kappa | nan | infinite | finite (k : ℕ)
  deriving Repr

/-- §4.4's MatchOnInfinity, transcribed from the braced definition. -/
def matchOnInfinity : Rω → Rω → Bool
  | .nan,    .nan    => true
  | .real _, .real _ => true
  | .posInf, .posInf => true
  | .negInf, .negInf => true
  | _,       _       => false

/-- §4.5. The required specializations are a computed finite set, so
    conformance is a set difference rather than a reading exercise.
      F₈ = {Binary8p4se, Binary8p3se}   F₄ = {Binary4p2sf}
      {} ≠ F_X ⊆ {binary32, binary16, BFloat16}
      ρ = (NearestTiesToEven, SatNone)
    ⚠ F_X is implementation-chosen ("the choice of subset for F_X is
    implementation-defined"), so this is a predicate on a declared F_X, not a
    closed set. -/
def requiredAdd (F4 F8 : Finset Format) (FX : Finset Format) :
    Finset (Format × Format × Format) :=
  ((F4 ∪ F8) ×ˢ (F4 ∪ F8) ×ˢ (F8 ∪ FX))
```

## 5. Gaps in the source that the transcription surfaces

Producing these is part of the value of the exercise. All four are findings
about `IEEE_D1.md` itself.

**Gap 1 — the language as used exceeds the language as defined.** §4.3.2 defines
four constructs: exact pattern (§4.3.2.1), set inclusion (§4.3.2.2), wildcard
(§4.3.2.3), explicit parameters in a result expression (§4.3.2.4). The
definitions also use, without defining:

| Construct | Site |
|:--|:--|
| guard | `ωSqrt(X) if X < 0 → NaN` (§4.10.8); `ωCopySign(±∞, Y) if Y ≥ 0` (§4.10.2) |
| conjunctive guard | `if X < M^lo and X ≠ −∞` (§4.7.5) |
| disjunction in a pattern position | `ωSaturate(SatNone, TowardZero or TowardNegative, …)` (§4.7.5) |
| `where` block with local bindings | `Q = max(⌊log₂|X|⌋, 1−B) − P + 1` (§4.7.4); §4.7.2; §4.7.6 |
| conditional result expression | `ωMinimum(X, Y) → if X < Y then X else Y` (§4.11.1) |
| prose side condition on a parameter | `0 ≤ R < 2^N` (§4.7.4 **Details**) |

Each is marked `⚠` at its site above. This table is the first thing that should
go back to the working group.

**Gap 2 — the semantics is exact ℝ with transcendentals, and no bridge to
computation is given.** §3.3 and §4.1 above. Section B is the missing bridge.

**Gap 3 — the artifact is already lossy.** §4.7.5's signature renders as
`ωSaturate_{M}^{lo}_{,M}^{hi}(…)`, a flattened `ωSaturate_{M^lo, M^hi}`. §4.4's
brace-stacked `MatchOnInfinity`, §4.5's braced `MinmaxOp` set, and Annex F's
two-column table are similarly degraded. Layout-significant mathematics has not
survived transport into plain text — which, under the premise of §0, means the
normative artifact is degrading with no upstream to restore it. This is the
strongest practical argument for a representation that does survive transport.

**Gap 4 — self-containment has one real exception.** §4.8 terminates in English:
"The extended real value encoded by x", "The code in f that decodes to X", for
`f ∈ {binary64, binary32, binary16, BFloat16}`. §4.7.2 routes every external
decode through it and §4.5 makes a nonempty `F_X` mandatory, so a required part
of conformance rests on a definition this document does not contain. A.4 models
it as an opaque parameter so the boundary is visible rather than silently filled
with an IEEE 754 model.

## 6. What stays prose, and what gets generated

| Material | Treatment |
|:--|:--|
| §1.2 *shall* / *should* / *may* / *can* | per-clause metadata, never code. `shall` clauses become proof obligations; `should` and `may` explicitly do not. Flattening this erases the line between conforming and conventional. |
| §2.1 definitions | doc comments on the formal definitions they name — *canonical form*, *trailing significand*, *normal*, *subnormal*, *code point* — not a parallel glossary that can disagree |
| §3.2 naming, Annex B/C value tables, Annex F groups | **generated** from Section A and kept as regression fixtures. Annex B says so itself: it is informative, and "the detailed specification of the encoding is presented in §4.7.6" |
| Annex A rationale, Annex D/E examples, Annex G bibliography | prose, attached to the clause each justifies. Rationale is not derivable; it is the argument *for* the specification |

## 7. Alternatives rejected, and why

| Form | Fails because |
|:--|:--|
| OWL / RDF / description logic | §2.3 needs `÷`, `mod`, `#S`, `sgn`; §4.7.2 needs `x mod 2^{P−1}`; §4.4 needs a max over a set and an interval cardinality — all outside DL. And §4.3.2's first-match-wins is non-monotonic, which DL cannot express at all |
| general term-rewriting system | more power than §4.3.2 needs, and it reopens confluence and termination, which clause ordering closes. §4.1 calls an operation a *mapping* — a function, not a relation |
| tables / relational data alone | §5.2's `reduce` is recursive, §4.10 nests `ωProject ∘ ωOp ∘ ωDecode`, and §4.3.2.4 lets a result expression reference another specialization. Tables hold neither recursion nor composition |
| prose plus clause numbers (the status quo) | §4.6 demands attestation over all operand values; prose cannot be attested. And Gap 3 shows this prose is degrading in transit |
| a general document AST | represents the artifact, not the content. Useful only for provenance |
| an executable model in a conventional language | would silently insert a working precision the document never authorises, and would make §3.3's boundary invisible |

## 8. Obligations on whoever builds this

1. Compile it. Nothing above has been checked; expect `Mathlib` name churn and a
   termination proof to discharge in `ωDecodeAux`. Note that the proofs and the
   *discipline* are separable: the clause-order fidelity of Section A and the
   three-outcome reporting of B.4 are enforceable while every theorem below is
   still an unproved goal. Do not defer the discipline until the proofs land.
2. Complete the transcription — §4.10.4 through §4.16, and all of §5 — following
   A.7's schema. That is transcription, not design.
3. Discharge or replace the two `axiom`s in B.2. `ωProjectQ` should be a genuine
   definition over ℚ and `ωProjectQ_agrees` a theorem; they are stated as
   axioms here only because the rational specialisation of §4.7.4 has not been
   written out.
4. Prove `ωProject` monotone on boundary-free intervals, which is what makes
   `separatesCheck` a sound witness for `Separates`.
5. Build the round-trip renderer and make **C7** a test: emit §4.7.4 and §4.7.5
   from the AST and diff against `IEEE_D1.md`, requiring the diff to equal the
   reviewed baseline of §2. Someone with the PDF in hand must review that
   baseline — it is the list of places the transliteration and the model
   disagree, and only the PDF says which of the two is right.
6. **Digest every quotation, not just the file.** Each definition above cites a
   clause, and several quote it. Clause numbers are stable across revisions;
   quoted bytes are not. Record a source span plus a digest of the quoted bytes
   for each citation, so a revised clause surfaces as a `stale-quotation`
   diagnostic naming the affected definition.

   This is not hypothetical. `IEEE_D1.md` was replaced while this document was
   being written — 660 lines changed, and the pin in `src/rules/conformance.jl`
   moved from `820cb500…` to `75f38b4c…`. Every citation here had to be
   re-verified by hand afterwards. A whole-file digest detects *that* something
   changed; only per-quotation digests say *what broke*.
7. Send Gap 1's table to the working group. Six undefined constructs in a
   normative clause list is a defect in the source, not in the reader.
