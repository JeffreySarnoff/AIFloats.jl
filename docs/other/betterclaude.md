# A better way: reconciling `denotational.md` and `usingdsl.md`

**Status:** design record. Not an IEEE document. Changes nothing about the
authority of `IEEE_D1.md` or the designated P3109 report.

Its two inputs sit beside it:
[`denotational.md`](denotational.md) and [`usingdsl.md`](usingdsl.md).

**Provenance.** These are not independent documents, and treating the "two
approaches" framing as pristine would misattribute several ideas.
`denotational.md` has been revised twice while this synthesis was written:

| Revision | Idea | Came from |
|:--|:--|:--|
| 1 | per-quotation digests (§8 item 6) | `usingdsl.md`'s provenance model |
| 1 | soundness/termination split, three outcomes (§B.4) | this synthesis's review |
| 1 | certificates generated, not authored (§B.3) | this synthesis's review |
| 2 | effectivity is domain-relative, not intrinsic (§3.3) | this synthesis's review (W-b, below) |
| 2 | round-trip diffs against a reviewed baseline (C7, §8 item 5) | this synthesis's review (W-c, below) |

`usingdsl.md` is unmodified. Where this document corrects it — the pilot slice —
the correction lives here, marked as a delta.

## 1. The two approaches

Both answer the same question — *what representation should carry the
information in `IEEE_D1.md`* — and each solves the half the other leaves open.

**`denotational.md`** takes the document as the sole source and asks what a
faithful transcription must preserve. Two layers: a **denotational core**
(total, clause-ordered, two-sorted, `noncomputable` — though §3.3 now qualifies
where and why) and a **finite evidence layer** (rational enclosure, separation,
certificate) bridging §4.6's demand to compute results the standard defines over
ℝ. Its contributions are semantic: it locates the computability boundary, gives
the bridge an unconditional soundness theorem, insists on three-outcome
reporting, and identifies four defects in the source.

It has no process. A Lean file is not a thing a working group edits, reviews,
diffs across revisions, or renumbers.

**`usingdsl.md`** answers the engineering question, and answers it well. AFSpec
is an authoring surface sized for review; stable IDs and provenance are
mandatory; `first_match` is normative language semantics with overlap,
reachability and exhaustiveness analysis; modality is enforced data, with the
excellent rule that *a normative requirement expressed only as free text is
rejected*; indexed `Value<f>` / `Code<f>` / `Datum` make sort confusion
untypeable; literals are exact by construction; the trusted primitive base is
explicit and small; §11–§15 supply versioning, reproducibility, phasing,
acceptance criteria and a risk register. The **source digest / semantic digest**
split in §3 is the best single idea in either document.

Its semantics has one hole, and it is exactly where `denotational.md` is
strongest.

## 2. How each informs the other

### 2.1 What `denotational.md` supplies to AFSpec

**The missing accuracy contract.** AFSpec §6.6 says an execution adapter "may
approximate such a term only under an explicit accuracy contract" and never
defines the contract. §10.2 asks for exhaustive evaluation "**where the
mathematical primitive is executable**" — a qualifier carrying the entire
problem silently. `denotational.md` §B is that contract, already written:
`Enclosure`, `Separates`, `enclosure_sound`, `Certificate`.

**Three outcomes, never two.** §B.4 requires every operand tuple to land in
exactly one of **certified**, **refuted**, or **unresolved**, with narrowing
under an explicit budget and exhaustion reported as unresolved — "never as
success, and never as a defect in the specification". AFSpec has no vocabulary
for the third state, and a checker without one will eventually record a budget
exhaustion as a pass.

**Soundness is unconditional; termination is what needs an argument.**
`enclosure_sound` carries no number-theoretic hypothesis, so any validating
certificate discharges §4.6. Transcendence enters only to explain why the search
for one can be expected to finish. A builder who cannot supply that argument
still has a correct system.

**Effectivity is a property of a definition applied to a domain, not of the
definition.** §3.3 (as revised): `⌊log₂|X|⌋` is exact whenever `X` is dyadic —
`(bitlength|m| − 1) + e` for `X = m·2^e` — and §4.7.2 decodes every datum to a
dyadic. So §4.7.4 is exact for the whole exact-arithmetic family and
non-effective only where an ω-result leaves the fragment. This is the single
most consequential fact in either document, and §5 and §7 W-b are built on it.

**Certificates are generated, never authored** (§B.3). Build output that happens
to be normative evidence, so nothing here can drift.

**Round-trip against a reviewed baseline, not an empty diff** (C7, as revised).
AFSpec's Markdown criterion — "shall parse and contain every required stable ID"
(§10.3) — is far too weak under a transcription premise.

**The four source defects, which AFSpec must represent rather than absorb.**
§4.3.2 defines four constructs; the standard uses at least six more. AFSpec's
grammar legislates all of them, and each is an interpretation made on the
standard's behalf — §6.

### 2.2 What `usingdsl.md` supplies to the denotational core

**An authoring layer.** The whole of AFSpec §6. `denotational.md` has no answer
to "who writes this and how is it reviewed".

**Stable IDs instead of clause numbers, and per-quotation provenance.**
`denotational.md` cited `§4.7.4` throughout with no staleness detection. Not
hypothetical: `IEEE_D1.md` was replaced mid-authoring — 660 lines changed, the
pin in `src/rules/conformance.jl` moving `820cb500…` → `75f38b4c…` — and every
citation had to be re-verified by hand. §8 item 6 now requires a digest per
quoted span. The idea is AFSpec's; the incident was the core document's.

**Two digests.** A whole-file digest cannot distinguish a whitespace change from
a rule change. AFSpec §3's split can.

**Modality as enforced data.** §6.12, against `denotational.md`'s "metadata,
never code" and nothing further.

**Acknowledged overlap.** `denotational.md` leans on Lean's match compiler,
which reports *unreachable* patterns — the wrong analysis. §4.3.2's design is
*intentional overlap resolved by order*: `ωAdd(+∞, ∗)` and `ωAdd(∗, +∞)` overlap
deliberately. AFSpec's `@overlap(reason=...)` is what the standard needs.

**Process.** §11–§15, against a seven-item to-do list.

## 3. Where they conflict, and how it resolves

### Conflict A — what is authoritative

`usingdsl.md` §3: "There shall be exactly one editable semantic source: the
AFSpec corpus." `denotational.md` treats `IEEE_D1.md` as normative.

> `IEEE_D1.md` is **normative**. The AFSpec corpus is the **authoritative model
> of it**. Every other artifact is generated. The two are tied by a
> *bidirectional* obligation — round-trip rendering one way, clause coverage the
> other — and neither is optional.

"One source of truth" is right about the model and wrong about the standard. A
model that can drift from the normative text without a build failure is not a
model of it.

### Conflict B — is Lean a target or the semantics?

`usingdsl.md` §8.2: "Lean is a verification target, not the authoring source."
`denotational.md` treats Lean as where meaning lives.

**Both: Lean is generated, and it is still the semantic reference.** AFSpec's
`first_match`, its refinement types and its `Datum`/`Value<f>` distinction need
a denotation, and a Julia compiler is not one — it is a program that could be
wrong. Making the generated Lean define what the IR *means* shrinks the trusted
base from "the AFSpec compiler and its analyses" to "the Lean kernel and the
primitive contracts", without asking anyone to author in Lean.

### Conflict C — the oracle

`usingdsl.md` §8.1: "The interpreter is the behavioral oracle."
`denotational.md` §4.1: for transcendental operations no such oracle exists.

**The oracle is partial by construction, and the language must say where.** §5.

## 4. The better way

Six layers, four obligations.

```
L0  IEEE_D1.md                    normative; digest-pinned; never edited
     |  coverage ^     v round-trip
L1  AFSpec corpus                 authoritative MODEL; stable IDs; provenance;
     |                            modality; first_match; indexed types
L2  CheckedSpec IR                canonical; source digest + semantic digest
     |
     +-- L3a  generated Lean        the DENOTATION. total; noncomputable where
     |                              the standard is non-effective
     +-- L3b  generated interpreter the PARTIAL ORACLE. defined exactly on the
     |                              effective fragment
     +-- L3c  certificates          the BRIDGE. generated by narrowing, checked
     |                              against L3a; three outcomes
     +-- L3d  Markdown, RDF, Julia  presentation, provenance, implementation
```

**Obligation 1 — round-trip.** The Markdown adapter re-renders every modelled
clause; the diff against L0 must equal a reviewed baseline.

**Obligation 2 — coverage.** Every normative clause of L0 is accounted for in
the **clause register** (§7 X-c), which assigns each clause exactly one of
*modelled*, *waived*, or *divergent*.

**Obligation 3 — agreement**, three propositions rather than one equation:

- on the `dyadic`, `rational` and `algebraic` fragments, `L3b ≡ L3a` — a Lean
  goal;
- on the `transcendental` fragment, for each **certified** operand tuple, `L3c`
  witnesses `L3a` by `enclosure_sound`;
- **refuted** and **unresolved** tuples are reported with counts, never absorbed.

**Obligation 4 — digests.** The semantic digest gates regeneration of normative
artifacts; the source and per-quotation digests gate provenance.

## 5. The synthesis's contribution: domain-indexed effectivity

Neither input had this. `denotational.md` §3.3 now carries the underlying fact
(effectivity is domain-relative); what follows is the machinery that makes it a
checkable compiler property, and it refines §3.3's three rows into four.

Every AFSpec declaration receives an **effectivity class**, *computed*, never
annotated:

| Domain of the ω-result | §4.7.4 / §4.7.6 decidable? | Reached by |
|:--|:--|:--|
| `dyadic` | yes — integer work | `ωAdd`, `ωSubtract`, `ωMultiply`, `ωFMA`, `ωFAA`, `ωNegate`, `ωAbs`, `ωCopySign`, the extremum family, `ωConvert` |
| `rational` | yes — exact rational comparison | `ωRecip`, `ωDivide` |
| `algebraic` | yes — needs real-algebraic arithmetic | `ωSqrt`, `ωRSqrt`, `ωHypot` |
| `transcendental` | **no** | `ωExp`, `ωExp2`, `ωLog`, `ωLog2`, `ωLogOnePlus`, `ωExpMinusOne`, §4.10.10–§4.10.16 |

Only the fourth row needs certificates. Scoping the evidence layer to it — not
to everything — is what the domain-relative reading buys.

Primitives declare effectivity **per argument domain**:

```text
primitive function log2(x: Real) -> Real
    effectivity {
        domain dyadic        => exact;       // (bitlength|m| - 1) + e
        domain rational      => exact;
        domain algebraic     => algebraic;
        domain transcendental => symbolic;
    };
```

and the compiler propagates domains alongside types. Propagation needs
**declared closure facts**, which are semantic claims and must be reviewed, not
inferred (§7 X-a):

```text
closure dyadic under { add, subtract, multiply, negate, abs };   // not divide, not sqrt
closure rational under { add, subtract, multiply, divide };      // not sqrt
closure algebraic under { add, subtract, multiply, divide, sqrt };
```

Three consequences:

1. AFSpec §10.2's "where the mathematical primitive is executable" becomes a
   computed set the compiler prints.
2. The certificate obligation is raised **automatically** for every
   `transcendental` declaration, and *only* for those. It cannot be forgotten,
   and it cannot be discharged by an adapter quietly choosing a working
   precision — the failure `denotational.md` §3.3 exists to prevent.
3. Changing a primitive's declared domains, or a closure fact, can move the
   class of declarations that never mention it. The diagnostic names every one,
   giving AFSpec §6.8's trusted-base review actual teeth.

The certificate is `denotational.md` §B.3 as generated IR:

```text
certificate for Exp<Binary8p4se, Binary8p4se, (NearestTiesToEven, SatNone)> {
    entry 0x00 { enclosure [1, 1];                 result 0x40; status certified; }
    entry 0x01 { enclosure [1041/1024, 2083/2048]; result 0x40; status certified; }
    ...
    entry 0x7A { budget_exhausted;                              status unresolved; }
}
```

## 6. Interpretations as a first-class, enumerable output

`usingdsl.md` reserves `@status(value="interpretation")` in one example and does
not develop it. `denotational.md` found six constructs used in normative clauses
that §4.3.2 never defines. Every one is a decision made *on the standard's
behalf*, and burying such decisions in a grammar is how a model quietly becomes
a second standard.

`interpretation` is therefore a declaration kind, not a status string, requiring
a source clause, what the text leaves open, the reading adopted, and the
alternatives rejected. `aifspec report --interpretations` emits the list — the
deliverable to send the working group. For the current draft it opens with
§4.3.2's six undefined constructs and §4.8's escape into English ("The extended
real value encoded by *x*"), which must be an `external` declaration with an
explicit IEEE 754 dependency, not a primitive.

The check is a **coverage** condition, not a cardinality one (§7 X-d): the
parser knows which constructs it accepted beyond §4.3.2's four, and every one of
them must have an interpretation.

## 7. Review of the better way, and the improvements it needed

Prior rounds produced W-a … W-e; W-b and W-c turned out to be defects in
`denotational.md` and have been fixed there. This round found four more. X-a is
the serious one: it is a hole in the fix for W-b.

**X-a — domain propagation was assumed free, and it is not.** §5 said "the
compiler propagates domains alongside types" as though that were mechanical. It
is not: propagation needs to know that dyadics are closed under `+`, `−`, `×`
but **not** under `÷` (1/3) or `√` (√2), that rationals are closed under `÷` but
not `√`, and so on. Those are semantic claims. Getting one wrong silently
mis-classifies an operation — precisely the failure effectivity exists to
prevent, reintroduced one level down.
*Fix:* closure facts are **declared** in the corpus, reviewed like primitives,
and part of the trusted base. §5 now states them explicitly, and criterion 6
requires publishing them.

**X-b — certificates do not scale, and neither document said where the line
is.** A binary operation at K = 8 is 65 536 operand pairs per specialization —
fine. Both documents then gesture at "every format the document defines"; at
K = 16 that is 2³² tuples per specialization, which is not fine.
*Fix:* certification is **required only for §4.5's required set**, which is
finite and small by construction (`F₈` = two formats, `F₄` = one, `F_X` at most
three). Beyond it, effectivity classification and three-outcome reporting still
apply, but certification is opt-in per specialization with coverage reported as
a count. Conformance is a §4.5 notion anyway; extending certification past it
was scope creep.

**X-c — Obligations 1 and 2 could disagree without anyone noticing.** A clause
modelled correctly but divergent from the corrupt transliteration lands in the
rendering baseline; a clause not modelled lands in the coverage waiver. Nothing
forced those lists to be disjoint, so a clause could be waived *and* silently
divergent, satisfying both checks while being neither modelled nor reviewed.
*Fix:* one **clause register**, not two lists. Each clause carries exactly one
status — *modelled*, *waived*, or *divergent* — and a clause appearing under
more than one is a build failure.

**X-d — "interpretations must be non-empty" was a gameable criterion.** It
rewards recording trivia and says nothing about the interpretations that matter.
*Fix:* make it a coverage condition over a computed set. The parser already
knows which constructs it accepted beyond §4.3.2's four; every one must have an
interpretation, and the count is incidental.

**X-e — the pilot slice proves the wrong thing** (inherited from `usingdsl.md`
§13 Phase 1, which is unchanged). It models §3.1, §4.7.2, §4.7.4 and §4.16 — all
`dyadic`, hence all decidable. That pilot yields a working interpreter, passes
exhaustive tests, and gives false confidence, because the effectivity split and
the certificate path are never exercised. It would also have hidden both W-b and
X-a completely.
*Fix:* Phase 1 includes one transcendental. §4.10.9 `Exp` at `Binary8p4se` is
256 operand points — small enough to enumerate by hand, large enough to force
the enclosure machinery and at least one closure fact to exist before anything
is built on them.

## 8. Revised phase plan

Changes from `usingdsl.md` §13 are marked.

| Phase | Content | Change |
|:--|:--|:--|
| 1 | IR, diagnostics, canonical JSON, minimal parser. Model §3.1, §4.7.2, §4.7.4, §4.16 — **and §4.10.9 `Exp`**. Domain-indexed effectivity, declared closure facts, the certificate obligation, the clause register and the rendering baseline all land here. | **X-e**, **X-a**, **X-c** |
| 2 | Reference interpreter as the partial oracle; exhaustive tests on `dyadic`/`rational`/`algebraic`; **narrowing loop and generated certificates for `Exp`, with three-outcome reporting**. Generate Julia *tests* before Julia *implementations*. | certificates pulled forward |
| 3 | Saturation, conversion, required format sets, specializations, conformance modalities. **Certification scoped to §4.5's required set.** Generate the declaration report from the IR. | **X-b** |
| 4 | Block operations; sequence-rest patterns and indexed stochastic rounding as deliberate grammar extensions. | unchanged |
| 5 | RDF/SHACL; Lean adapter emitting definitions **and Obligation-3 goals**. | goals made explicit |
| 6 | AFSpec becomes authoritative *as the model*: generate the Markdown reference, registries, conformance tables; freshness a required CI check. **L0 remains normative.** | Conflict A |

Obligations 1, 2 and 4 apply from Phase 1 — cheap at five clauses, expensive to
retrofit.

## 9. Acceptance criteria

`usingdsl.md` §14, plus six.

Retained: single grammar source; pilot compiles without unresolved proof
obligations; idempotent formatting; canonical JSON round-trips; deterministic
builds; stable IDs and source references on every normative declaration;
exhaustiveness on every total declaration; documented intentional overlap;
narrow-format agreement with the Julia reference; Julia naming changes confined
to the target mapping; SHACL-valid RDF; compiling Lean; CI detects stale
artifacts.

Added:

1. **Round-trip.** Every modelled clause re-renders and the diff against L0
   equals the reviewed baseline exactly.
2. **Clause register.** Every clause in the generated inventory carries exactly
   one status; no clause appears twice; waivers and divergences are reviewed.
3. **Effectivity.** Every declaration has a computed class derived from argument
   domains. Every `transcendental` declaration **within §4.5's required set**
   reports certified / refuted / unresolved counts. Exactly three outcomes, no
   fourth, and no collapsing of the third.
4. **Quotation freshness.** Every quoted span's digest matches L0's current
   bytes.
5. **Interpretation coverage.** Every construct the parser accepted beyond
   §4.3.2's four has an interpretation naming the clause and the alternatives
   rejected.
6. **Trusted base.** The primitive set with its per-domain effectivity **and the
   closure facts** are published, and any change lists every declaration whose
   class moves.

Criterion 3 is the one to defend hardest. Every practical failure of a standards
model is a case that was neither verified nor recorded.

## 10. What this does not solve

- **It does not fix the standard.** §4.3.2's undefined constructs, §4.8's escape
  into English, and the absent accuracy contract behind §4.6 are defects in the
  source. The model records and reports them; only the working group can close
  them.
- **It does not make the transliteration lossless.** L0 is a degraded rendering
  of a PDF. Round-tripping proves the model agrees with the text it has, not
  with the text that was written — which is why the baseline must be reviewed by
  someone holding the PDF.
- **It does not remove the trusted base.** The Lean kernel, the primitive
  contracts with their domain classifications, the declared closure facts, and
  the compiler's canonicalization all remain trusted. The contribution is that
  the base is small, enumerated and reviewable rather than "whatever the
  interpreter does".
- **It does not certify beyond §4.5.** Certification is scoped to the required
  set; wider formats get classification and reporting, not proof.
- **It does not decide `F_X`.** §4.5 leaves the external format subset
  implementation-defined, so conformance is a predicate over a declared `F_X`.
- **It does not guarantee certification terminates.** Budget exhaustion is a
  reportable outcome, not a bug to suppress.
