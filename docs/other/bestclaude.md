# The best way: an authored model, one mechanized denotation, obligation-driven evidence

**Status:** design synthesis. Not an IEEE document. Changes nothing about the
authority of `IEEE_D1.md` or the designated P3109 report.

Inputs, both beside this file: [`betterclaude.md`](betterclaude.md) and
[`bettercodex.md`](bettercodex.md). Their common ancestors are
[`denotational.md`](denotational.md) and [`usingdsl.md`](usingdsl.md).

**Provenance.** `denotational.md` was revised twice during this sequence — the
soundness/termination split, generated-not-authored certificates, domain-relative
effectivity, per-quotation digests, and the rendering baseline all landed after
it was first written. `usingdsl.md` and `bettercodex.md` are unmodified. Where
this document corrects any input, it says so.

## 1. The two syntheses

Both start from `denotational.md` (meaning, and the honest computability
boundary) and `usingdsl.md` (authorship, provenance, lifecycle). They diverge on
where the semantics lives and how evidence is planned.

`betterclaude.md` keeps the standard normative, makes the AFSpec corpus the
authoritative *model*, and ties them with round-trip and coverage obligations.
Its contribution is **domain-indexed effectivity**: a computed class per
declaration, derived from the domains its arguments actually take, so the
evidence layer is scoped rather than universal.

`bettercodex.md` accepts the same layering but attacks two things
`betterclaude.md` got wrong: it will not let a *generator* define semantics, and
it will not let a per-declaration label stand in for evidence planning. Its
contributions are **CoreSpec** — a small calculus with one mechanized denotation
— and **obligation-driven, path-sensitive evidence**.

On the points where they disagree, `bettercodex.md` is right, and two of its
corrections reach further back than `betterclaude.md`, into `denotational.md`.

## 2. What `bettercodex.md` gets decisively right

**1 — CoreSpec, and one denotation instead of N.** `betterclaude.md` §3
Conflict B concluded "Lean is generated, and it is still the semantic
reference." That is wrong in a way I did not see: generating a bespoke Lean
definition per operation and calling it authoritative **puts semantic trust in
the generator**. `bettercodex.md` §4.1 fixes it — define CoreSpec's syntax,
typing judgment and denotation *once* in Lean; emit each checked package as
CoreSpec **data**; prove well-typed packages denote mappings of their declared
types; make generated names thin wrappers over the generic denotation. The Lean
adapter becomes shallow and the semantic module deep. My design had one
generated definition to trust per operation; this has one interpreter, total.
Adopted wholesale.

**2 — Evidence obligations beat effectivity labels.** `betterclaude.md` §5
classified per declaration. `bettercodex.md` §5 derives obligations from each
reachable **case path** and each **observation** made of a value. Both documents
agree the class stays as a diagnostic; the enforceable output is the obligation.
The obligation table — exact arithmetic, algebraic ordering, analytic separation,
exact boundary, external contract — is the right granularity.

**3 — Heterogeneous certificates, and the defect they expose.** This is the most
important catch, and it reaches past `betterclaude.md` into `denotational.md`
§B.3. My `Certificate` structure carries only an `Enclosure`. But a
positive-width interval **cannot** separate a value lying exactly on a rounding
boundary, and `denotational.md` §B.4's own table admits boundary hits *do* occur
for the algebraic row — √4 = 2 is a datum. So the certificate form I defined is
insufficient for a row I claimed was fine, and the W3 fix did not catch it
because it was thinking about transcendentals. `bettercodex.md` §5.1's five
payload forms — exact normalization trace, algebraic witness plus isolating
interval, directed enclosure, symbolic boundary proof, external-contract witness
— are the fix. Adopted.

**4 — Endpoint agreement is not folklore.** `denotational.md` §B.3 has
`separatesCheck` and notes monotonicity as an attached obligation;
`bettercodex.md` makes the theorem an **explicit named dependency of the
certificate**, so a certificate cannot be checked without saying which theorem
licensed the check. Stronger, and adopted.

**5 — An assertion-level ledger, not a clause register.** `betterclaude.md` §7
X-c replaced two lists with one clause register, one status per clause. That
still cannot express what the standard actually looks like: one clause lowering
to several rules, one helper supporting several assertions. `bettercodex.md`
§3.1 uses the **assertion** — smaller than a clause, and many-to-many with
declarations — carrying clause, page, span, byte digest, modality, realizing
declarations, mapping kind, and reviewed rendering divergences. Its critique is
exactly right: "a raw diff can force a renderer to reproduce known mangling,
while a declaration-only round trip can miss omitted requirements." One
mechanism subsumes my round-trip baseline *and* my clause register. Adopted.

**6 — Maturity gates.** `betterclaude.md` had a binary build gate, which forces
a choice between blocking all modelling on unresolved proofs and hiding them.
`bettercodex.md` §8 gives levels — parsed, checked, denoted, rendered,
conformance-certified — each artifact declaring its attained level. Adopted, with
a ratchet added in §9 Y-b.

**7 — Publish the trusted computing base.** §7 enumerates it and lists
independent reduction checks: formatter idempotence, canonical JSON round trips,
a second CoreSpec decoder, proof-kernel checking, exhaustive narrow-format
comparison, cross-adapter digest assertions. Stronger than my criterion 6.

## 3. What `betterclaude.md` carries that `bettercodex.md` lacks

**1 — The arithmetic fact, and the map it produces.** `bettercodex.md` mentions
"`floor(log2(abs(x)))` on a dyadic input, which is exactly decidable" in
passing. `betterclaude.md` §5 derives it — `⌊log₂|X|⌋ = (bitlength|m| − 1) + e`
for `X = m·2^e`, and §4.7.2 decodes *every* datum to a dyadic — and draws the
consequence: §4.7.4 is exact for the entire exact-arithmetic family, so the
evidence engine is needed only where an ω-result leaves the fragment. It then
maps the standard's operations onto the domains. That map is what tells a builder
where the work is; keep it.

**2 — Why certification scopes to §4.5.** `bettercodex.md` speaks of "required
finite specializations" without stating the scaling problem.
`betterclaude.md` §7 X-b does: 65 536 operand pairs at K = 8 is fine, 2³² at
K = 16 is not, so certification is required only for §4.5's set (`F₈` two
formats, `F₄` one, `F_X` at most three) and is opt-in beyond it with coverage
reported. Conformance is a §4.5 notion; extending certification past it was
scope creep in both directions.

**3 — Soundness and termination as a stated principle.** `bettercodex.md` has
the sentence. `denotational.md` §B.4 develops it, including the consequence that
matters practically: a builder who cannot supply the termination argument still
has a correct system, with a weaker completion guarantee.

**4 — Interpretation *coverage*, not just interpretation entities.**
`bettercodex.md` §3.2 has the better entity — ambiguity, adopted reading,
rejected alternatives, approval state, revision history. `betterclaude.md` §7
X-d has the better check: not "interpretations must be non-empty" (gameable) but
a coverage condition over a computed set — the parser knows which constructs it
accepted beyond §4.3.2's four, and every one must have an interpretation.
Combine both.

**5 — The concrete defect inventory.** `bettercodex.md` refers to "damaged
source markup" and to constructs "beyond the constructs explicitly described".
`denotational.md` names them: six undefined constructs with sites (guards
§4.10.8/§4.10.2, conjunctive guards §4.7.5, in-pattern disjunction §4.7.5,
`where` blocks §4.7.2/§4.7.4/§4.7.6, conditional results §4.11.1, prose side
conditions §4.7.4 Details); the mangled `ωSaturate_{M^lo,M^hi}` signature at two
sites; §4.8's escape into English. The named list is what you send the working
group.

**6 — Provenance honesty between the documents themselves.** When a design
record is revised in light of its sibling, saying so prevents a reader from
misattributing the idea. Cheap, and it keeps the record usable later.

## 4. Not actually conflicts

Two apparent disagreements dissolve on reading.

**Is a declaration-wide class useful?** `bettercodex.md` calls it "too coarse"
and then says "classification is derived and diagnostic; evidence obligations are
the enforceable output." That is agreement. The class earns its place as a
*scoping and diagnostic* device — it says which operations touch the evidence
engine at all, and it is what makes the trusted-base diagnostic possible
(changing a primitive's declared domain names every declaration whose class
moves). The obligations are what the build enforces.

**Authority.** `bettercodex.md` §3's three-way split — normative source,
authoritative editable model, canonical semantic form — is `betterclaude.md`'s
Conflict A resolution with CoreSpec inserted, and it is the better statement of
it.

## 5. The combined design

```
   pinned P3109 revision  (normative; digest-pinned; never edited)
        |
        |  assertion inventory + reviewed transcription ledger
        v
   AFSpec corpus          (authoritative EDITABLE MODEL; stable IDs; modality;
        |                  first_match; indexed types; interpretations)
        |  parse, resolve, type-check, elaborate, analyze
        v
   CoreSpec package       (canonical SEMANTIC FORM; small calculus;
        |                  source digest + semantic digest + maturity level)
        |
        +--> CoreSpec denotation in Lean   ONE mechanized meaning; generated
        |                                  names are wrappers, not definitions
        +--> evidence engine + certificates  path-sensitive obligations;
        |                                    heterogeneous payloads; 3 outcomes
        +--> reference evaluator           candidate producer; oracle only where
        |                                  it decides an obligation exactly
        +--> adapters                      Julia, Markdown, RDF, tables
```

Three authorities, never collapsed: the pinned revision is **normative**; AFSpec
is the **authoritative model of it**; CoreSpec is the **canonical semantic form
of the model**. "Single source of truth" governs editable declarations. It does
not license a transcription to override the standard silently.

## 6. Evidence discipline

**Obligations, not labels.** The planner derives an obligation per reachable
case path and per observation. Domains and their declared closure facts —
dyadics closed under `+ − ×` but not `÷` or `√`; rationals closed under `÷` but
not `√`; algebraics closed under `√` — are how domains propagate; the *class* is
the diagnostic summary. Closure facts are declared, reviewed, and part of the
published trusted base.

**Where the work actually is**, from §3 item 1:

| Domain of the ω-result | §4.7.4 / §4.7.6 | Reached by |
|:--|:--|:--|
| `dyadic` | exact, integer work | `ωAdd`, `ωSubtract`, `ωMultiply`, `ωFMA`, `ωFAA`, `ωNegate`, `ωAbs`, `ωCopySign`, the extremum family, `ωConvert` |
| `rational` | exact rational comparison | `ωRecip`, `ωDivide` |
| `algebraic` | real-algebraic arithmetic | `ωSqrt`, `ωRSqrt`, `ωHypot` |
| `transcendental` | undecidable in general | `ωExp`, `ωExp2`, `ωLog`, `ωLog2`, `ωLogOnePlus`, `ωExpMinusOne`, §4.10.10–§4.10.16 |

**Certificates are generated, heterogeneous, and named.** Each entry: operand
tuple, claimed result, path/case ID, evidence kind, payload, checker version,
licensing theorem, semantic digest. Payloads: exact normalization trace;
algebraic witness with isolating interval; directed enclosure **plus the named
monotonicity theorem** that makes endpoint agreement sound; symbolic boundary
proof selecting the tie rule; external-contract witness.

**Exactly three outcomes.** *certified* — a small checker validated evidence for
the claimed result. *refuted* — valid evidence gives a different result.
*unresolved* — budget, theory or contract insufficient. Budget exhaustion is
always unresolved, never success and never a defect in the specification.
Soundness of an accepted certificate is independent of termination of the search
for one.

**Scope.** Certification is *required* only for §4.5's required specializations,
which are finite and small by construction. Beyond them, classification and
three-outcome reporting still apply; certification is opt-in with coverage
reported as a count.

**The evaluator has no conformance force.** It is an oracle exactly where it
decides an obligation exactly; elsewhere it produces a candidate whose status is
nil until a certificate validates it. Approximate host arithmetic may guide
interval refinement and may never enter canonical semantics or certify itself.

## 7. Fidelity: the transcription ledger

One mechanism, replacing both round-trip baselines and clause registers. The
unit is the **assertion** — a definition, equation, requirement, side condition,
note or external dependency — smaller than a clause and many-to-many with
declarations. Each entry records the assertion ID and pinned revision; clause,
page, span and **digest of the cited bytes**; normative status and modality; the
realizing AFSpec declarations and case IDs; whether the mapping is exact,
interpretive, externally defined or waived; and any reviewed rendering
divergence caused by damaged source markup.

The build fails on an unledgered normative assertion, a stale span digest, or an
unreviewed waiver.

Rendering divergences are expected and must be reviewed by someone holding the
PDF, because the source is already corrupt at sites the model must render
correctly — `ωSaturate_{*M*}^{lo}_{*,M*}^{hi}` at two places in the current
file. Only the PDF says which of model and transliteration is right.

## 8. Maturity, and the trusted computing base

**Levels:** parsed → checked → denoted → rendered → conformance-certified. Every
artifact states its attained level, and no consumer may assert conformance from
an artifact below the top level.

**Published TCB:** the AFSpec parser, resolver, type checker and lowering to
CoreSpec; CoreSpec's formal denotation and the Lean kernel; primitive and
external contracts; **the declared closure facts**; the certificate checker and
each theorem library it invokes; canonicalization and digest implementations.
Reduced by independent checks — formatter idempotence, canonical JSON round
trips, a second CoreSpec decoder, proof-kernel checking, exhaustive narrow-format
comparison, cross-adapter semantic-digest assertions.

A semantic digest identifies meaning. It is not evidence of fidelity to the
standard, nor of correctness; the ledger and the certificates carry those,
separately.

## 9. Review of the combined design

Five findings. Y-e is the sharpest and contradicts a worked example in
`bettercodex.md`.

**Y-a — path-sensitive planning is undecidable, and neither document says which
way it errs.** Deriving obligations "from each reachable case path" needs
reachability, and guards range over reals (`ωSqrt(X) if X < 0`, `ωCopySign(±∞, Y)
if Y ≥ 0`). Undecidable in general. A planner that assumes a path unreachable
silently drops an obligation; one that assumes it reachable merely wastes work.
*Fix:* the planner is **sound by over-approximation**. Undecided reachability
plans the obligation. Unreachable-but-planned is waste; reachable-but-unplanned
is a hole, and the asymmetry must be stated in the analysis contract, not left
to the implementer.

**Y-b — maturity gates can become a permanent excuse.** Nothing in
`bettercodex.md` §8 forces a level to rise, or prevents shipping a `denoted`
package where conformance evidence is implied.
*Fix:* the attained level is embedded in every artifact and asserted by every
consumer that claims conformance; and a **ratchet** — the level attained for a
given assertion may not decrease across source revisions without a recorded,
reviewed waiver. Without the ratchet, "levels" is a vocabulary for deferring
indefinitely.

**Y-c — heterogeneous certificates grow the trusted base, and that is not
priced.** Five payload forms means five checkers, each with its own theorem
dependencies: monotonicity for enclosures, minimal-polynomial arithmetic for
algebraic witnesses, symbolic identity for boundary proofs.
`bettercodex.md` publishes the TCB but treats payload forms as free.
*Fix:* payload forms are a **closed, versioned set**. Adding one is a TCB change
requiring the review an added primitive gets, and the diagnostic must name every
certificate whose validity now depends on the new checker.

**Y-d — the assertion inventory has a bootstrap problem, worse than the clause
version.** "The build fails on an unledgered normative assertion" presupposes an
enumeration of normative assertions, extracted from the same damaged source.
Assertions are finer and more numerous than clauses, so the problem is larger,
not smaller, and neither document says who produces the inventory or how it is
validated.
*Fix:* the inventory is a generated, digest-pinned artifact reviewed once per
source revision by someone holding the PDF. Its diff is the **first** thing
examined when the pinned revision changes — which, on the evidence of this
sequence, is more often than a plan assumes.

**Y-e — the motivating example for path-sensitivity is not in the standard, and
the real requirement is stronger than "path-sensitive".** `bettercodex.md` §9
Phase 2 requires the pilot to "include its exact `exp(0)` path rather than
treating the family uniformly." There is no such path. §4.10.9 gives `ωExp` four
clauses — `NaN`, `+∞`, `−∞`, `X` — and no `ωExp(0) → 1`. Zero falls through to
`ωExp(X) → e^X`. The asymmetry is visible one line down: `ωLog(0) → −∞` **is** an
explicit clause, so `Log` has the special case in its clause list and `Exp` does
not.

So recognizing `e^0 = 1` is not path analysis over the clause structure. It
requires **symbolic normalization of the ω-expression** — noticing that `e^X`
with `X` normalizing to `0` is exactly `1`. That is a different and larger
capability than walking cases, and it belongs in the trusted base as an
explicitly bounded simplifier with its own contract.
*Fix:* separate the two capabilities in the design. **Path sensitivity** reads
the clause list and is cheap. **Expression normalization** recognizes exact
values inside a terminal clause, is a CAS fragment, is part of the TCB, and must
be bounded and declared. Requiring the pilot to exercise `exp(0)` is right — but
as a test of the normalizer, not of the path planner, and `bettercodex.md`
attributes it to the wrong mechanism.

## 10. Phase plan

| Phase | Content |
|:--|:--|
| 1 | AFSpec parsing, typed lowering, canonical CoreSpec, diagnostics, digests. **CoreSpec's Lean denotation defined in the same phase** — not deferred behind generators. Assertion inventory and transcription ledger. Model §3.1, §4.7.2, §4.7.4, §4.16, one exact arithmetic operation, and **§4.10.9 `Exp`**. Declared closure facts; obligation planner with its over-approximation contract (Y-a); bounded normalizer with its contract (Y-e). |
| 2 | Every evidence path exercised: exact rational evaluation, one algebraic witness, directed enclosures with named monotonicity theorem, a symbolic boundary certificate, three-outcome reporting. Pilot covers ordinary, special-value, exact-tie, non-boundary transcendental, **and the `exp(0)` normalization case**. |
| 3 | Required specializations and modalities; certification scoped to §4.5. Julia *tests* before Julia *implementations*; then Markdown and RDF. Every adapter embeds and verifies the same semantic digest and maturity level. |
| 4 | Conversion, saturation, remaining scalar operations, block operations, external IEEE 754 contracts, stochastic parameters. Extend AFSpec syntax only when a real clause cannot lower cleanly to existing CoreSpec forms. |
| 5 | Authority migration, after reviewed coverage, structural rendering, evidence checks and semantic equivalence with the current implementation. Each pinned revision and its ledger is preserved, never rewritten. **The pinned revision stays normative.** |

## 11. Acceptance criteria

- One grammar source for grammar and parser; every surface construct has a
  specified lowering to CoreSpec.
- CoreSpec typing and denotation defined and checked in Lean; generated names
  are wrappers over the generic denotation, never independent definitions.
- Every normative source assertion is modelled, interpreted, externally pinned,
  or explicitly waived in the reviewed ledger; span digests current; rendering
  divergences reviewed against the PDF.
- Ordered cases exhaustive; overlaps acknowledged; unreachable cases rejected or
  demonstrated to be source defects.
- Evidence planning is path-sensitive, over-approximating on undecided
  reachability, and produces inspectable obligations.
- Expression normalization is bounded, declared, and in the published TCB.
- Every §4.5 required specialization is generically proved or has a certified
  entry per operand tuple; refuted and unresolved counts are zero at the
  conformance-release gate and reported at every other gate.
- Certificate payload forms are a closed versioned set; certificate checking is
  independent of candidate production; each certificate names its licensing
  theorem and checker version.
- Every construct the parser accepted beyond §4.3.2's four constructs has an
  interpretation naming the clause, the adopted reading, and the alternatives
  rejected.
- Maturity level embedded in every artifact, asserted by every conformance
  claim, and non-decreasing per assertion without a reviewed waiver.
- Trusted computing base published, including closure facts and normalizer
  bounds; any change lists every declaration or certificate it affects.
- Deterministic canonical output and digests; Julia naming confined to the
  target adapter; generated Lean compiles; RDF satisfies SHACL; CI detects every
  stale artifact.

## 12. What this does not solve

- **It does not fix the standard.** §4.3.2's six undefined constructs, §4.8's
  escape into English, and the absent accuracy contract behind §4.6 are defects
  in the source. The model records and reports them; only the working group can
  close them.
- **It does not make the transliteration lossless.** The pinned source is a
  degraded rendering of a PDF. The ledger proves the model agrees with the text
  it has; only a PDF reviewer can say whether that text is right.
- **It does not remove trust, only bound it.** The Lean kernel, CoreSpec's
  denotation, primitive and external contracts, closure facts, normalizer
  bounds, certificate checkers and canonicalization all remain trusted. The
  contribution is that the base is enumerated, versioned and independently
  cross-checked rather than implicit in an interpreter.
- **It does not certify beyond §4.5**, and does not guarantee certificate search
  terminates. Budget exhaustion is a reportable outcome, not a bug to suppress.
- **It does not decide `F_X`.** §4.5 leaves the external format subset
  implementation-defined, so conformance is a predicate over a declared `F_X`.

The rule the two syntheses converge on, with one addition: **author once, lower
once, define meaning once, never confuse a computed candidate with checked
evidence — and never let the mechanism that found an exact value go unnamed.**
