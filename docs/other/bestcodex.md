# The best combined approach: AFSpec, CoreSpec, and checked finite evidence

**Status:** reviewed synthesis of [betterclaude.md](betterclaude.md) and
[bettercodex.md](bettercodex.md). This is an implementation recommendation, not
an IEEE document, and does not alter the authority of the designated P3109
source revision.

The two input syntheses agree on the destination: an editable DSL, a typed
canonical representation, exact denotational semantics, generated target
artifacts, assertion-level provenance, and checked evidence for required finite
specializations. They differ mainly in where to put meaning and how to decide
what can be computed. Resolving those differences produces a stronger design
than either one alone.

## 1. Decision

Adopt a **verified specification pipeline** with five rules:

1. Authors edit AFSpec, not Lean, Julia, RDF, generated Markdown, or
   certificates.
2. AFSpec lowers to a small typed calculus, CoreSpec, through one compiler
   module.
3. CoreSpec’s denotation is defined once in Lean; generated operation names are
   wrappers over CoreSpec data, not separately generated semantics.
4. Executability is determined from path-specific evidence obligations, not a
   blanket label on an operation or primitive.
5. Conformance claims require checked finite evidence with exactly three
   outcomes: certified, refuted, or unresolved.

This retains AFSpec’s editorial leverage, the denotational model’s honesty
about exact reals, `betterclaude.md`’s coverage and interpretation disciplines,
and `bettercodex.md`’s small semantic kernel and stronger certificate model.

## 2. What the two syntheses contribute

- **Authoring — `betterclaude.md`:** AFSpec is the editable model, with stable
  IDs, modality, provenance, and ordered rules.
- **Meaning — `bettercodex.md`:** AFSpec lowers to CoreSpec data interpreted by
  one mechanized denotation.
- **Fidelity — both:** a reviewed assertion inventory and transcription ledger
  provide coverage, source-span freshness, and rendering checks.
- **Ambiguity — `betterclaude.md`:** interpretations are first-class,
  enumerable declarations rather than hidden parser decisions.
- **Computability — `bettercodex.md`:** generate path-sensitive evidence
  obligations based on required observations.
- **Certification — both:** exact, algebraic, enclosure, boundary, and external
  witnesses feed a small checker.
- **Failure reporting — `betterclaude.md`:** certified, refuted, and unresolved
  remain distinct; budget exhaustion is unresolved.
- **Trust — `bettercodex.md`:** publish the trusted base and reduce it with a
  generic CoreSpec formalization and independent checks.
- **Delivery — both:** use staged maturity gates and include a transcendental
  operation in the pilot.

## 3. The architecture

```text
L0  Pinned source revision
       |  reviewed assertion inventory
       |  source spans, digests, interpretations, waivers
       v
L1  AFSpec corpus                         editable semantic model
       |  parse, resolve, check, elaborate
       v
L2  Canonical CoreSpec package            typed semantic interchange
       |---------------|-----------------|------------------|
       v               v                 v                  v
L3a Lean denotation   L3b evidence      L3c evaluator      L3d adapters
     and proofs           planner and       exact only          Julia
                          checker                              Markdown
                                                               RDF/SHACL
       \_______________ checked claims and shared digests __/
                               |
                               v
L4  Conformance bundles and revision reports
```

L0 is immutable *as a pinned revision*; a new draft creates a new revision and
ledger rather than rewriting the old one. L1 is authoritative as the editable
machine model. L2 is authoritative as that model’s canonical meaning. L3 and L4
are derived and reproducible.

The main compiler is a deep module. Its interface stays small:

```julia
compile(sources::Vector{SourceFile}, options::CompileOptions)::CompileResult
emit(spec::CheckedSpec, target::EmitTarget)::ArtifactBundle
```

Reading and writing files belongs to adapters. Parsing, name resolution, type
checking, CoreSpec lowering, provenance validation, rule analysis,
canonicalization, and evidence-obligation derivation stay in the compiler’s
implementation. Tests use the same interface as callers.

## 4. Four independent obligations

No single digest, proof, renderer, or test establishes that the model is good.
The pipeline must discharge four independent obligations.

### 4.1 Fidelity

Every normative source assertion must appear in a reviewed assertion inventory.
The transcription ledger maps each assertion to one or more AFSpec declarations
or rule cases and records whether it is:

- modelled exactly;
- modelled through an approved interpretation;
- delegated through a pinned external contract; or
- explicitly waived with a reviewed reason.

Each entry carries a source span and digest. The build fails on an unmapped
assertion, a stale quotation, or an unreviewed waiver.

Rendering is checked structurally at the equation and requirement level. A
reviewed divergence baseline records places where the available source text is
already damaged or where generated typography intentionally differs. Requiring
a raw empty textual diff would reward reproduction of corrupt markup; checking
only declaration IDs would miss omitted semantics.

### 4.2 Semantic preservation

Every AFSpec construct has one specified lowering to CoreSpec. The formal
CoreSpec module defines:

- syntax and well-typedness;
- refinement and indexed-type interpretation;
- first-match behavior;
- exact and extended-real expression denotation;
- explicit partiality;
- primitive and external contracts; and
- the denotation of conformance predicates.

The Lean adapter emits CoreSpec data. Convenience definitions refer to the
generic denotation. This avoids maintaining one semantics in the compiler and a
second in generated Lean.

Semantic preservation has two checked parts: lowering fixtures establish that
surface forms become the intended CoreSpec forms, and Lean establishes that a
well-typed CoreSpec package denotes mappings of the declared types. Ultimately,
the lowering itself should be verified or validated by an independent decoder
and structural round trip.

### 4.3 Behavioral evidence

For exactly decidable paths, the reference evaluator must agree with the formal
denotation. For other paths, a result is only a candidate until a certificate
checker validates evidence connecting it to the denotation.

For each required finite specialization, either a generic theorem covers all
operands or every operand tuple has a certificate. Reports retain separate
certified, refuted, and unresolved counts. No success criterion may silently
discard the unresolved set.

### 4.4 Reproducibility and lineage

All derived artifacts carry:

- AFSpec language and CoreSpec schema versions;
- source revision and source-corpus digest;
- canonical semantic digest;
- transcription-ledger digest;
- evidence-policy digest;
- generator or checker name and version.

Source, semantic, ledger, and evidence digests answer different questions and
must not be substituted for one another. Canonical builds are independent of
filesystem order, locale, timezone, hash randomization, and host floating-point
state.

## 5. The AFSpec/CoreSpec seam

AFSpec retains the authoring specification in [usingdsl.md](usingdsl.md), with
the following additions and constraints.

### 5.1 Surface language responsibilities

AFSpec directly represents:

- Format families and constrained format instances.
- `Datum`, `Code<f>`, and `Value<f>` as distinct types.
- Pure functions and externally visible operations.
- Named, ordered, guarded cases with explicit bindings.
- Exact integers and rationals and symbolic real expressions.
- Requirements with `shall`, `should`, and `may` modalities.
- Notes and examples that cannot be normative dependencies.
- Interpretations, external contracts, and assertion provenance.

The standard’s `Binary` remains `Binary` in AFSpec. A Julia mapping may name the
format type `BinaryFormat` and the indexed encoded-value representation
`Binary`, but that rename cannot affect semantic IDs or source rendering.

### 5.2 CoreSpec responsibilities

CoreSpec is intentionally less convenient. Its closed node set should include
only typed literals, variables, calls, immutable lets, conditionals, finite
collections, pattern tests, ordered case selection, and explicit constructors
for special values and partial results. Surface sugar is absent.

The deletion test justifies this seam: without CoreSpec, each adapter must
reimplement elaboration, ordering, type interpretation, and error-prone DSL
details. With it, that complexity is local to the compiler and every adapter
receives leverage from one checked representation.

Case order is preserved in the semantic digest. Proven overlap is allowed only
with a reviewed acknowledgement. Proven unreachable cases are errors unless
the ledger marks them as a source defect. Undecidable overlap, exhaustiveness,
or refinement questions become named proof obligations.

### 5.3 Interpretation and external declarations

An interpretation is not merely `@status("interpretation")`. It records the
gap, adopted meaning, alternatives, consequences, approval, and source
assertion. The current inventory is expected to include the constructs used but
not defined by the equation-language clause: guards, conjunctive conditions,
pattern disjunction, local `where` bindings, conditional results, and parameter
side conditions.

An external declaration identifies semantics supplied by another standard. It
includes a pinned citation, typed contract, permitted evidence mechanism, and
version policy. External IEEE formats must use this form rather than an opaque
primitive with no visible dependency.

## 6. One denotation, two execution modes

CoreSpec’s formal denotation uses the closed extended reals required by P3109:
one NaN, two infinities, ordinary mathematical reals, and no mathematical
negative zero. Encoded distinctions live only in format-indexed values.

An operation has the structural form:

```text
decode operands -> apply exact omega operation -> project once -> encode result
```

The formal denotation may be noncomputable. That is a faithful property, not a
failure.

The reference evaluator has two modes:

1. **Exact mode** computes only when the required observation is decidable in
   its supported theory.
2. **Candidate mode** uses directed arbitrary-precision computation to propose
   enclosures or results, but cannot certify itself.

No adapter may turn candidate mode into silent host-language rounding. The
formal denotation remains the meaning in both modes.

## 7. Evidence planning by observation

`betterclaude.md` improves on naive call-graph classification by making
effectivity depend on argument domains. That is necessary but not sufficient.
The final design tracks the **observation required of an intermediate value** as
well as its domain.

For example, `log2(q)` is generally not an algebraic value for rational `q`, but
`floor(log2(q))` is exactly decidable for positive rational `q` by integer
comparison. Conversely, merely knowing that a result is algebraic does not by
itself choose the correct side of a rounding boundary. Classification must
follow the question the semantics asks.

The compiler therefore derives obligations per reachable case path:

```text
expression domain + requested observation + path assumptions
                              |
                              v
                 evidence strategy or proof obligation
```

Supported strategies initially are:

| Strategy | Typical obligation |
|:--|:--|
| Exact normalization | Rational equality, integer division, parity, dyadic `floor(log2(...))` |
| Algebraic decision | Sign or equality of a real algebraic expression |
| Directed enclosure | Analytic expression separated from a projection boundary |
| Boundary proof | Exact tie, exact representable result, or special identity such as `exp(0)=1` |
| External witness | Claim governed by a pinned external contract |

This plan is derived, never hand-labelled as an operation-wide truth. Primitive
contracts describe supported domain/observation pairs. Changing a primitive
contract produces a semantic review report listing every affected obligation.

## 8. Certificate protocol

A certificate is tied to the semantic digest, operation specialization, operand
tuple or generic domain, selected case path, claimed result, and evidence
policy. Its payload matches one strategy from §7.

For an analytic enclosure, the checker requires:

1. A proof-producing enclosure of the exact denotational value.
2. A proof that every value in that enclosure projects to the claimed code.
3. Any monotonicity, continuity, or boundary-exclusion theorem used by step 2.

Equal endpoint projections alone are accepted only when a checked theorem makes
that implication valid for the projection and interval. Exact ties use a
boundary proof; they are not left to an enclosure loop that can never separate
them.

Certificate production runs under explicit resource limits and returns exactly:

- `certified(evidence_digest)`;
- `refuted(counterevidence_digest, actual_result)`; or
- `unresolved(reason, budget_used)`.

Soundness of accepted evidence is unconditional on search termination. Claims
about eventual completion—whether based on finiteness, algebraic decidability,
or transcendence—are separately named theorems or engineering expectations.

Certificates are generated conformance evidence, not normative source text.
They are checked by a smaller module that does not share approximate result
logic with the producer.

## 9. Maturity gates

A single “build passed” state hides too much. Every package reports the highest
gate it attained:

- `parsed` — syntax is valid.
- `checked` — names, types, refinements, provenance, and ordered-rule analyses
  pass or expose named obligations.
- `denoted` — CoreSpec data is accepted by the formal semantic module.
- `faithful` — assertion coverage, quotation freshness, interpretations, and
  the rendering baseline are reviewed.
- `evaluated` — exact evaluator agreement passes on its declared domain.
- `certified` — required finite specializations have no refuted or unresolved
  tuples.
- `publishable` — all configured documentation, graph, proof, implementation,
  and freshness policies pass.

Unresolved proof obligations may be useful during transcription and analysis,
but artifacts state them prominently. They cannot cross a release gate whose
policy requires discharge.

## 10. Knowledge graph and reports

The RDF graph is a query adapter over CoreSpec plus the transcription and
evidence records. It is not another semantics. It represents:

- Revisions, clauses, assertions, declarations, specializations, and cases.
- Order between cases and dependencies between semantic entities.
- Requirements, modalities, interpretations, waivers, and informative notes.
- External contracts and pinned citations.
- Evidence obligations, certificates, outcomes, and generated artifacts.
- Source, semantic, ledger, and evidence lineage.

Named graphs isolate revisions, PROV-O expresses derivation, and SHACL checks
shape constraints. Required reports include semantic revision diff, clause
coverage, stale quotations, interpretations, trusted primitives/externals,
evidence outcomes, and conformance status.

## 11. Review of this combined design

The combined proposal was reviewed against the failure modes in both inputs and
improved as follows.

**Generated Lean could still drift from AFSpec.** Generating bespoke function
bodies would make the generator part of every operation’s semantics. CoreSpec
data plus one generic Lean denotation removes that duplicated implementation.

**Domain-indexed effectivity was still too coarse.** The example classification
of `log2` demonstrates the problem: value class and decidability of an
observation are different. Evidence planning now uses domain, observation, and
path assumptions.

**“Transcendental operations do not hit boundaries” had exceptions and required
more theorem than stated.** Special inputs such as zero or one can produce exact
results, and operation families need separate arguments. Boundary proofs and
path-sensitive planning remove the blanket claim.

**Positive-width enclosures could not certify ties.** Heterogeneous certificate
forms now include exact and symbolic boundary witnesses.

**Endpoint equality was not independently sufficient.** The checker now demands
the monotonicity or boundary theorem that licenses endpoint reasoning.

**A round-trip diff could preserve corruption.** The assertion ledger combines
structural rendering with reviewed divergences, while the coverage inventory
detects omissions.

**The normative source was described as “never edited.”** Only a pinned revision
is immutable. New drafts create explicit revision lineage and semantic diffs.

**A generated certificate was at risk of being called normative.** It is
evidence for a conformance claim; the standard and its authoritative model
remain distinct from the evidence bundle.

**Proof incompleteness could freeze useful transcription work.** Maturity gates
allow honest intermediate artifacts without weakening publication policy.

## 12. Implementation plan

### Phase 1: prove the shape

Implement the AFSpec parser, formatter, diagnostics, assertion inventory,
transcription ledger, typed CoreSpec lowering, canonical serialization, and
digests. In Lean, define CoreSpec syntax, typing, and first-match denotation.

The pilot corpus includes format constraints, decode, rounding, projection,
next-greater/next-less, one exact arithmetic operation, and `Exp` on a required
eight-bit format. This exercises indexed types, clause order, exact projection,
special values, and analytic evidence before the architecture hardens.

### Phase 2: prove the evidence protocol

Implement exact normalization, algebraic decisions, directed enclosures,
boundary witnesses, the independent certificate checker, and three-outcome
reporting. Exercise at least:

- an ordinary exact rational result;
- a NaN or infinity path;
- an exact rounding tie;
- `exp(0)=1` as an exact analytic special case; and
- a non-boundary transcendental result requiring enclosure refinement.

### Phase 3: establish conformance

Model required formats, projections, operation specializations, external format
selection, and modalities. Exhaustively enumerate required narrow formats or
replace an enumeration with a checked generic theorem. Generate declaration,
coverage, interpretation, and evidence reports.

### Phase 4: add consumer adapters

Generate Julia tests first, then Julia definitions where appropriate. Add
Markdown structural rendering and RDF/SHACL. Every adapter rejects a package
whose declared semantic digest differs from the one it consumed.

### Phase 5: expand and migrate

Complete scalar and block operations, add deliberate syntax extensions only
where CoreSpec cannot already express a clause clearly, and pin external
contracts. Make AFSpec authoritative as the editable model only after the
`faithful` and configured conformance gates pass.

## 13. Acceptance criteria

The system is ready for authoritative model use when all of these hold:

- One grammar source drives the AFSpec parser and published grammar.
- Every AFSpec construct has a documented, tested CoreSpec lowering.
- The generic CoreSpec typing and denotation compile in pinned Lean tooling.
- Every normative assertion is exactly modelled, interpreted, externally
  pinned, or reviewed as a waiver.
- Every quotation digest and rendering-divergence baseline is current.
- The interpretations report is reviewed and traces each decision to its source
  gap.
- Ordered rules retain source order; overlaps are acknowledged; unreachable
  rules and exhaustiveness gaps are errors or explicit source defects.
- Evidence obligations are derived by domain, observation, and path.
- The certificate checker handles exact, algebraic, enclosure, boundary, and
  external witnesses without trusting approximate candidate results.
- Required conformance bundles contain no refuted or unresolved tuples.
- The primitive and external trusted base is published with its dependents.
- All artifacts carry matching lineage and semantic digests.
- Julia’s `BinaryFormat`/`Binary` spelling remains an adapter mapping.
- Generated Lean compiles, RDF passes SHACL, Markdown passes structural fidelity
  checks, and CI detects stale outputs.

The resulting system is neither “a DSL with several generators” nor “a Lean
model with some tooling.” It is one authored model, one small semantic kernel,
and multiple independently checkable claims about fidelity, meaning, behavior,
and conformance.
