# A better way: an authored specification with a mechanized semantic kernel

**Status:** reviewed design synthesis. This is not an IEEE document and does
not change the authority of the designated P3109 source revision.

This document treats [denotational.md](denotational.md) and
[usingdsl.md](usingdsl.md) as two approaches to one goal: preserving P3109 as a
precise, reviewable, computable-where-possible, and auditable specification.

## 1. What each approach gets right

`denotational.md` starts from meaning. It identifies the closed extended reals,
format-indexed code points, first-match equations, and the
decode–operate–project factorization as the semantic core. More importantly, it
does not pretend that an exact-real definition containing transcendental
functions is automatically executable. Its finite evidence layer—exact
evaluation where possible, certified enclosures elsewhere, and explicit
unresolved outcomes—is the necessary bridge from denotation to conformance.

Its weakness is authorship. Lean-shaped definitions are valuable verification
material, but they expose proof-assistant and library details to editors, do not
by themselves preserve normative prose or modality, and provide no complete
revision, rendering, or multi-target generation workflow.

`usingdsl.md` starts from authorship and lifecycle. AFSpec gives the standard a
small editorial language, stable identities, clause provenance, exact literals,
indexed types, ordered rules, conformance requirements, deterministic digests,
and adapters for Julia, Lean, Markdown, and RDF. Its compiler is a deep module:
a small interface hides parsing, resolution, checking, analysis, and
canonicalization, giving callers leverage and maintainers locality.

Its weakness is the transition from exact meaning to executable evidence.
Calling the interpreter an oracle is too strong for general exact-real
expressions, and an unspecified “accuracy contract” does not establish that an
approximated result rounds to the value required by the standard.

The approaches therefore fit together, but simply placing them side by side is
not enough. They need one semantic seam and one evidence discipline.

## 2. The combined design

Use AFSpec as the only editable semantic model, but lower it to a much smaller
calculus named **CoreSpec**. The transcription ledger remains editable
provenance and review data; it cannot define operational meaning. Define
CoreSpec’s denotation once, formally. All executable and presentational
artifacts consume the same checked CoreSpec package.

```text
Pinned P3109 source revision
        |  assertion inventory and reviewed transcription ledger
        v
AFSpec editorial source
        |  parse, resolve, type-check, elaborate, analyze
        v
Canonical CoreSpec package
        |--------------------|--------------------|-------------------|
        v                    v                    v                   v
formal denotation      evidence engine      reference evaluator      adapters
(Lean)                 and certificates     (defined fragment)       Julia/docs/RDF
```

The important improvement is the CoreSpec seam. AFSpec is allowed to be
pleasant to author; CoreSpec is required to be small enough to define and
verify. Surface conveniences—guarded constraints, named cases, `where`
bindings, set-pattern sugar, and operation specialization—must lower to a few
typed CoreSpec forms. Adapters never interpret AFSpec syntax and never invent
semantics.

The compiler module keeps the two-operation interface proposed by
`usingdsl.md`:

```julia
compile(sources::Vector{SourceFile}, options::CompileOptions)::CompileResult
emit(spec::CheckedSpec, target::EmitTarget)::ArtifactBundle
```

Internally, `compile` owns the elaboration to CoreSpec. The formalizer,
evaluator, evidence engine, and generators are adapters at real seams because
multiple implementations consume the same checked package.

## 3. Authority and fidelity

Three different kinds of authority must not be collapsed:

1. The pinned P3109 revision is the **normative source**.
2. AFSpec is the **authoritative editable model** of that revision.
3. CoreSpec is the **canonical semantic form** of that model.

During a revision, discrepancies are possible and must be visible. “Single
source of truth” applies to editable semantic declarations; it does not grant a
transcription permission to override the standard silently.

### 3.1 The transcription ledger

Maintain a reviewed, machine-readable ledger relating source assertions to
AFSpec entities. An assertion is smaller than a clause and may be a definition,
equation, requirement, side condition, note, or external dependency. Each entry
records:

- A stable assertion ID and the pinned document revision.
- Clause, page, source span, and digest of the cited bytes.
- Normative status and requirement modality.
- The AFSpec declarations and case IDs that realize the assertion.
- Whether the mapping is exact, interpretive, externally defined, or waived.
- Any reviewed rendering divergence caused by damaged source markup.

Coverage is many-to-many: one source assertion may lower to several rules, and
one helper may support several assertions. The build fails on an unledgered
normative assertion, a stale span digest, or an unreviewed waiver.

This is stronger than a whole-document textual round trip. A raw diff can force
a renderer to reproduce known mangling, while a declaration-only round trip can
miss omitted requirements. The correct test combines assertion coverage,
source-span freshness, structural equation rendering, and a reviewed divergence
baseline.

### 3.2 Interpretations are entities

The standard uses guards, local bindings, conditional results, pattern
disjunction, and parameter side conditions beyond the constructs explicitly
described in its equation-language clause. These are not harmless parser
details. AFSpec shall include an `interpretation` declaration containing:

- The source assertion it interprets.
- The ambiguity or missing rule.
- The adopted reading.
- Rejected alternatives and their consequences.
- Approval state and revision history.

`aifspec report --interpretations` produces the complete working-group review
list. Normative semantics may depend on an approved interpretation, but the
dependency remains visible in the IR and knowledge graph.

An operation whose meaning is delegated to another standard is instead an
`external` declaration. It names and pins that dependency and states its typed
contract. It is not disguised as an unexplained primitive.

## 4. CoreSpec: the semantic kernel

CoreSpec should contain only what is necessary to state the denotation:

- Closed sums and products, exact integers and rationals, mathematical reals,
  and `nan`, `neg_inf`, and `pos_inf`.
- Refinement-carrying format values and indexed `Code<f>` and `Value<f>`.
- Immutable bindings, typed calls, conditionals, and finite collections.
- Ordered case lists with patterns, Boolean guards, and results.
- Total and explicitly partial mappings.
- Primitive and external references with contracts.
- Source assertion IDs and normative status on every semantic node.

First-match behavior is a fold over the ordered case list: evaluate each
pattern and guard in source order and return the first result. Case order is
therefore part of canonicalization and the semantic digest. Overlap is legal but
must be acknowledged; proven unreachable rules are errors. If overlap or
exhaustiveness lies outside the checker’s decidable fragment, it becomes a
proof obligation rather than an assumption.

The denotation preserves the two important sorts:

```text
Value<f> --decode{f}--> Datum --omega operation--> Datum
                                           |
                                           v
                             project{result_format, projection}
                                           |
                                           v
                                    Value<result_format>
```

`Datum` is the closed extended-real domain and contains neither encoded negative
zero nor NaN payloads. Encoding distinctions remain in `Value<f>`. Arithmetic
on `Code<f>` produces an integer and must pass through a checked constructor
before becoming another code point.

### 4.1 Formalization without generated-semantics drift

Do not generate a fresh, bespoke Lean implementation of every AFSpec operation
and then declare it authoritative. That places semantic trust in the generator.
Instead:

1. Define the CoreSpec syntax, typing judgment, and evaluator/denotation once in
   Lean.
2. Emit each checked package as CoreSpec data plus proof obligations.
3. Prove that well-typed packages denote mappings of their declared types.
4. Generate convenient named Lean definitions only as wrappers around the
   generic denotation.

This makes the Lean adapter shallow and the semantic module deep. Generator
errors remain possible, but canonical package hashes, data round trips, and a
second decoder can detect them; they cannot silently redefine the calculus.

## 5. Evidence is obligation-driven, not globally “executable”

The denotational document correctly distinguishes exact meaning from finite
evidence, but a declaration-wide `exact`/`algebraic`/`transcendental` label is
too coarse. An operation containing `log2` may need only
`floor(log2(abs(x)))` on a dyadic input, which is exactly decidable. Conversely,
an apparently algebraic expression may still require a difficult equality at a
rounding boundary.

The compiler should instead derive **evidence obligations** from each reachable
case path and each observation made of a value. It tracks both the value domain
and the required observation:

| Obligation | Preferred evidence |
|:--|:--|
| Integer/rational arithmetic and comparison | Normalization and exact evaluation |
| Algebraic equality or ordering | Minimal-polynomial/isolating-interval decision procedure |
| Analytic value separated from a rounding boundary | Directed rational or ball enclosure |
| Exact boundary or tie | Symbolic identity or dedicated boundary proof |
| Unsupported external meaning | Contract-specific evidence |

This path-sensitive analysis is more useful than classifying a whole call graph.
It can recognize special cases such as `exp(0) = 1`, keep an exact rational
projection exact, and request an enclosure only for the residual analytic case.

### 5.1 Certificate forms

Certificates are generated artifacts, never handwritten semantic sources. A
certificate entry contains the operand tuple, claimed result, path/case ID,
evidence kind, evidence payload, checker version, and semantic digest. The
payload is one of:

- An exact normalization trace.
- An algebraic witness and isolating interval.
- A directed enclosure plus a proof that the entire enclosure projects to the
  claimed result.
- A symbolic boundary proof selecting the correct tie rule.
- An external-contract witness.

Checking an enclosure by projecting its endpoints is valid only after a theorem
establishes monotonicity for that projection and interval. The certificate must
name that theorem or carry a stronger boundary-exclusion witness; endpoint
agreement alone is not accepted as folklore.

Every evidence job has exactly three top-level outcomes:

- **certified** — a small checker validated evidence for the claimed result;
- **refuted** — valid evidence establishes a different result;
- **unresolved** — the budget, supported theory, or external contract was
  insufficient.

Budget exhaustion is always unresolved. Soundness of accepted certificates is
separate from termination of certificate search.

### 5.2 What the reference evaluator means

The evaluator is an oracle only for obligations it decides exactly. Elsewhere
it is a candidate-result producer whose answer has no conformance force until a
certificate validates it. Approximate host arithmetic may guide interval
refinement but never enter canonical semantics or certify its own result.

For a required finite specialization, conformance is established by exhaustive
enumeration of operand tuples and a certified entry for each tuple, or by a
generic theorem covering them. Refuted and unresolved counts are always
reported. A specification package may be internally valid while its conformance
evidence is incomplete; release policy decides which artifacts require complete
evidence.

## 6. Derived products and the knowledge graph

Julia, Markdown, RDF, tables, and reports are adapters over `CheckedSpec`.
Target mappings may rename the standard’s `Binary` format family to Julia
`BinaryFormat` and `Value<Binary(...)>` to Julia `Binary`, but cannot alter
types, rules, order, or provenance.

The knowledge graph is derived rather than authoritative. It contains nodes for
document revisions, assertions, declarations, rule cases, interpretations,
externals, requirements, evidence jobs, certificates, and generated artifacts.
Edges record `models`, `derivedFrom`, `uses`, `calls`, `precedes`, `requires`,
`interprets`, `supersedes`, `certifies`, and `refutes`. RDF named graphs preserve
revision context; PROV-O records derivation; SHACL validates graph shape.

Normative dependencies on informative notes are rejected. Informative material
may explain or cite normative entities but cannot define them.

## 7. Trust and reproducibility

Publish the trusted computing base rather than implying that generation removes
trust. It includes:

- The AFSpec parser, resolver, type checker, and lowering to CoreSpec.
- CoreSpec’s formal denotation and the Lean kernel used to check it.
- Primitive and external contracts.
- The certificate checker and any theorem library it invokes.
- Canonicalization and digest implementations.

Reduce this base with independent checks: formatter idempotence, canonical JSON
round trips, a second CoreSpec decoder, proof-kernel checking, exhaustive narrow
format comparison, and cross-adapter semantic-digest assertions.

Every artifact carries a source digest, semantic digest, language version,
source revision, generator/checker version, and evidence-policy digest. A
semantic digest identifies meaning; it is not proof of fidelity or correctness.
The transcription ledger and checked evidence supply those separate claims.

## 8. Review of the combined design

The initial synthesis needed six corrections.

**A DSL plus generated Lean was still two semantic implementations.** The fix
is CoreSpec data interpreted by one mechanized denotation, with generated names
as wrappers rather than independent definitions.

**A declaration-wide effectivity label lost path and observation information.**
The fix is obligation-driven, path-sensitive evidence planning. Classification
is derived and diagnostic; evidence obligations are the enforceable output.

**Intervals did not cover exact boundaries.** Positive-width enclosures cannot
separate a value lying exactly on a rounding boundary. The fix is heterogeneous
certificates, including symbolic boundary and algebraic witnesses.

**Endpoint agreement was being asked to prove too much.** It is sound only
under a proved monotonicity/boundary theorem for the projection in question.
The fix makes that theorem an explicit dependency of the certificate checker.

**Textual round-trip and clause coverage were both too blunt.** The fix is an
assertion-level transcription ledger with structural rendering and reviewed
divergences.

**Unresolved proof work could either block all modeling or be hidden.** The fix
is maturity gates: a package can be parsed, checked, denoted, rendered, or
conformance-certified at distinct levels. Each artifact states its attained
level; release policy may demand a higher one.

## 9. Implementation sequence

### Phase 1: establish the semantic seam

Implement AFSpec parsing, typed lowering, canonical CoreSpec, diagnostics,
digests, and the transcription ledger. Model one format, decode, rounding,
projection, one ordered arithmetic operation, and one transcendental operation.
Define CoreSpec’s Lean denotation at the same time; do not postpone semantics
until after generators exist.

### Phase 2: exercise every evidence path

Implement exact rational evaluation, one algebraic witness path, directed
enclosures, boundary certificates, and three-outcome reporting. The pilot shall
include ordinary, special-value, exact-tie, and non-boundary transcendental
cases. `Exp` on a required eight-bit format is a suitable small enumeration but
must include its exact `exp(0)` path rather than treating the family uniformly.

### Phase 3: conformance and adapters

Model required specializations and modalities. Generate Julia tests before
implementation methods, then Markdown and RDF. Require all adapters to embed
and verify the same semantic digest.

### Phase 4: broaden the corpus

Add conversion, saturation, remaining scalar operations, block operations,
external IEEE 754 contracts, and stochastic parameters. Extend AFSpec syntax
only when a real clause cannot lower clearly to existing CoreSpec forms.

### Phase 5: authority migration

After reviewed coverage, structural rendering, evidence checks, and semantic
equivalence with the current implementation, make AFSpec authoritative as the
editable model. Preserve each pinned source revision and its ledger rather than
rewriting history.

## 10. Acceptance criteria

The better approach is ready for authoritative use when:

- The AFSpec grammar and parser share one grammar source.
- Every surface construct has a specified lowering to CoreSpec.
- CoreSpec typing and denotation are defined and checked in Lean.
- Every normative source assertion is modelled, interpreted, externally pinned,
  or explicitly waived in a reviewed ledger.
- Source-span digests and reviewed rendering divergences are current.
- Ordered cases are exhaustive; overlaps are acknowledged; unreachable cases
  are rejected or explicitly demonstrated as source defects.
- Evidence planning is path-sensitive and produces inspectable obligations.
- Every required finite specialization is generically proved or has a certified
  entry for every operand tuple; refuted and unresolved counts are zero at the
  conformance-release gate.
- Certificate checking is independent of approximate result production.
- Canonical output and digests are deterministic across supported platforms.
- Julia naming changes remain confined to the target adapter.
- Generated Lean compiles, RDF satisfies SHACL, Markdown passes structural
  rendering checks, and CI detects every stale artifact.

The central rule is simple: **author once, lower once, define meaning once, and
never confuse a computed candidate with checked evidence.**
