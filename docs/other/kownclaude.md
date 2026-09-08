# Plan for an AI-readable and efficiently usable P3109 knowledge repository

**Status:** reviewed implementation plan. This is not an IEEE document and does
not change the authority of the designated P3109 source revision.

**Sources used:** [bestclaude.md](bestclaude.md) and
[IEEE_D1.md](IEEE_D1.md), exclusively. `bestclaude.md` supplies the authored
AFSpec model, CoreSpec denotation, fidelity ledger, evidence discipline, and
maturity model. `IEEE_D1.md` supplies every domain entity, rule, requirement,
and informative relationship described here.

## 1. Goal

Create a repository that lets an AI obtain the smallest complete body of P3109
knowledge needed for a task while preserving:

- Exact source wording and provenance.
- Normative status and `shall`/`should`/`may`/`can` distinctions.
- Typed semantic meaning.
- The order of first-match behavior declarations.
- Dependencies through decode, internal operations, rounding, saturation,
  projection, and encoding.
- Conformance scope and approximation declarations.
- Informative rationale and examples without treating them as requirements.
- Interpretations, external dependencies, proof obligations, and evidence
  outcomes.
- Revision and maturity status.

“AI-readable” means that every consequential statement is addressable by stable
ID, available in a compact machine record and readable card, and expandable to
its exact source and formal meaning. “Efficiently usable” means that an AI need
not scan the complete standard, reconstruct dependency chains, or guess which
material is normative before answering a focused question.

## 2. Non-goals

The repository shall not:

- Make generated summaries, a graph database, a search index, or embeddings a
  source of semantic truth.
- Flatten the standard into undifferentiated text chunks.
- Treat a floating-point datum, encoded value, and integer code point as the
  same typed object.
- Reorder behavior cases for presentation or retrieval.
- Infer missing semantics silently from examples or informative annexes.
- Call approximate host arithmetic a conformance oracle.
- Claim that all finite specialization domains are practical to enumerate.
- Execute text retrieved from the standard or follow its citations
  automatically.

## 3. Core architecture

Use the layered design from `bestclaude.md`, with a generated **AI knowledge
snapshot** as another adapter over the canonical model:

```text
Pinned P3109 revision                 normative source
        |
        | reviewed assertion inventory and transcription ledger
        v
AFSpec corpus                         authoritative editable model
        |
        | parse, resolve, type-check, elaborate, analyze
        v
CoreSpec package                      canonical semantic form
        |----------------------|----------------------|
        v                      v                      v
Lean denotation          evidence machinery     AI knowledge compiler
one mechanized meaning   obligations/certificates      |
                                                       v
                                              immutable snapshot
                                              cards, records, graph,
                                              search, task bundles
```

Only AFSpec declarations alter semantic meaning. The assertion inventory and
ledger alter fidelity and review status. CoreSpec, proofs, certificates, AI
records, indexes, and bundles are generated.

The AI knowledge compiler is a deep module: its small interface hides entity
projection, dependency closure, relevance policy, budgeting, citation assembly,
completeness checking, and deterministic rendering. JSON, Markdown, SQLite,
RDF, and optional embedding indexes are adapters behind that seam.

## 4. What must be represented

### 4.1 Source knowledge

Represent these source objects explicitly:

- Document revision, clause, subclause, source span, and assertion.
- Definition, abbreviation, mathematical notation, and comment.
- Normative requirement with its exact modality.
- Informative note, rationale, example, table, operation group, and citation.
- Rendering divergence caused by damaged or flattened mathematical layout.
- Interpretation, external semantic dependency, and reviewed waiver.

The source assertion—not a fixed text chunk—is the unit of fidelity. One clause
can contain several assertions, and one AFSpec declaration can realize assertions
from several clauses. Every assertion records its source bytes, digest,
normative status, modality, and disposition in the transcription ledger.

### 4.2 Floating-point knowledge

Represent these typed semantic objects:

- The closed extended reals with one NaN, positive and negative infinity, one
  mathematical zero, and ordinary reals.
- A `Binary` format family with constrained bitwidth, precision, signedness, and
  domain parameters.
- Derived exponent bias, canonical form, normal/subnormal classification,
  trailing significand, datum set, value set, and encoding.
- `Datum`, `Code<f>`, and `Value<f>` as distinct types.
- Named format instances and aliases.
- Rounding modes, including stochastic variants and their random-bit
  constraints.
- Saturation modes and projection specifications.

The repository must preserve the standard’s use of a value as a code point
associated with a format while keeping its decoded datum distinct. A target
adapter may use different programming-language names; target aliases never
change semantic IDs.

### 4.3 Operation knowledge

Every operation family uses the recurring structure present in the standard:

```text
Signature
Parameters
Operands
Result or results
Ordered Behavior cases
Optional Details
```

Represent public operations, internal `omega` operations, format-level
operations, projection accessors, comparisons, classifiers, and next-value
operations. Each behavior case has a stable ID, source position, patterns,
guard, result expression, local bindings, direct calls, and interpretation
dependencies.

First-match order is semantic. Every representation stores both the ordered
case array and explicit `precedes` relations. A compact summary may not replace
or reorder the full array.

### 4.4 Conformance and approximation knowledge

Represent:

- Required format sets, including the implementation-chosen nonempty external
  format subset.
- Required operation families and quantified specialization constraints.
- An implementation’s declared supplied specializations.
- The §4.6 agreement obligation for each supplied exact specialization.
- Approximate implementation identifiers, NaN and infinity matching, `kappa`
  values, per-result aggregation, and disjoint operand-domain partitions.
- Additional accuracy declarations and their status.
- Evidence obligations, proof strategy, certificate, outcome, and maturity.

Section 4.5 defines the minimum a conforming implementation must supply. Section
4.6 additionally requires agreement for every specialization it supplies,
including optional ones. The knowledge model must express both facts; evidence
scope cannot be reduced to the minimum set alone.

### 4.5 Block and scaled knowledge

Represent block size, scale-factor format and value, fixed-length element
sequences, element formats, block decoding, block projection, conversions,
reductions, dot products, and elementwise operation schemas. Indexed stochastic
random values and the derived projection for each result element are explicit.

Scaled operations are derivations from block-size-one operations. Store that
derivation rather than duplicating all scalar semantics under new names.

## 5. Knowledge object contract

Every generated object has a common envelope:

```json
{
  "id": "p3109.operation.Log",
  "revision": "p3109-d1-2026-09-07",
  "kind": "OperationFamily",
  "name": "Log",
  "authority": "model",
  "normative_status": "normative",
  "modality": null,
  "knowledge_status": "defined",
  "maturity": "checked",
  "source_assertion_ids": [],
  "dependency_ids": [],
  "interpretation_ids": [],
  "external_contract_ids": [],
  "obligation_ids": [],
  "semantic_digest": "...",
  "payload": {}
}
```

The closed `knowledge_status` vocabulary is:

```text
defined | interpreted | external | waived | unresolved
```

The closed evidence outcome vocabulary is:

```text
certified | refuted | unresolved
```

Each object kind defines its payload schema. No generic “metadata” or
“additional properties” field may carry untyped semantics. Extensions require a
schema version and an impact report.

### 5.1 Three views of one object

Generate three views from the same object:

1. **Index row:** identity, kind, names, statuses, clause, and direct relations;
   intended for resolution and filtering.
2. **Knowledge card:** a concise Markdown/JSON explanation with signature,
   ordered cases or defining statement, direct dependencies, conformance links,
   interpretations, and citations.
3. **Full object:** complete CoreSpec projection, source assertions, proof and
   evidence links, and all typed relations.

The card is not an AI-written paraphrase. It is a deterministic rendering of
typed fields plus reviewed explanatory prose. Unreviewed generated explanation
may be returned in a session but cannot be published as repository knowledge.

### 5.2 Identity and specialization policy

Stable IDs do not contain filenames, page numbers, or target-language names.
Aliases resolve to stable IDs but do not replace them.

Keep generic operation families symbolic. Materialize a specialization only
when it is named by the standard, required by a conformance profile, declared by
an implementation, or targeted by evidence. Arbitrary valid specializations are
canonical query values, not pre-generated objects. This prevents combinatorial
growth while retaining exact resolution.

## 6. Snapshot layout

```text
knowledge/
  source/
    <revision>/
      IEEE_D1.md
      source-manifest.json
      assertions.afledger
      rendering-divergences.afledger
  model/
    p3109/
      vocabulary.afspec
      formats.afspec
      projection.afspec
      internal.afspec
      scalar.afspec
      block.afspec
      conformance.afspec
      informative.afspec
      interpretations.afspec
      externals.afspec
  policy/
    retrieval.toml
    evidence.toml
  schema/
    afspec-version.txt
    corespec-version.txt
    knowledge-version.txt

generated/
  knowledge/
    <revision>/<semantic-digest>/
      START.md
      manifest.json
      catalog.jsonl
      relations.jsonl
      core/corespec.json
      objects/
      cards/
      evidence/
      reports/
      bundles/
      indexes/

src/
  knowledge/
    compile.jl
    resolve.jl
    assemble.jl
    compare.jl
    validate.jl

test/
  knowledge/
    schema/
    golden/
    queries/
    revisions/
```

Knowledge changes are authored only under `knowledge/source`,
`knowledge/model`, and `knowledge/policy`. Tooling changes under `src/knowledge`
cannot inject semantic objects. Everything under `generated/knowledge` is
replaceable output.

`START.md` is a short human/AI entry point explaining authority, statuses,
retrieval order, and available snapshots. `manifest.json` is the machine entry
point. It includes all digests, schema versions, maturity, object and relation
counts, artifact locations, and validation results.

The minimum portable snapshot is `START.md`, `manifest.json`, `catalog.jsonl`,
`relations.jsonl`, `objects/`, and `cards/`. SQLite, RDF, embeddings, and
preassembled bundles are optional indexes that may be deleted and rebuilt.

## 7. Retrieval interface

Expose three essential operations:

```text
resolve(snapshot, query, filters) -> ResolutionSet
assemble(snapshot, request) -> KnowledgeBundle
compare(old_snapshot, new_snapshot, selector) -> ChangeBundle
```

`resolve` accepts a stable ID, canonical name, alias, clause, text query, or
specialization expression. It never chooses silently among ambiguous results.

`assemble` accepts resolved IDs, a task profile, context budget, relation depth,
and desired view. It hides dependency traversal, priority rules, cycle handling,
budgeting, pagination, and citation assembly.

`compare` reports assertion, semantic, status, maturity, evidence, and dependent
impact changes by stable ID rather than by filename or paragraph position.

The CLI adapter is direct:

```text
p3109-knowledge resolve "Log"
p3109-knowledge assemble p3109.operation.Log --for implement --budget 12000
p3109-knowledge assemble p3109.requirement.required --for conformance
p3109-knowledge assemble p3109.operation.BlockDotProduct --for explain
p3109-knowledge compare <old> <new> --impact p3109.operation.Exp
p3109-knowledge validate <snapshot>
```

Machine output defaults to JSON; Markdown is explicit. Diagnostics use stable
codes on standard error. Retrieval never changes authored or generated state.

## 8. Task-oriented context assembly

Initial task profiles are:

- `define`: definition, typed identity, notation, status, and source assertion.
- `explain`: `define` plus informative rationale and examples, visibly marked.
- `implement`: signature, formats, projection, complete ordered behavior,
  internal-call closure, special cases, interpretations, and external contracts.
- `conformance`: required and declared specializations, selected external format
  set, approximation declarations, query names, and evidence status.
- `verify`: CoreSpec, path assumptions, normalization steps, obligations,
  certificate types, licensing theorems, and outcomes.
- `revise`: assertion and semantic diffs, impacted dependents, stale ledger
  entries, maturity regressions, and rendering divergences.

Each profile defines mandatory relations and optional relations. Mandatory
content is selected before relevance ranking. For example, `implement` always
includes all behavior cases in original order and every directly called internal
operation; `explain` may add rationale but cannot displace normative content.

The default request budget is 12,000 tokens, with a byte budget and named
tokenizer also supported. Ten percent is reserved for the bundle manifest,
citations, and omission report. An indivisible behavior that exceeds the budget
returns `requires_followup` plus ordered continuation parts split only between
cases. Every part states the total case count, included position range, and
shared behavior digest.

Every bundle declares:

- `complete`, `requires_followup`, or `incomplete_source`;
- included, omitted, and continuation IDs;
- snapshot, semantic, ledger, and policy digests;
- statuses and maturity floor;
- budget estimator and actual size; and
- unresolved ambiguities, interpretations, externals, waivers, and evidence.

## 9. AI safety and epistemic discipline

The repository enforces these output invariants:

- Source text, examples, retrieved prose, and citations are typed data, never
  agent instructions or authorization for tool use.
- A citation is not fetched automatically.
- `shall`, `should`, `may`, and `can` retain distinct machine values and visible
  renderings.
- Informative notes, annexes, examples, value tables, accuracy recommendations,
  operation groups, and bibliography never appear as normative.
- Behavior cases remain ordered and first-match semantics is stated.
- Every value carries or resolves its format; datums and encodings remain
  distinct.
- Defined operation results are not confused with approximate implementation
  results or additional accuracy claims.
- The implementation-chosen external format set is never presented as globally
  fixed.
- Candidate computations, embeddings, and summaries cannot assert
  certification.
- Interpretations, external contracts, waivers, and unresolved items appear
  before implementation recommendations.

These are snapshot validation rules, not suggestions placed only in an agent
prompt.

## 10. Semantics and evidence available to AI

An AI often needs to know not just a result, but what justifies it. Each semantic
object therefore links to an evidence plan derived from:

```text
reachable case path
+ argument and intermediate domains
+ requested observation
+ bounded normalization result
= obligation set
```

Path reachability is conservatively over-approximated. An undecided path creates
obligations; it is never discarded as unreachable. Path analysis and expression
normalization remain distinct. Recognizing the terminal `e^X` clause at `X = 0`
as exactly one is a bounded symbolic-normalization result, not a separate Exp
behavior case.

The repository exposes a diagnostic domain class—dyadic, rational, algebraic,
transcendental, or external—but enforcement operates on the more precise
obligations. It also exposes the closure facts and normalizer rules used to
derive them because those facts are part of the trusted base.

Certificate payloads form a closed, versioned set:

- Exact normalization trace.
- Algebraic witness with isolating interval.
- Directed enclosure with the named theorem licensing projection over the
  interval.
- Symbolic boundary proof selecting the applicable tie rule.
- External-contract witness.

Adding a certificate form changes the trusted base and requires an impact
report. Certificate production and checking are separate modules. Production
may use approximate computation; the checker may not trust the candidate
producer.

Evidence has exactly three outcomes: certified, refuted, or unresolved. Budget
exhaustion is unresolved. Soundness of accepted evidence is independent of
whether evidence search is guaranteed to terminate.

### 10.1 Correct evidence scope

Do not equate “required by §4.5” with “small enough to enumerate.” Required
specializations involving 4- and 8-bit operands may be enumerable, while a
selected external format can make tuple enumeration impractical.

Evidence policy is therefore:

1. Every specialization an implementation declares as supplied receives the
   applicable §4.6 exact-agreement or §4.4 approximation obligation.
2. A conforming implementation must at least declare the §4.5-required set for
   its chosen external-format subset.
3. Small finite domains may use exhaustive tuple certificates.
4. Large scalar or block domains require a generic theorem, compositional proof,
   or reviewed partition whose union covers the declared domain.
5. Coverage counts and unresolved regions are explicit; “finite” alone never
   selects enumeration.

## 11. Build and validation pipeline

Build a snapshot in this order:

1. Verify the pinned source digest.
2. Generate a proposed assertion inventory from the source structure.
3. Require human review of that inventory against the authoritative rendering.
4. Validate assertion spans, byte digests, modalities, and ledger dispositions.
5. Compile AFSpec to typed canonical CoreSpec.
6. Check first-match order, typing, refinements, overlap acknowledgements,
   reachability, and exhaustiveness.
7. Derive dependencies, conservative evidence obligations, domain summaries,
   and bounded normalizations.
8. Compute source, semantic, ledger, retrieval-policy, and evidence-policy
   digests.
9. Generate objects, cards, forward and reverse relations, catalogs, reports,
   and optional indexes.
10. Cross-check identical IDs, relation sets, statuses, order, and digests in
    every representation.
11. Run AI retrieval evaluations and formal/evidence checks required by the
    target maturity gate.
12. Publish atomically, retaining the previously valid snapshot on failure.

Every artifact states one maturity level:

```text
parsed -> checked -> denoted -> faithful -> evaluated -> certified -> publishable
```

Consumers assert the minimum level they require. For an unchanged assertion,
maturity may not decrease in a later snapshot without a reviewed waiver. A
changed or new assertion may restart at a lower level, but the transition and
affected dependents are reported rather than hidden.

## 12. Evaluation suite

Use task tests whose expected results are stable IDs, relations, statuses, and
ordered cases rather than one preferred prose answer.

The initial suite shall ask the repository to:

1. Define datum, floating-point value, code point, format, operation, and
   specialization without conflating them.
2. Explain the four format parameters and derive the bias and short name of a
   concrete format.
3. Retrieve a complete operation schema with parameters, operands, result,
   behavior, and details.
4. Return Log’s behavior in exact first-match order and distinguish its explicit
   zero case from Exp’s terminal expression.
5. Trace Add through decode, internal addition, projection, rounding,
   saturation, and encoding.
6. Determine the §4.5 minimum operation set for a declared external-format
   choice.
7. Determine the §4.6 obligation for an additional supplied specialization.
8. Explain a `kappa` declaration, including NaN/infinity matching and a
   partitioned finite-result domain.
9. Retrieve classifiers, comparisons, format-level operations, and operation
   groups with correct status.
10. Trace BlockDotProduct through scale decoding, element multiplication,
    reduction, and projection.
11. Explain indexed stochastic rounding for a block result.
12. Retrieve the rationale for the single NaN, single zero, infinities, exponent
    bias, and subnormals without promoting rationale to requirement.
13. List every interpretation, external contract, and unresolved obligation
    affecting a selected operation.
14. Compare two snapshots and return changed assertions plus transitively
    affected semantic entities and evidence.

For every test, store required IDs and edges, forbidden statuses, maximum size,
completeness state, and required citations. Initial acceptance requires:

- Exact stable-ID and canonical-name resolution.
- All required behavior cases in correct order.
- All required normative assertions and modalities.
- No informative-as-normative, candidate-as-certified, or external-as-defined
  contamination.
- No silent ambiguity, truncation, waiver, maturity regression, or unresolved
  evidence.
- Byte-identical bundles for identical snapshot, request, and tokenizer policy.

## 13. Implementation phases

### Phase 0: fix the contracts

Specify stable IDs, assertion and ledger schemas, CoreSpec and knowledge-object
schemas, the three-operation retrieval interface, bundle completeness states,
digest framing, maturity values, normalizer bounds, and diagnostic codes.

Exit criterion: the Log definition, including ordered cases, can be represented
from source assertion through AI card with no untyped semantic escape.

### Phase 1: build a vertical knowledge slice

Pin the current source revision and review the assertions needed for terminology,
`Binary8p4se`, projection, decode/round/saturate/encode, Add, Log, Exp,
next-greater/next-less, relevant conformance rules, one approximation example,
BlockDotProduct, and one informative rationale.

Generate the minimum portable snapshot and implement `resolve` and `assemble`
for `define`, `explain`, `implement`, and `conformance` profiles.

Exit criterion: the relevant evaluation tests pass, and every compact result
expands to source assertions, AFSpec, and CoreSpec.

### Phase 2: establish semantics and evidence planning

Define CoreSpec syntax, typing, and one generic denotation in Lean. Implement
conservative path planning, the bounded expression normalizer, published closure
facts, and inspectable evidence obligations.

Exit criterion: no undecided reachable path is omitted, and `exp(0)` is
recognized through a declared normalizer rule rather than an invented behavior
case.

### Phase 3: establish evidence checking

Implement the closed certificate payload set and independent checker. Exercise
exact arithmetic, rational division, one algebraic result, an exact tie, a
non-boundary transcendental enclosure, and an external contract. Report all
three outcomes.

Exit criterion: candidate generation cannot assign `certified`, and every
accepted certificate identifies its checker, licensing theorem, semantic
digest, and covered domain.

### Phase 4: complete retrieval and revision support

Implement `compare`, reverse dependencies, impact analysis, optional SQLite and
RDF indexes, atomic publication, and the maturity ratchet. Add tokenizer-aware
budgets and continuation bundles.

Exit criterion: all derived indexes can be deleted and recreated byte for byte,
and revision impact is computed by stable ID.

### Phase 5: expand the standard by dependency

Expand formats and projection first; then internal functions; scalar arithmetic,
extrema, comparisons, classifiers, and meta operations; conformance and
approximation; block and scaled operations; finally informative annexes and
citations. Extend the query suite with each slice.

Exit criterion: every reviewed source assertion is represented, interpreted,
externally pinned, or waived, and every published entity has complete task
context for its supported profiles.

### Phase 6: optimize measured AI use

Measure lookup latency, bundle size, mandatory-ID recall, relation recall,
contamination, and redundant tokens. Preassemble only frequent bundles. Add an
embedding index only if deterministic name, lexical, and graph retrieval show a
measured recall gap.

Exit criterion: optimization changes no semantic selection rule, required ID,
status, case order, or digest, and every optimization remains a deletable cache.

## 14. First review and incorporated improvements

The initial plan was reviewed for clarity, simplicity, specificity,
effectiveness, and correctness.

### 14.1 Clarity

**Finding:** “knowledge,” “understanding,” “model,” and “index” could be read as
competing sources.

**Improvement:** the plan now defines three authorities and gives each generated
view one role. The common object envelope makes status and maturity visible in
every representation.

### 14.2 Simplicity

**Finding:** separate interfaces for cards, graph traversal, full-text search,
proof lookup, and context packing would expose storage mechanics.

**Improvement:** one deep retrieval module exposes only `resolve`, `assemble`,
and `compare`. Optional stores are adapters and deletable caches. Generic
specializations remain symbolic unless a concrete reason requires
materialization.

### 14.3 Specificity

**Finding:** “optimize for AI” was not measurable.

**Improvement:** the plan specifies object fields, task profiles, mandatory
relations, budget behavior, completeness states, fourteen query tests, and
explicit acceptance properties.

### 14.4 Effectiveness

**Finding:** fixed-size source chunks would separate an operation from its
internal calls, projection, conformance obligations, or rationale.

**Improvement:** bundles follow typed purpose-specific relations. Mandatory
semantic closure is selected before optional relevance ranking, with explicit
continuations when it cannot fit.

### 14.5 Correctness

**Finding:** two attractive simplifications were wrong. Required specializations
are not necessarily small enough to enumerate, and §4.6 is not limited to the
minimum set named by §4.5.

**Improvement:** the evidence policy now covers every specialization an
implementation declares and selects exhaustive, theorem-based, compositional,
or partitioned evidence by domain size and structure. It also preserves the
source’s modality, first-match order, typed value distinctions, external-format
choice, approximation rules, block semantics, and informative status.

## 15. Second review: realizability

The improved plan was reviewed again as an implementation proposal.

### 15.1 Assertion inventory bootstrap

Automatic extraction cannot prove completeness from mathematically complex or
damaged source text.

**Resolution:** extraction proposes assertions; a human reviews the inventory
for each pinned revision. Unreviewed inventory produces only an
`incomplete_source` snapshot and cannot attain `faithful` maturity.

### 15.2 Formalization latency

Waiting for all Lean definitions and evidence checkers would postpone useful AI
retrieval for too long.

**Resolution:** Phase 1 publishes an explicitly `checked` vertical slice; it
cannot imply denotation or conformance. Formal meaning and evidence advance the
same objects through later maturity gates without changing the retrieval
interface.

### 15.3 Evidence scale

External formats, multi-operand operations, and blocks can make enumeration
astronomical despite finite domains.

**Resolution:** evidence objects support generic theorems and domain partitions
as first-class coverage, with tuple certificates reserved for genuinely small
domains. Evidence is stored separately and summarized in ordinary bundles.

### 15.4 Conservative planning cost

Over-approximating undecidable path reachability may generate unnecessary
obligations.

**Resolution:** false-positive obligations may be discharged by a reachability
proof and cached by semantic digest. The planner is never permitted to remove an
obligation merely to meet a time or context budget.

### 15.5 Trusted-base growth

Closure facts, bounded normalization, and heterogeneous certificate checkers
can quietly enlarge the trusted base.

**Resolution:** each is closed and versioned. A change emits affected-object and
affected-certificate reports and invalidates dependent evidence. New certificate
forms and normalizer rules require explicit review.

### 15.6 Multiple generated representations

Maintaining cards, JSON, relations, SQLite, RDF, and bundles would be fragile if
they evolved independently.

**Resolution:** a single knowledge-object stream generates them in one build,
and validation compares IDs, edges, order, status, and digests across every
enabled adapter. The portable snapshot does not depend on optional stores.

### 15.7 Model-dependent token budgets

Token counts differ across AI systems, and an indivisible rule list can exceed a
budget.

**Resolution:** the caller specifies a tokenizer or byte budget. Bundles record
the estimator, reserve manifest space, and use explicit ordered continuations.
No partial bundle is labelled complete.

### 15.8 Maturity ratchet across changed revisions

A strict ratchet is inappropriate when the normative assertion itself changes.

**Resolution:** unchanged assertions may not regress without a reviewed waiver;
changed and new assertions may restart lower, but their transitions and
dependent impact are mandatory revision-report entries.

The design is realizable because Phase 1 needs only a reviewed source slice,
AFSpec/CoreSpec records, deterministic cards, relation traversal, and two
retrieval operations. Formal proofs, certificate checking, whole-document
coverage, optional indexes, and performance optimization deepen the same
interfaces incrementally.

## 16. Definition of done

The repository is ready for routine AI use when:

- A new agent can begin at `START.md`, locate a snapshot, and understand
  authority and status without scanning the repository.
- Stable IDs, canonical names, aliases, clauses, and declared specializations
  resolve deterministically; ambiguity is explicit.
- Every modeled assertion has fresh source provenance and a reviewed ledger
  disposition.
- Cards and bundles preserve types, modality, first-match order, conformance
  scope, approximation domains, interpretations, and evidence status.
- Mandatory dependencies are never displaced by relevance scoring or budget
  pressure.
- Every bundle reports completeness and provides deterministic continuation
  when necessary.
- Every semantic claim expands to source assertion, AFSpec declaration,
  CoreSpec object, and available evidence.
- The fourteen-task evaluation suite passes without status contamination or
  silent omission.
- Enabled representations contain identical IDs, relations, case order, and
  digests.
- Identical requests against one immutable snapshot produce identical bytes.
- Consumers cannot claim a maturity level higher than the snapshot provides,
  and unchanged assertions cannot regress silently.
- No generated card, index, graph, bundle, embedding, or certificate is needed
  to reconstruct the editable semantic model.

The decisive test is whether an AI can retrieve a compact answer, know exactly
what kind of claim it is, expand it to complete ordered semantics, and identify
both its source assertion and its evidence without guessing.
