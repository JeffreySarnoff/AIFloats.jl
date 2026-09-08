# Plan for an AI-readable P3109 knowledge repository

**Status:** reviewed implementation plan. This is not an IEEE document and does
not change the authority of the designated P3109 source revision.

**Sources used:** [bestcodex.md](bestcodex.md) and
[IEEE_D1.md](IEEE_D1.md), exclusively. The former supplies the verified
AFSpec/CoreSpec/evidence architecture; the latter supplies the actual knowledge
shapes, terminology, operations, requirements, and informative material the
repository must preserve.

## 1. Outcome

Build a versioned knowledge repository in which an AI can reliably:

- Resolve a P3109 term, format, operation, specialization, clause, or
  requirement to a stable identity.
- Retrieve a compact explanation without losing normative status or source
  provenance.
- Obtain the complete ordered semantics and dependencies needed to implement an
  operation.
- Determine which specializations a conforming implementation shall provide.
- Distinguish exact definitions, approximate implementations, informative
  recommendations, interpretations, external dependencies, and unresolved
  evidence.
- Compare revisions without mistaking renamed or moved text for semantic
  change.
- Expand from a short answer to full formal meaning and checked evidence without
  switching to a different source of truth.

The repository shall have one editable semantic model, AFSpec; one canonical
semantic interchange, CoreSpec; and generated AI-facing views. Search indexes,
knowledge graphs, summaries, context bundles, tables, and embeddings are
derived caches, never independent knowledge sources.

## 2. Design principles

### 2.1 Preserve the standard’s distinctions

The repository must make the following distinctions impossible to overlook:

- Normative `shall`, recommended `should`, permitted `may`, and factual `can`.
- A mathematical datum versus a format-indexed encoded floating-point value and
  its integer code point.
- A format family, a valid format instance, a format name, and an external
  named format (§3.2.1).
- An operation family, a parameterized specialization, and an implementation of
  that specialization.
- Public operations versus internal `omega` operations.
- Exact defined results versus `kappa`-approximate implementation results.
- Scalar, block, and scaled operations.
- Normative clauses versus informative notes, rationale, examples, value
  tables, operation groups, and bibliography.
- Defined semantics, approved interpretations, pinned external semantics,
  waivers, and unresolved obligations.

These are typed fields and graph relations, not labels inferred from prose at
query time.

### 2.2 Preserve order where order is meaning

Operation behavior is an ordered sequence of pattern-matching declarations, and
the first matching pattern defines the result. Rule order must therefore remain
in AFSpec, CoreSpec, entity records, context bundles, semantic digests, diffs,
and generated explanations. A graph edge alone is insufficient; every behavior
case also carries an integer position and stable case ID.

### 2.3 Separate knowledge from retrieval

AFSpec and its transcription ledger state what is known. CoreSpec states the
canonical meaning. A knowledge compiler produces representations optimized for
retrieval. The retrieval module may rank and omit material to meet a context
budget, but it may not rewrite equations, collapse modalities, reorder cases,
or present informative material as normative.

### 2.4 Make uncertainty explicit

AI-readable does not mean artificially complete. Every assertion has a
`knowledge_status` drawn from a closed vocabulary:

```text
defined
interpreted
external
waived
unresolved
```

Every conformance-evidence result has exactly one status:

```text
certified
refuted
unresolved
```

An AI-facing answer or context bundle must retain these values and the reasons
behind every non-`defined` or non-`certified` item.

### 2.5 Prefer deterministic retrieval before probabilistic retrieval

Stable-name lookup, aliases, full-text search, typed filters, and graph traversal
cover the standard’s principal use cases and are inspectable. Embeddings may be
added later as a recall aid, but they return candidate stable IDs only. Exact
hydration and provenance always come from the generated snapshot.

## 3. Knowledge model

### 3.1 Source and editorial entities

The source layer contains:

- `DocumentRevision`
- `Clause`
- `SourceAssertion`
- `SourceSpan`
- `Definition`
- `Notation`
- `Requirement`
- `Note`
- `Rationale`
- `Example`
- `Table`
- `OperationGroup`
- `Citation`
- `Interpretation`
- `ExternalContract`
- `Waiver`

A `SourceAssertion` is the unit of coverage. It is smaller than a clause and
large enough to carry one independently meaningful definition, equation,
constraint, requirement, or informative statement. Each assertion records its
modality, normative status, exact source span, digest, and containing clause.

### 3.2 Semantic entities

The semantic layer contains:

- `FormatFamily`, constrained `FormatInstance`, `FormatName`, and
  `ExternalFormat` (§3.2.1)
- `DatumType`, `CodeType`, `ValueType`, and `SequenceType`
- `Projection`, `RoundingMode`, and `SaturationMode`
- `OperationFamily` and `OperationSpecialization`
- `Parameter`, `Operand`, and `Result`
- `Behavior` and ordered `BehaviorCase`
- `PrimitiveContract` and `ExternalContractRef`
- `ConformanceSet` and `RequiredSpecialization`
- `ApproximationDeclaration`, including NaN/infinity matching, per-result and
  aggregate `kappa`, and any disjoint domain partition
- `EvidenceObligation`, `Certificate`, and `EvidenceOutcome`

The schema must directly represent the recurring operation definition shape in
the standard: Signature, Parameters, Operands, Result, ordered Behavior, and
optional Details. Details are not dumped into one text field; constraints,
local definitions, references, and genuinely explanatory prose are separated.

Block operations add a positive block size, a scale format and value, fixed
length element sequences, element formats, and indexed stochastic-rounding
inputs. Scaled operations are represented as derived block-size-one
specializations rather than duplicated operation definitions.

Operation families remain symbolic. Materialize a specialization record only
when the source names it, conformance requires it, an implementation declares
it, or evidence targets it. Other valid parameter combinations are normalized
query values resolved against the family. This avoids generating an unbounded
or needlessly large specialization catalog.

#### 3.2.1 Format family, format instance, format name, external format

These four are distinct kinds, not four spellings of one thing. Collapsing any
pair produces a claim that is well formed, plausible, and wrong.

**`FormatFamily`.** `Binary` is a schema parameterized by (K, P, Σ, Δ). It is
not a format: it has no datum set, no encoding, and no code points, so the
format-level operations of §4.14 are undefined on it. §3.2 names it — "Formats
defined in this document shall be named Binary{K, P, Σ, Δ}."

**`FormatInstance`.** `Binary(K, P, Σ, Δ)` **whose parameters satisfy §3.1**:
K greater than two; 0 < P < K when Σ is Signed; 0 < P ≤ K when Σ is Unsigned.
Only a satisfying tuple denotes a format, which §3.1 defines as a datum set
D_f together with a bijective encoding onto the code points 0 through 2^K − 1.

A violating tuple denotes nothing. It is a **non-format**, not an invalid
format, and the repository shall represent it as a resolution failure rather
than as an entity carrying a validity flag. There is no entity to attach the
flag to.

Derived attributes are functions of the instance and are never stored as
independent facts: the exponent bias is 2^{K−P−1} for signed and 2^{K−P} for
unsigned instances (§3.1), and the remaining §4.14 quantities follow from the
same four parameters.

§3.1 places no upper bound on K, so the family has **infinitely many** valid
instances. Materializing them is impossible rather than merely wasteful. The
rule already stated for operation specializations applies here unchanged:
materialize an instance record only when the source names it, conformance
requires it, an implementation declares it, or evidence targets it. Every other
instance is a normalized query value resolved against the family.

**`FormatName`.** The shortened notation of §3.2,
Binary⟨κ⟩p⟨ψ⟩⟨σ⟩⟨δ⟩ with σ in {s, u} and δ in {e, f} — for example
`Binary12p7se` and `Binary8p1uf`. A name is a **designator**, not a format.
Naming is a total injection from valid instances to names, so on the valid
domain name and instance determine each other and either resolves to the other.
A well-formed name whose parameters violate §3.1, such as `Binary8p8se`,
resolves to nothing, exactly as the corresponding tuple does.

Identity is carried by the canonical parameter tuple, never by the name string.
The name is an alias record pointing at the instance ID, on the same footing as
the target-language aliases of §3.4.

**`ExternalFormat`.** `binary64`, `binary32`, `binary16`, and `BFloat16` are
named formats used by §4.5's F_X, §4.8, and §4.9. They are **not** instances of
the `Binary` family, and the standard's own table proves it. §4.14 gives the
family bias as 2^{K−P−1} for signed formats and states each external format's
bias directly:

| Named format | K | P | family 2^{K−P−1} | §4.14 `ExponentBiasOf` |
|:--|--:|--:|--:|--:|
| binary64 | 64 | 53 | 1024 | **1023** |
| binary32 | 32 | 24 | 128 | **127** |
| binary16 | 16 | 11 | 16 | **15** |
| BFloat16 | 16 | 8 | 128 | **127** |

Each differs by exactly one, so there is no tuple for which an external format
equals `Binary(K, P, Signed, Extended)`. Their datum sets differ as well: §3.1
NOTE 1 gives family formats a single NaN and no negative zero, whereas §4.8's
`omegaDecodeExternal` maps "Any NaN" to NaN and −0 to 0 — collapsing
distinctions the external encoding carries. Their meaning is delegated, since
§4.8 defines external decoding and encoding by reference to another standard.

An `ExternalFormat` therefore carries an `ExternalContractRef` with a pinned
citation, not a parameter tuple, and it never acquires a `FormatInstance` ID.
§4.14's row values for these formats are **quoted table facts**, not derived
ones, and shall be recorded with that provenance.

### 3.3 Essential relations

At minimum, the graph shall represent:

```text
containsAssertion    models              definedBy
hasParameter         hasOperand          hasResult
hasBehavior          hasCase             precedesCase
specializes          calls               uses
decodesWith          projectsWith        encodesWith
constrains           requires            groupedAs
explainedBy          exemplifiedBy       cites
interprets           dependsOnExternal   waives
createsObligation    certifiedBy         refutedBy
supersedes           generatedFrom
```

Every edge is directed and typed. Derived inverse edges may be materialized for
fast traversal but are not authored separately.

### 3.4 Stable identity and aliases

Stable IDs are semantic and revision-aware without incorporating filenames,
page numbers, or target-language spellings. Human names and aliases are indexed
separately. For example, the P3109 format family remains `Binary`; a Julia
adapter may call its type `BinaryFormat` and the corresponding encoded value
representation `Binary`, but those aliases do not change the standard entity.

Every ID resolves within an explicit snapshot. Cross-revision identity is
expressed with `supersedes`, `splitFrom`, or `mergedFrom`; it is never guessed
from spelling alone.

## 4. Repository layout

Use a small authored area and a fully generated snapshot area:

```text
knowledge/
  source/
    p3109-d1-2026-09-07/
      IEEE_D1.md
      source-manifest.json
      assertions.afledger
      rendering-divergences.afledger
  spec/
    p3109/
      module.afspec
      vocabulary.afspec
      formats.afspec
      projection.afspec
      internal-functions.afspec
      scalar-operations.afspec
      block-operations.afspec
      conformance.afspec
      informative.afspec
      interpretations.afspec
      externals.afspec
  policy/
    evidence.toml
    context.toml
  schema/
    afspec-version.txt
    corespec-version.txt

generated/
  knowledge/
    <semantic-digest>/
      manifest.json
      corespec.json
      entities.jsonl
      assertions.jsonl
      edges.jsonl
      names.json
      search.sqlite
      graph.ttl
      cards/
      packs/
      evidence/
      reports/
      rendered/

src/
  knowledge/
    compiler.jl
    retrieval.jl
    context.jl
    validation.jl

test/
  knowledge/
    fixtures/
    golden/
    queries/
```

Only `knowledge/source`, `knowledge/spec`, `knowledge/policy`, and schema version
files are edited to change knowledge. Tool implementations and tests live under
`src/knowledge` and `test/knowledge`; they cannot supply semantic content.
Everything under `generated/knowledge` begins with or is covered by a
generated-artifact notice.

`manifest.json` is the single entry point for tools and agents. It identifies
the snapshot, all digests and versions, maturity gate, artifact paths, available
interfaces, and counts by entity, normative status, knowledge status, and
evidence outcome.

The source snapshot may initially be copied from the designated document rather
than moved. Its manifest records the original logical path and byte digest so
there is no ambiguity about which text was transcribed.

## 5. AI-facing representations

### 5.1 Entity records

`entities.jsonl` contains one canonical retrieval record per stable entity. A
record includes:

```json
{
  "id": "p3109.operation.Log",
  "kind": "OperationFamily",
  "name": "Log",
  "aliases": [],
  "normative_status": "normative",
  "knowledge_status": "defined",
  "summary": "Natural logarithm followed by projection to the result format.",
  "source_assertions": ["p3109.d1.4.10.9.log"],
  "parameters": [],
  "operands": [],
  "results": [],
  "ordered_case_ids": [],
  "direct_dependency_ids": [],
  "conformance_requirement_ids": [],
  "interpretation_ids": [],
  "informative_ids": [],
  "evidence_status": null,
  "semantic_digest": "..."
}
```

The example shows shape, not complete Log content. Generated summaries are
structural: they are assembled from checked fields and reviewed prose, not
invented by a language model. Full expressions live as typed CoreSpec nodes and
as deterministic human-readable renderings.

JSONL permits streaming, line-addressable inspection, and simple text tools.
SQLite provides fast full-text and relational lookup from the same records.
Both carry the same snapshot digest and are checked for equivalent IDs and
relations. JSONL, the manifest, and cards form the minimum portable snapshot;
SQLite, RDF, embeddings, and precomputed packs are optional, deletable indexes.

### 5.2 Knowledge cards

A knowledge card is a compact Markdown and JSON view of one entity. It contains,
in this order:

1. Stable ID, kind, name, and status.
2. One-paragraph structural summary.
3. Typed signature or defining statement.
4. Ordered behavior cases, when applicable.
5. Direct semantic dependencies.
6. Applicable conformance requirements.
7. Interpretations, external dependencies, and open obligations.
8. Source assertions with clause and span references.
9. Links to informative rationale and examples, clearly marked informative.

Cards target 400–900 tokens. A card that cannot fit shall link to separately
addressable sections rather than silently omit cases or requirements.

### 5.3 Task context packs

A context pack is a deterministic, bounded closure around one or more entities.
It has a machine-readable preamble containing the query, purpose, snapshot and
semantic digests, included IDs, omitted IDs, truncation reasons, and token/byte
estimates.

Supported purposes initially are:

- `define` — definition, notation, direct source assertions, and status.
- `explain` — `define` plus informative rationale and examples.
- `implement` — typed signature, ordered cases, called operations, format and
  projection dependencies, edge cases, and relevant interpretations.
- `verify` — `implement` plus CoreSpec nodes, proof and evidence obligations,
  certificates, and external contracts.
- `conformance` — required specialization rules, format sets, projection,
  approximation declarations, evidence outcomes, and query names.
- `revise` — old and new assertions, semantic diff, affected dependents, stale
  interpretations, and rendering divergences.

The default budget is 12,000 tokens with a caller-supplied override. The packer
reserves 10% for its manifest and omission report. It never silently truncates
an ordered case list. If an indivisible behavior cannot fit, the result is
`requires_followup` and supplies deterministic continuation parts split only at
case boundaries. Every part carries the complete case count, covered position
range, and shared behavior digest; no part by itself is labelled complete.

Purpose-specific traversal prevents dependency explosion. `implement` follows
semantic calls, format/projection dependencies, and normative constraints, but
does not pull the bibliography or unrelated rationale. `explain` may follow
informative edges but labels them. All traversals are cycle-safe and have
explicit depth and item limits.

### 5.4 Exact source and semantic views

An AI can always expand a card or pack to:

- The exact source span from `IEEE_D1.md`.
- The AFSpec declaration.
- Canonical CoreSpec JSON.
- The formal denotation reference.
- Evidence and conformance reports.

This progressive disclosure is essential: compact views optimize routine use,
while exact views make every consequential claim inspectable.

## 6. Retrieval module

Provide one deep retrieval module with four operations:

```text
resolve(query, snapshot) -> Resolution
get(ids, view, snapshot) -> KnowledgeBundle
context(ids, purpose, budget, snapshot) -> ContextBundle
search(query, filters, limit, snapshot) -> SearchResults
```

`resolve` handles stable IDs, exact standard names, known aliases, clause IDs,
and fully specified specializations. Ambiguity is returned as ranked candidates,
never resolved silently.

`get` returns exact requested records without graph expansion. `context` applies
the declared purpose policy and produces a deterministic dependency closure.
`search` performs lexical and typed-field search; optional semantic search may
only add candidate IDs before canonical hydration.

The command-line adapter is intentionally thin:

```text
p3109-know resolve Log
p3109-know get p3109.operation.Log --view card
p3109-know context p3109.operation.Log --purpose implement --budget 12000
p3109-know search "rounding tie" --kind BehaviorCase --status normative
p3109-know context p3109.requirement.required_operations --purpose conformance
p3109-know diff <old-snapshot> <new-snapshot> --impact
p3109-know check <snapshot>
```

All commands default to JSON on standard output and may render Markdown with an
explicit option. Diagnostics go to standard error and use stable codes. No
command fetches from the network or mutates the authored corpus.

## 7. Building knowledge safely

The knowledge compiler performs these steps in order:

1. Verify the pinned source manifest and source-span digests.
2. Parse AFSpec and the transcription ledger.
3. Resolve names, types, stable IDs, modalities, and source assertions.
4. Lower AFSpec once to typed CoreSpec.
5. Check format refinements and ordered rule semantics.
6. Derive dependency edges and path-specific evidence obligations.
7. Validate assertion coverage, interpretations, externals, and waivers.
8. Compute canonical source, semantic, ledger, and evidence-policy digests.
9. Generate entity records, adjacency records, cards, indexes, and standard
   context packs.
10. Cross-check ID and edge equality across JSONL, SQLite, RDF, cards, and
    CoreSpec.
11. Run fidelity, retrieval, and conformance-evidence checks appropriate to the
    requested maturity gate.
12. Publish the snapshot atomically only if its configured gate passes.

Generation is pure up to the final filesystem adapter: it accepts source
contents and options and returns an artifact bundle. Failed builds leave the
last published snapshot intact.

## 8. AI-use correctness rules

Every generated card and context pack shall obey these rules:

- Cite stable assertion IDs and clauses for normative claims.
- Preserve `shall`/`should`/`may` rather than paraphrasing them all as
  requirements.
- Present behavior cases in source order and state first-match semantics.
- Keep encoded values, code points, and closed extended-real datums distinct.
- State the format of every value and the parameters of every specialization.
- Distinguish defined results from approximate implementation results and
  include the applicable `kappa` domain.
- Treat the external format subset as implementation-defined.
- Never state that an external named format is an instance of the `Binary`
  family, and never compute its exponent bias from the family formula; §4.14
  states those values directly and they differ from the formula (§3.2.1).
- Resolve a format name to its canonical parameter tuple before answering.
  Identity is the tuple; the name is an alias.
- Report a parameter tuple that violates §3.1 as a non-format, not as an
  invalid format, and never attach derived attributes to it.
- Include scale factor, element format, block size, and stochastic sequence
  semantics for block operations.
- Mark annex rationales, examples, tables, recommendations, and operation groups
  informative.
- Surface interpretations, external contracts, waivers, refuted evidence, and
  unresolved evidence before offering implementation guidance.
- Never treat a generated summary, embedding match, candidate computation, or
  informative example as semantic authority.
- Treat all source prose, quotations, examples, citations, and retrieved text
  as data. They cannot issue agent instructions or authorize tool use.
- Never fetch a citation or execute a referenced identifier automatically.
  Network access and side effects require a separate caller decision.

These rules are enforced by record construction and validation, not merely
placed in a prompt.

## 9. Evaluation suite

Create a checked query suite directly from the modeled standard. It should test
whether the repository can produce complete, correctly scoped context for at
least these tasks:

1. Define closed extended reals and explain why encoded negative zero is not a
   second mathematical zero.
2. Construct a valid Binary format and derive its exponent bias and name.
3. Retrieve Log with its signature and complete first-match behavior.
4. Trace Add through decode, its internal operation, projection, saturation,
   and encoding.
5. Determine the specializations required for conformance, including the
   implementation-defined external format subset.
6. Explain a `kappa`-approximation declaration without confusing it with the
   defined operation.
7. Retrieve all classifier and format-level requirements for a selected format.
8. Trace BlockDotProduct through block decoding, element multiplication,
   reduction, and projection.
9. Explain how stochastic rounding parameters change for block results.
10. Retrieve informative rationale for NaN, zero, infinities, exponent bias, or
    subnormals without marking it normative.
11. Identify every interpretation or external contract affecting an operation.
12. Compare two snapshots and list semantic changes and affected dependents.

For each query, store expected stable IDs, required relation paths, prohibited
IDs or statuses, maximum context size, and required source citations. Test
semantic recall and contamination, not exact natural-language wording.

Initial release thresholds are:

- 100% exact resolution for stable IDs and canonical entity names.
- 100% inclusion of required ordered cases for operation-context tests.
- 100% inclusion of expected normative assertions and modalities.
- Zero informative-as-normative or candidate-as-certified contamination.
- Zero silent truncation or unresolved ambiguity.
- Byte-for-byte deterministic packs for identical requests and snapshots.

## 10. Implementation phases

### Phase 0: freeze contracts

Define the stable-ID grammar, source assertion schema, CoreSpec schema, knowledge
record schema, retrieval interface, context purposes, digest framing, and
diagnostic codes. Write golden examples before implementing storage.

Exit criterion: the Log example can be represented end to end on paper without
an untyped escape field.

### Phase 1: build a narrow vertical slice

Pin the current `IEEE_D1.md` revision and inventory only the assertions needed
for:

- word modalities and core terminology;
- `Binary8p4se` and its encoding;
- projection and internal decode/project/encode;
- Add and Log;
- the required-specialization rules relevant to those operations;
- BlockDotProduct;
- the informative NaN rationale; and
- the approximate Exp example.

Author the corresponding AFSpec, lower it to CoreSpec, and generate entity
records, cards, an adjacency index, and five purpose-specific context packs.
Do not start with the whole standard.

Exit criterion: the evaluation suite passes for the modeled slice, and every
answer can expand to source, AFSpec, and CoreSpec.

### Phase 2: implement retrieval and revision behavior

Implement the four-operation retrieval module, JSON CLI, SQLite index, semantic
diff, impact traversal, and atomic snapshot publication. Test ambiguous names,
cycles, corrupt indexes, stale digests, over-budget requests, and incomplete
snapshots.

Exit criterion: deleting the retrieval module would force its deterministic
closure, ranking, budgeting, and status-preservation logic into every caller.
This confirms that the module has useful depth.

### Phase 3: establish formal meaning and evidence

Define the generic CoreSpec denotation in Lean. Add exact evaluation,
path-sensitive evidence planning, directed enclosures, exact-boundary evidence,
and the independent certificate checker. Include an ordinary exact result, a
special value, a rounding tie, `exp(0)`, and a non-boundary transcendental case.

Exit criterion: candidate computation cannot produce `certified` without a
checker-validated certificate tied to the semantic digest.

### Phase 4: expand by semantic dependency

Expand in dependency order:

1. All definitions, notation, formats, and projection modes.
2. Internal decode, round, saturate, encode, and projection functions.
3. Scalar arithmetic, extrema, comparisons, classifiers, and format-level
   operations.
4. Conformance and approximation declarations.
5. Block decoding/projection, conversion, reductions, elementwise operations,
   and scaled derivations.
6. Informative rationales, value tables, examples, accuracy recommendations,
   groups, and citations.

At each increment, regenerate the snapshot and extend the query suite. Expansion
follows dependencies rather than document page order so every published entity
has usable context.

### Phase 5: optimize AI use

Measure pack size, retrieval latency, required-ID recall, contamination, and
redundant-token rate. Add precomputed high-frequency packs and, only if lexical
and graph retrieval show a measured recall gap, an optional embedding index.

Exit criterion: optimization changes neither included mandatory IDs nor any
semantic digest, and every cache can be deleted and deterministically rebuilt.

### Phase 6: make the model authoritative

After the `faithful` gate passes for the complete assertion inventory and the
configured formal/evidence gates pass, make AFSpec authoritative as the editable
model. Generate the human reference, implementation artifacts, conformance
reports, and AI snapshot from the same CoreSpec package.

## 11. First review: clarity, simplicity, specificity, effectiveness, correctness

The initial plan was reviewed against the requested qualities. The following
changes are incorporated above.

### Clarity

**Problem:** “knowledge repository” could mean a document collection, graph,
vector database, formal model, or all four.

**Improvement:** the plan now names one semantic source, one canonical form, and
three generated retrieval forms. It defines the exact role of JSONL, SQLite,
RDF, cards, and context packs.

### Simplicity

**Problem:** exposing every generator and store directly would create several
shallow interfaces and force callers to understand storage details.

**Improvement:** callers see four retrieval operations and one manifest. SQLite,
JSONL, graph traversal, ranking, token budgeting, and fallback behavior stay
inside one deep module. Embeddings are deferred until measured need exists.

### Specificity

**Problem:** “make it AI-readable” was not testable.

**Improvement:** the plan specifies record fields, context purposes, a default
budget, traversal behavior, failure modes, twelve evaluation tasks, and numeric
release thresholds.

### Effectiveness

**Problem:** fixed chunks of the large Markdown document would separate
operations from called internal functions, projection rules, conformance
requirements, or rationale.

**Improvement:** entity cards and purpose-specific graph closures use semantic
IDs and typed edges. Progressive disclosure provides compact default context
without losing access to exact source and CoreSpec.

### Correctness

**Problem:** summaries and probabilistic retrieval could erase first-match
order, modality, format indexing, approximation domains, or
normative/informative status.

**Improvement:** these properties are mandatory typed fields, validated across
all views. The correctness rules explicitly cover the distinctive scalar,
conformance, approximation, block, scaled, and informative structures in
`IEEE_D1.md`.

## 12. Second review: realizability

The improved plan was reviewed once more for whether a small team can actually
build it.

### Finding 1: full transcription is too large for a first milestone

The standard contains terminology, formats, projection, numerous scalar
operation families, conformance matrices, block schemas, scaled derivations,
and extensive informative annexes. Attempting all of them before testing the
retrieval interface would delay feedback and magnify schema mistakes.

**Resolution:** Phase 1 is a narrow but representative vertical slice spanning
every knowledge status and the scalar/block/conformance seams.

### Finding 2: a formal proof stack is not required to test AI usability

Waiting for complete Lean semantics and certificate machinery would block cards,
retrieval, provenance, and context evaluation.

**Resolution:** the schema and CoreSpec seam are fixed in Phase 0, the AI slice
is exercised in Phase 1, and formal meaning/evidence follows in Phase 3. Until
then snapshots cannot claim the `denoted` or `certified` maturity gates.

### Finding 3: maintaining JSONL, SQLite, RDF, cards, and packs looks duplicative

It would be duplicative if any were editable or implemented its own semantics.

**Resolution:** canonical CoreSpec and entity records generate all stores in one
pass. Cross-store ID and edge equality is checked. SQLite and precomputed packs
can be postponed or deleted without losing knowledge.

### Finding 4: token counts vary by model

A hard token limit is not portable across AI systems.

**Resolution:** `context` accepts a named tokenizer or byte budget, records the
estimator used, reserves manifest space, and reports omissions. The 12,000-token
default is policy rather than schema.

### Finding 5: automatic source assertion extraction cannot establish coverage

The source has complex mathematics, multi-column material, and distinctions
whose meaning depends on context. An extractor can propose spans but cannot
certify that no normative assertion was missed.

**Resolution:** assertion inventories are reviewed artifacts. Automation may
suggest entries and detect changed spans, but the `faithful` gate requires human
approval of the inventory and waivers for the pinned revision.

### Finding 6: AI-written summaries could become an accidental second standard

Free-form generated explanations are useful but cannot be trusted as durable
knowledge.

**Resolution:** published card summaries are deterministic renderings or
reviewed prose with assertion provenance. Unreviewed AI output is session-local
or stored as a clearly non-authoritative proposal, never merged into entity
records automatically.

### Finding 7: exhaustive evidence can grow rapidly

Finite operand spaces are not necessarily small, especially for multi-operand
and block operations.

**Resolution:** evidence supports both generic theorems and enumerated
certificates, is generated only for configured conformance targets, and is
stored separately from ordinary retrieval records. AI context includes evidence
summaries by default and hydrates individual certificates on demand.

### Finding 8: an AI can mistake retrieved prose for instructions

Even a standards repository is an untrusted retrieval source from the agent’s
point of view. Mixing content with control text would make future imported
citations or examples capable of steering tools.

**Resolution:** manifests and context bundles place policy metadata in a fixed
envelope and source material in explicitly typed data fields. Retrieval never
executes content, follows links, or grants authority. The caller remains
responsible for deciding what actions are allowed.

The plan is realizable because the first useful artifact needs only the source
snapshot, reviewed ledger slice, AFSpec/CoreSpec data model, entity generator,
and retrieval module. Formal evidence, full-corpus coverage, RDF, embeddings,
and optimized precomputed packs are incremental capabilities behind stable
interfaces.

## 13. Definition of done

The AI knowledge repository is ready for routine use when:

- The manifest is sufficient for a new agent to discover the snapshot and
  retrieval interface without scanning the repository.
- Stable IDs and canonical names resolve exactly and ambiguous aliases remain
  explicit.
- Every modeled normative assertion has fresh provenance and a reviewed ledger
  disposition.
- Context packs preserve rule order, modality, types, approximation domains,
  knowledge status, and evidence status.
- The twelve-task evaluation suite meets the thresholds in §9.
- Every compact claim can expand to its exact source span, AFSpec declaration,
  and CoreSpec meaning.
- Generated stores contain identical entity and relation sets and matching
  digests.
- Identical requests against one snapshot produce byte-identical results.
- An incomplete, stale, ambiguous, over-budget, refuted, or unresolved result is
  visible in both machine-readable output and human rendering.
- No derived cache, summary, graph, or embedding is required to reconstruct the
  authoritative model.

The practical test is whether an AI can ask one precise question, receive the
smallest complete context for its purpose, and trace every consequential answer
back to ordered semantics and a source assertion without guessing.
