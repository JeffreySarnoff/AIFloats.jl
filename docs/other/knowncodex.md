# An AI-usable knowledge repository for P3109

**Status:** design plan. Not an IEEE document. Changes nothing about the
authority of the pinned source revision.

**Sources:** this plan uses only [`bestcodex.md`](bestcodex.md) and
[`IEEE_D1.md`](IEEE_D1.md). Its architecture, obligations, gates and vocabulary
are `bestcodex.md`'s; its measurements and hazards are taken from `IEEE_D1.md`
directly.

## 1. The measurement that reframes the problem

Before designing retrieval, measure the corpus.

| Property | Value |
|:--|--:|
| `IEEE_D1.md` size | 3 069 lines / 155 982 bytes |
| Approximate tokens, whole file | **≈ 37 500** |
| Clause 4 (Operations) alone | ≈ 17 000 |
| Clause 4.10 (Arithmetic) alone | ≈ 5 800 |
| Clauses (`##`/`###`/`####`) | 84 |
| Signature/Behavior record pairs | 42 |
| Distinct operation names with a Signature | 48 |
| ω-clause lines | 373 |
| NOTEs | 38 |
| `shall` / `should` / `may` | 23 / 10 / 12 |

The entire normative source fits in a modern context window several times over.
**This is not a retrieval problem.** Chunking, embedding and similarity search
would add a lossy layer over a corpus that could simply be read whole.

The real failure mode is different, and §2 measures it: an agent reading this
file *directly* reads it **wrongly**, in ways that are systematic, silent, and
reproducible. So the repository's job is not to find text. It is to deliver
**normalized, addressable, order-preserving facts with verifiable provenance**,
and to make the ways an agent goes wrong impossible rather than merely
discouraged.

This inverts the usual priority. `bestcodex.md` §4 names four independent
obligations — fidelity, semantic preservation, behavioral evidence,
reproducibility. For an AI consumer, **fidelity is the whole product** and the
other three are what make fidelity checkable.

## 2. What defeats an AI reading `IEEE_D1.md` directly

Six hazards, each measured in the current file. Every one produces a confident
wrong answer, not an error.

**H1 — Intra-word emphasis breaks substring search. 627 lines (20% of the
file).** The transliteration interleaves markup inside tokens:
`*ω*Sqrt(*X*) if *X <* 0 → NaN`. An agent searching for `Sqrt(X) if X < 0`
finds nothing and concludes the guard does not exist. Searching for `ωSqrt`
finds nothing because the name is split by `*`.

**H2 — Hyphenation splits words across lines. 19 sites.** §4.1 NOTE 4 reads
`… are auto-` / `matically extracted …`. A search for "automatically extracted"
returns empty. A search for "Auxiliary operations are" succeeds. Which of those
an agent tries is luck.

**H3 — Two-column layout interleaves unrelated definitions.** §4.11.1 line 1666:
`*ω*Minimum(NaN, ∗) → NaN     *ω*Maximum(NaN, ∗) → NaN`. Minimum and Maximum are
different operations printed side by side. A line-oriented reader attributes
one's clauses to the other. Annex F has the same shape across four groups.

**H4 — First-match order is invisible in a fragment.** §4.3.2: *"the first
matching pattern in the order presented in this document defines the
behavior."* Retrieving clause 5 of an ordered list without clauses 1–4 yields a
confidently wrong answer. The lists are long: **32 clauses** in §4.10.6 (FMA),
24 in §4.10.7 (FAA), 19 in §4.10.4, 18 in §4.11.4.

**H5 — Three sorts look alike.** §4.1 and §3.1 distinguish a `Value<f>` (a code
point), a `Datum` (a closed extended real), and the code integer itself. §3.1
NOTE 2 warns that a real constant appearing in an operation definition means
`ωEncode_f` of it. An agent that flattens these produces answers that typecheck
in prose and are wrong.

**H6 — Non-effectivity is invisible.** §4.10.9 ends `ωExp(X) → e^X`; §4.7.4 then
decides by exact real comparison on `ν`. Nothing in the text says "you cannot
compute this." An agent will compute a float, round it, and report the result
as the standard's answer.

## 3. The repository

`bestcodex.md` §3's layers, with each layer's obligation to an AI consumer made
explicit.

```text
L0  pinned source revision            IEEE_D1.md + digest. Never the read path.
      |   normalization + assertion inventory
      v
L1  AFSpec corpus                     editable model; the human-authored layer
      |   parse, resolve, check, elaborate
      v
L2  canonical CoreSpec package        typed semantic interchange
      |
      +-- L3a  Lean denotation        meaning, defined once
      +-- L3b  evidence planner and certificate checker
      +-- L3c  exact-only evaluator
      +-- L3d  adapters  ->  **AI VIEW**  the agent's read surface
      |
      v
L4  conformance bundles and revision reports
```

The **AI view** is a new adapter under L3d, and the only thing an agent is
permitted to read. It is generated, never authored. Agents never read L0
directly, because §2 is what happens when they do.

Two rules follow from `bestcodex.md` §1 and hold for the AI view specifically:

- **Rule A (no second semantics).** The AI view is a *projection* of L2. It adds
  no fact that is not derivable from CoreSpec plus the ledger, exactly as
  `bestcodex.md` §10 says of the RDF graph: "a query adapter … not another
  semantics."
- **Rule B (no unlabelled claim).** Every fact carries its assertion ID, source
  span, digest, modality, and maturity gate. A fact without provenance is not
  emitted.

## 4. The unit of knowledge: the assertion record

`bestcodex.md` §4.1 makes the **assertion** the unit of fidelity. It is also the
right unit for an agent: smaller than a clause, individually addressable, and
carrying everything needed to use or refuse it.

```json
{
  "id": "p3109.4.10.9.exp.behavior.terminal",
  "revision": "ieee-p3109-d1-2026-09-07",
  "clause": "4.10.9", "kind": "omega_clause",
  "operation": "Exp", "case_index": 4, "case_count": 4,
  "order_critical": true,
  "text": "ωExp(X) → e^X",
  "normalized": {"pattern": ["real X"], "guard": null, "result": "exp(X)"},
  "sorts": {"X": "Datum", "result": "Datum"},
  "effectivity": {"class": "transcendental", "observation": "value",
                  "computable": false, "evidence": "enclosure|boundary"},
  "modality": "shall",
  "source": {"line": 1341, "span": [64211, 64240], "digest": "sha256:…"},
  "renders_from": ["p3109.4.10.9.exp.signature"],
  "requires": ["p3109.4.7.3.project", "p3109.4.7.2.decode"],
  "gate": "denoted"
}
```

Six fields exist purely to defeat §2:

| Field | Defeats |
|:--|:--|
| `text` + `normalized` | H1, H2 — markup and hyphenation removed once, correctly |
| `operation` | H3 — column position can never mis-assign a clause |
| `case_index` / `case_count` / `order_critical` | H4 — a fragment announces that it is one of N ordered cases |
| `sorts` | H5 — every name carries its sort |
| `effectivity` | H6 — the record states outright that it is not computable |
| `source` + `digest` | citation is verifiable, not recalled |

`normalized` is the AI-load-bearing field. It is the CoreSpec form of the clause
per `bestcodex.md` §5.2 — literals, variables, calls, lets, conditionals,
pattern tests, ordered case selection — so an agent reasons over a closed node
set instead of over prose.

## 5. The four obligations, as guarantees to an agent

`bestcodex.md` §4, restated as what the AI view promises.

**Fidelity (§4.1) — "every assertion is here, or its absence is recorded."**
The inventory is complete or the build fails. An agent can therefore treat
"absent from the view" as "absent from the standard", which is exactly the
inference it cannot safely make against L0.

**Semantic preservation (§4.2) — "`normalized` means what the clause means."**
One specified lowering per construct, lowering fixtures, and one generic Lean
denotation. The agent is not trusting a paraphrase.

**Behavioral evidence (§4.3) — "a computed answer is labelled as evidence or as
a candidate."** Per `bestcodex.md` §6, exact mode versus candidate mode. The AI
view exposes that distinction directly: any numeric answer carries
`certified` / `refuted` / `unresolved`, and **never** a bare number.

**Reproducibility (§4.4) — "the facts state which revision they came from."**
Source, semantic, ledger and evidence digests are distinct and all four ride on
every answer. When the pinned revision changes, stale facts are detectable
rather than silently retained.

## 6. Access patterns

Five queries cover essentially everything an agent asks of this corpus. Each
returns records from §4, never prose.

| Query | Returns | Guarantee |
|:--|:--|:--|
| `op(name)` | the full §4.3.1 record: signature, parameters, operands, result, **all** behavior cases in order | H4 — never a partial case list |
| `clause(id)` | every assertion under that clause, with `case_count` | completeness within the clause |
| `defines(term)` | the §2.1 definition plus every clause that uses it | H5 — sorts travel with terms |
| `evidence(op, spec, operands)` | outcome + certificate digest, or `unresolved` | H6 — no bare numbers |
| `quote(id)` | verbatim span + digest + line | citation the agent can verify |

**`op(name)` is atomic and never truncated.** The largest record is §4.10.6 FMA
at 32 ordered clauses; the whole of clause 4.10 is ≈ 5 800 tokens. Returning a
complete operation record costs a few hundred tokens. There is no budget reason
to fragment one, and H4 is a decisive reason not to.

A sixth query, `all()`, returns the complete normalized corpus. At ≈ 37 500
tokens for the source — and less once markup and layout are removed — this is
affordable, and it is the correct default for an agent doing whole-standard
work. Design for it rather than against it.

## 7. Gates as trust labels

`bestcodex.md` §9's seven gates — `parsed`, `checked`, `denoted`, `faithful`,
`evaluated`, `certified`, `publishable` — become the agent's trust vocabulary.
Every record carries its gate, and the agent's permitted use is a function of
it:

| Gate reached | An agent may |
|:--|:--|
| `parsed` / `checked` | quote the text; state the structure |
| `denoted` | reason about meaning; compose with other assertions |
| `faithful` | assert that the fact is what the standard says |
| `evaluated` | report exact results on the declared domain |
| `certified` | report a conformance result |
| `publishable` | cite it as settled |

This is the mechanism that stops the most damaging AI behavior on a standard:
asserting conformance from material that has only been parsed. The gate is not
advisory metadata — it is a precondition on the claim.

## 8. First review — clarity, simplicity, specificity, effectiveness, correctness

**Clarity.** The draft mixed "what the repository stores" with "what the
pipeline does". *Improvement:* §3 now says only what the AI view is (an L3d
adapter, generated, the sole read path); everything about producing L2 stays in
`bestcodex.md` and is cited, not restated.

**Simplicity.** The draft proposed embeddings, a chunker, and a similarity
index. §1's measurement kills all three: 37 500 tokens does not need retrieval.
*Improvement:* deleted. The repository is a normalized fact store with five
lookups and one bulk read. This is the largest single simplification available
and it came from measuring rather than assuming.

**Specificity.** "Preserve rule order" is not actionable. *Improvement:* every
hazard in §2 carries a count and a site (627 lines, 19 hyphenations, line 1666,
32-clause FMA), and every mitigation is a named field in §4 with the hazard it
defeats.

**Effectiveness.** The draft's gates were a status line. *Improvement:* §7 binds
each gate to a permitted claim, so the label changes agent behavior instead of
decorating output.

**Correctness — one substantive error found.** The draft asserted that ordered
case lists could be chunked if each chunk carried its index. That is wrong under
§4.3.2: first-match means case *k* is only meaningful relative to cases 1…*k−1*,
so an index without the predecessors is not enough — the agent cannot evaluate
whether an earlier pattern already matched. *Improvement:* `op(name)` is atomic;
case lists are never split; `order_critical` marks any record whose meaning
depends on its predecessors, and such records are only ever returned as part of
a complete list.

**Correctness — one scope error found.** The draft had the AI view carrying
informative NOTEs alongside normative clauses at equal weight. §1.2 and
`bestcodex.md` §5.1 both forbid a normative dependency on informative material.
*Improvement:* NOTEs are `kind: "note"`, are returned only when asked for, and
can never appear in a `requires` edge.

## 9. Second review — realizability

**Effort, and where it sits.** Normalizing 42 Signature/Behavior records and 373
ω-clause lines is bounded, one-time work. The two-column de-interleaving (H3) is
the only genuinely awkward parser, and it affects a small, enumerable set:
§4.10.9, §4.11.1–§4.11.3, and Annex F. Hand-verification of the whole corpus is
feasible — 42 records is an afternoon of review, not a program.

**The de-interleaver must be verified, not trusted.** It is the one component
that can silently attribute a clause to the wrong operation. *Refinement:* every
de-interleaved record is diffed against a hand-transcribed fixture for its
clause, and those fixtures are checked in. Four clause groups, small enough to
do by hand and permanent thereafter.

**The bootstrap is real.** §5's fidelity guarantee needs an inventory of
normative assertions, which must itself be extracted from the damaged source.
*Refinement:* the inventory is generated, digest-pinned, and reviewed once per
revision by a person holding the PDF. Its diff is the first artifact examined
when the pinned revision changes.

**The AI view can be built before the rest of the pipeline exists.** L1, L2,
L3a–L3c are substantial projects. But §4's record needs only: normalized text,
sorts, order metadata, provenance, and an effectivity label. `effectivity` can
be hand-assigned for 48 operations and later replaced by `bestcodex.md` §7's
derived, path-sensitive obligations without changing the record shape.
*Refinement:* ship the AI view at gate `faithful` first. It is useful there,
and `evaluated`/`certified` fill in as L3b lands.

**One thing is not realizable early, and should be labelled rather than
attempted.** `evidence()` requires the certificate checker of `bestcodex.md` §8.
Until it exists, the query must answer `unresolved(reason: "no evidence engine")`
for every analytic operation. That is the honest answer and it is exactly the
three-outcome discipline of §8 applied to the repository's own immaturity. It
must not fall back to a computed float.

**Cost of being wrong is asymmetric, so default conservative.** A missing fact
makes an agent say "not in the corpus" — recoverable. A wrongly normalized
clause makes it assert a false rule with a valid-looking citation —
unrecoverable without re-reading the source. Every ambiguous normalization is
therefore emitted as `gate: "checked"` with the verbatim text and no
`normalized` field, rather than as a guess.

## 10. Build order

1. **Normalizer + span index.** Strip emphasis (H1), rejoin hyphenation (H2),
   de-interleave columns (H3) with checked-in fixtures. Emit one record per
   assertion with `text`, `source`, `digest`. Gate: `parsed`.
2. **Structure.** Attach `operation`, `case_index`, `case_count`,
   `order_critical`, `kind`, `modality`. Implement `op()`, `clause()`, `quote()`.
   Gate: `checked`.
3. **Inventory + ledger.** Complete the assertion inventory; review it against
   the PDF; wire the completeness check that makes "absent" trustworthy. Gate:
   `faithful`.
4. **Sorts and effectivity.** Add `sorts` and a hand-assigned `effectivity` over
   48 operations. Implement `defines()`. `evidence()` answers `unresolved`.
5. **Normalized forms.** Add the CoreSpec `normalized` field as L2 lands. Gate:
   `denoted`.
6. **Evidence.** Wire `evidence()` to the §8 checker. Gates: `evaluated`,
   `certified`.

Steps 1–4 are independent of the AFSpec/CoreSpec pipeline and deliver most of
the value against §2.

## 11. What this does not do

- **It does not fix the source.** The undefined equation-language constructs,
  §4.8's escape into English, and the damaged markup are defects in `IEEE_D1.md`.
  The repository records and reports them.
- **It does not make the standard computable.** H6 is a property of §4.10.9 and
  §4.7.4, not of the reader. The repository's contribution is to say so on every
  affected record.
- **It does not remove trust.** The normalizer, the de-interleaver, the fixtures,
  the inventory review, and everything in `bestcodex.md` §4.4's lineage remain
  trusted. The contribution is that the base is small and enumerated.
- **It is not a second source of truth.** Per Rule A, the AI view is a
  projection. When it disagrees with L2, L2 wins and the view is a bug.
