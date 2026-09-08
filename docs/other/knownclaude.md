# A warrant-carrying knowledge repository for P3109

**Status:** design plan. Not an IEEE document. Changes nothing about the
authority of the pinned source revision.

**Sources:** this plan uses only [`bestclaude.md`](bestclaude.md) and
[`IEEE_D1.md`](IEEE_D1.md). Its principles, obligations and vocabulary are
`bestclaude.md`'s; its measurements are taken from `IEEE_D1.md` directly.

## 1. Thesis

`bestclaude.md` closes on a rule: *author once, lower once, define meaning once,
never confuse a computed candidate with checked evidence — and never let the
mechanism that found an exact value go unnamed.*

The last clause is the whole design for an AI consumer. An agent's
characteristic failure on a standard is not ignorance; it is **producing a
correct-looking answer whose warrant is unstated and, on inspection, absent**.
So:

> **Every fact the repository returns names its warrant.** A fact without a
> warrant is not returned.

Six warrants, §5. Everything else here follows from making them explicit.

## 2. What the corpus actually is

| Property | Value |
|:--|--:|
| `IEEE_D1.md` | 3 069 lines, 155 982 bytes, **≈ 37 500 tokens** |
| Clause 4 (Operations) | ≈ 17 000 tokens |
| Signature/Behavior record pairs | 42 |
| Operation names with a Signature | 48 |
| ω-clause lines | 373 |
| Operations defined by **composition** of other ω-operations | 6 |
| Longest ordered case list | 32 (§4.10.6 FMA); then 24, 19, 18 |
| `shall` / `should` / `may` | 23 / 10 / 12 |

The corpus fits in context whole. **There is no retrieval problem here**, and
building embeddings and a chunker over 37 500 tokens would add a lossy layer for
no benefit. The problem is that the text does not, on its face, tell an agent
what kind of thing each statement is or how strongly it may be relied upon.

Three question types cover essentially all agent use:

1. *What does the standard say about X?* — needs verbatim text plus provenance.
2. *What is the result of Op on these operands?* — needs a warrant, and
   frequently the honest warrant is "no answer is available".
3. *May I claim conformance?* — needs the §4.5 scope and evidence status.

Only (1) is a text problem. (2) and (3) are warrant problems.

## 3. Three authorities, three claim strengths, and a fourth thing

`bestclaude.md` §5 fixes three authorities that must never be collapsed: the
pinned revision is **normative**; the AFSpec corpus is the **authoritative
editable model of it**; CoreSpec is the **canonical semantic form of the model**.

For an agent these become claim strengths, and the repository is a **fourth**
artifact that appears nowhere in that list:

| Source of a fact | The agent may say | It may **not** say |
|:--|:--|:--|
| pinned revision, verbatim + digest | "the standard states …" | — |
| model (AFSpec), gate `faithful` | "the standard requires …, as modelled" | "the standard states" *verbatim* |
| semantic form (CoreSpec) | "this denotes …" | "this computes …" |
| checked evidence | "conformance holds for …" | anything beyond §4.5's scope |
| **the repository itself** | **nothing** | it is never a citation |

**Rule R1 — the repository is never an authority.** It cites; it is not cited.
Every returned fact carries the identifier of what backs it, and an agent
answering from the repository must attribute to that backing artifact. This is
the rule that prevents a convenience layer from quietly becoming a fifth source
of truth.

## 4. Precomputed assets

`bestclaude.md` §6 contains work an agent should never redo. Four tables,
generated once, are the repository's substance.

### 4.1 The effectivity map

`bestclaude.md` §6, keyed by the domain of the ω-result. Every **finite** datum
is dyadic, because §4.7.2 decodes to `(0 or 1 + T·2^{1−P}) · 2^{E−B}` — so the
domain of an ω-result is determined by the operation, not by the format.

| Domain | §4.7.4 / §4.7.6 | Operations |
|:--|:--|:--|
| `dyadic` | exact, integer work | `ωAdd`, `ωSubtract`, `ωMultiply`, `ωFMA`, `ωFAA`, `ωNegate`, `ωAbs`, `ωCopySign`, the extremum family, `ωConvert` |
| `rational` | exact rational comparison | `ωRecip`, `ωDivide` |
| `algebraic` | real-algebraic arithmetic | `ωSqrt`, `ωRSqrt`, `ωHypot` |
| `transcendental` | undecidable in general | `ωExp`, `ωExp2`, `ωLog`, `ωLog2`, `ωLogOnePlus`, `ωExpMinusOne`, §4.10.10–§4.10.16 |

Verified against the source: `ωHypot(X, Y) → √(|X|² + |Y|²)` (§4.10.14) is
algebraic; `ωRecip(X) → 1/X` (§4.10.8) leaves the dyadics.

### 4.2 The composition graph

Six operations are not defined by a terminal clause at all but by calling
others:

```
ωLogOnePlus(X)             → ωLog(ωAdd(1, X))              §4.10.9
ωExpMinusOne(X)            → ωSubtract(ωExp(X), 1)         §4.10.9
ωMinimumNumber(X,Y)        → ωMinimum(X,Y)                 §4.11.1
ωMaximumNumber(X,Y)        → ωMaximum(X,Y)                 §4.11.1
ωMinimumMagnitudeNumber    → ωMinimumMagnitude             §4.11.2
ωMaximumMagnitudeNumber    → ωMaximumMagnitude             §4.11.2
```

The graph is small and must be explicit, because **effectivity is inherited
through it**. `ωExpMinusOne`'s own clause names only `ωSubtract` and `ωExp`; its
transcendental status comes from the callee. §9 records this as a correctness
error the first draft made.

### 4.3 The order index

§4.3.2: *"the first matching pattern in the order presented in this document
defines the behavior."* Every ω-clause carries `case_index` and `case_count`,
and any record with `case_count > 1` is **only ever returned as part of the
complete ordered list**. Case *k* is meaningless without cases 1…*k−1*: the
agent cannot tell whether an earlier pattern already matched. The largest list
is 32 clauses and the whole of §4.10 is ≈ 5 800 tokens, so there is no budget
argument for splitting one.

### 4.4 The sort table

§4.1 and §3.1 distinguish an encoded `Value<f>`, a `Datum` (closed extended
real), and the code integer. §3.1 NOTE 2 adds that a real constant written in an
operation definition means `ωEncode_f` of it. Every name in every normalized
clause carries its sort, so the distinction cannot be lost in paraphrase.

## 5. The warrant taxonomy

Every returned fact carries exactly one warrant.

| Warrant | Means | Agent may claim |
|:--|:--|:--|
| `quoted` | verbatim span + byte digest from the pinned revision | "the standard states" |
| `modelled` | a reviewed ledger entry maps this assertion to the model | "the standard requires, as modelled" |
| `derived` | computed from other facts by a named rule (e.g. effectivity through §4.2's graph) | "it follows that", naming the rule |
| `interpreted` | the source is silent or ambiguous; a recorded interpretation applies | "under interpretation ⟨id⟩" |
| `certified` | checked evidence exists for this operand tuple, naming the licensing theorem | "the result is" |
| `unresolved` | no warrant available — budget, theory, or scope | **"no answer is available", and nothing else** |

`bestclaude.md` §6 requires certificate payloads to name their **licensing
theorem** (endpoint agreement is sound only under a proved monotonicity result).
That name rides on the `certified` warrant, so an agent reporting a value can
say what makes it true.

**`unresolved` is a first-class answer, not a failure.** It is the mechanism
that stops the most damaging behavior available to an agent here: computing
`exp(x)` in host floating point, rounding, and reporting it as the standard's
result. §4.10.9 ends `ωExp(X) → e^X` and §4.7.4 then decides by exact real
comparison; nothing in the prose warns the reader. The repository must.

## 6. Clause-level special cases versus expression normalization

`bestclaude.md` §9 Y-e found that these are different mechanisms and are easy to
conflate. The distinction is load-bearing for an agent and is visible in the
source one line apart:

- `ωLog(0) → −∞` **is an explicit clause** in §4.10.9. Warrant: `quoted`.
- `ωExp(0)` has **no clause**. §4.10.9 gives `ωExp` exactly four cases — `NaN`,
  `+∞`, `−∞`, `X` — so zero falls through to `ωExp(X) → e^X`. That `e⁰ = 1`
  exactly is *not* in the standard; it requires symbolic normalization of the
  ω-expression.

The same holds through §4.2's composition graph: `ωExpMinusOne(0)` reduces to
`ωSubtract(ωExp(0), 1)`, which is exactly `0` — again by normalization, not by
any clause.

So the repository separates two answer sources and labels them differently:

| Mechanism | Reads | Warrant | In the trusted base |
|:--|:--|:--|:--|
| clause lookup | the ordered case list | `quoted` | no |
| expression normalization | inside a terminal clause | `derived`, naming the normalizer | **yes, and it must be bounded** |

`bestclaude.md` §8 requires normalizer bounds to be published as part of the
trusted computing base. An agent asking "what is `Exp(0)`?" must be told: no
clause covers it; it reaches the terminal clause; the exact value comes from
normalization ⟨bounded rule id⟩. An agent that cannot see this distinction will
report clause-backed and normalizer-backed answers with identical confidence.

## 7. Conservative defaults

`bestclaude.md` §9 Y-a fixes the direction in which an undecidable analysis must
err: **sound by over-approximation**. Reachable-but-unplanned is a hole;
unreachable-but-planned is only waste. As repository policy:

- Undecided clause reachability → the clause is returned as reachable.
- Ambiguous normalization → emit verbatim text with no normalized form, warrant
  `quoted`, rather than a guess.
- Unknown effectivity → `transcendental`, the most restrictive class.
- Missing evidence → `unresolved`, never a computed candidate.

The asymmetry justifies it. A missing fact makes an agent say "not in the
corpus" — recoverable by reading the source. A wrongly normalized clause makes
it assert a false rule with a valid-looking citation — not recoverable at all,
because the citation checks out.

## 8. Maturity, with the ratchet

`bestclaude.md` §8's levels — parsed, checked, denoted, rendered,
conformance-certified — become preconditions on claims, not status decoration.
A record's level bounds its warrant: nothing below `rendered` may carry
`modelled`, and nothing below `conformance-certified` may carry `certified`.

Y-b's **ratchet** applies to the repository directly: the level attained for a
given assertion may not decrease across source revisions without a recorded,
reviewed waiver. Without it, a revision silently downgrades facts an agent has
already relied on, and nothing signals that it happened.

## 9. First review — clarity, simplicity, specificity, effectiveness, correctness

**Correctness — a real error, caught by measurement.** The draft assigned an
effectivity class per operation by inspecting that operation's own clauses. That
is wrong for the six composed operations of §4.2: `ωExpMinusOne`'s clause names
only `ωSubtract` and `ωExp`, and a per-clause assignment would miss that the
transcendental status is inherited. *Fix:* effectivity is computed over the
composition graph and carries warrant `derived`, naming the rule. The graph is
now §4.2, an asset rather than an implementation detail.

**Correctness — an over-broad claim.** The draft asserted "every datum is
dyadic", which underwrites the whole effectivity map. False: ±∞ and NaN are
datums (§3.1, D_f ⊆ ℝ^ω) and are not dyadic, or even real. *Fix:* the claim is
"every **finite** datum is dyadic", and the non-finite cases are handled by the
leading clauses of every ω-list rather than by the map. §4.1 now says so.

**Correctness — a missing rule.** The draft let the repository answer in its own
voice. *Fix:* R1 in §3 — the repository is never an authority, only ever a
citation of one. Without this the convenience layer becomes a fifth source of
truth, which is exactly what `bestclaude.md` §5's three-authority split exists
to prevent.

**Clarity.** The draft interleaved "what the repository stores" with "how the
pipeline produces it". *Fix:* everything upstream is cited to `bestclaude.md`
and not restated; this document covers only the read surface.

**Simplicity.** The draft proposed an embedding index and a chunker. §2's
measurement removes the need for both: 37 500 tokens is not a retrieval problem.
*Fix:* deleted. Six warrants, four tables, and whole-record reads.

**Specificity.** "Preserve rule order" is not actionable. *Fix:* §4.3 gives the
rule (`case_count > 1` ⇒ atomic), the reason (§4.3.2 first-match), and the
numbers (32-clause maximum, ≈ 5 800 tokens for all of §4.10) that show atomicity
is affordable.

**Effectiveness.** Warrants were initially advisory labels. *Fix:* §5 and §8
make them preconditions — a claim an agent is not permitted to make without the
corresponding warrant, and a level below which a warrant cannot be issued.

## 10. Second review — realizability

**The four tables are small and hand-checkable.** 48 operations, 6 composition
edges, 42 record pairs, 373 ω-clauses. The effectivity map is 4 rows. All of it
can be reviewed by a person in an afternoon, and that review is worth more than
any automated check at this size.

**Order metadata is mechanical.** `case_index`/`case_count` come from counting
consecutive ω-clause lines within a Behavior block. The only care needed is
where two operations are printed side by side — §4.11.1 line 1686 carries
`ωMinimumNumber` and `ωMaximumNumber` on one physical line, and it is one of the
composition edges, so getting it wrong corrupts §4.2 as well as the order index.
*Refinement:* the affected clause groups get hand-transcribed fixtures, checked
in, and diffed on every build. There are four such groups.

**The warrant taxonomy is implementable before the pipeline exists.** `quoted`
needs a span index. `derived` needs the four tables. `interpreted` needs a list.
`unresolved` needs nothing. Only `modelled` and `certified` require AFSpec,
CoreSpec and the evidence engine. *Refinement:* ship with four of six warrants;
`modelled` and `certified` answer `unresolved` until their machinery lands. That
is the honest state and it is the same three-outcome discipline applied to the
repository's own immaturity.

**The expression normalizer is the one component that must be resisted.** §6
makes it necessary — without it the repository cannot answer `Exp(0)` — and
§8 puts it in the trusted base. It is also the component most likely to grow
without bound. *Refinement:* the initial normalizer recognizes exactly one
pattern class, exact identities at distinguished arguments (`e⁰ = 1`,
`log 1 = 0`, `√(x²) = |x|`), each enumerated, each with a fixture. Anything else
returns `unresolved`. Growth is a trusted-base change requiring the review a new
primitive gets.

**The bootstrap is real, and it is the assertion inventory.** §5's warrants
presuppose an enumeration of what the standard asserts, extracted from the same
source the repository exists to protect readers from. *Refinement:* the
inventory is generated, digest-pinned, and reviewed once per revision by a
person holding the PDF; its diff is the first artifact examined when the pinned
revision changes. This is unavoidable and should be budgeted, not engineered
around.

**What is not realizable soon, and must be labelled rather than approximated.**
Certification beyond §4.5's required set — two 8-bit formats, one 4-bit, `F_X`
at most three — is out of scope by `bestclaude.md` §6's scoping argument. An
agent asking about a wider format gets classification and order, and
`unresolved` for evidence. Saying so is the correct answer, not a limitation to
be papered over.

## 11. Build order

1. **Span index and `quoted`.** Verbatim text, line, span, digest. Fixtures for
   the four two-column clause groups. Delivers question type (1) completely.
2. **Order index and sorts.** `case_index`, `case_count`, atomic record reads,
   the sort table. Removes the first-match hazard.
3. **Composition graph and effectivity map, with `derived`.** Four rows and six
   edges; effectivity computed through the graph, never per clause.
4. **`unresolved` everywhere else.** Wire the conservative defaults of §7 before
   anything can return a number.
5. **`interpreted`.** The recorded-interpretation list, keyed by source gap.
6. **`modelled`, then `certified`.** As the ledger and the evidence engine land,
   with the ratchet from §8 in force from the first revision boundary.

Steps 1–4 need nothing from AFSpec, CoreSpec, or Lean, and they deliver the
warrants that matter most: an agent that can quote accurately, respect clause
order, know what is not computable, and refuse cleanly.

## 12. Limits

- **It does not fix the source.** The undefined equation-language constructs,
  §4.8's delegation to another standard in English, and the damaged markup are
  defects in `IEEE_D1.md`; the repository records them.
- **It does not make the standard computable.** §4.10.9 and §4.7.4 are
  non-effective; the contribution is that every affected record says so.
- **It does not remove trust.** The span index, the fixtures, the composition
  graph, the normalizer and its bounds, and the inventory review are all
  trusted. Per `bestclaude.md` §8 they are published, small, and enumerated.
- **It does not certify beyond §4.5**, and does not guarantee that certificate
  search terminates.
- **It is not an authority.** R1. The repository cites; it is never cited.
