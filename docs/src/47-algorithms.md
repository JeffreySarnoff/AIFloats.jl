# [Algorithms](@id algorithms)

```@meta
CurrentModule = AIFloats
DocTestSetup = :(using AIFloats)
```

This page describes **how** AIFloats obtains the results the other pages state as
contracts. Nothing here is an interface: the algorithms may be replaced by better
ones without notice, and code should depend on the documented behaviour rather
than on the mechanism producing it.

What is *not* negotiable is the specification each algorithm implements. The
normative source is the designated IEEE P3109 Interim Report, cited throughout as
**[P3109]** and listed with the other references at the foot of this page. Section
numbers always belong to that document. References to the wider literature are
background and motivation — they explain why an approach is the usual one, and
they never establish a guarantee this package makes.

Three algorithms earn a place here because a reader's trust or decisions depend
on them: how a stochastic mode turns `N` random bits into a rounding decision,
how a transcendental result is *proved* correctly rounded rather than merely
computed carefully, and how predicates written over exact real numbers are
evaluated on carriers that cannot hold them.

---

## [Stochastic rounding](@id alg-stochastic)

### Common aspects of the three variants

A stochastic mode rounds the same value up sometimes and down other times, so
that the *expected* result tracks the exact value instead of a fixed neighbour.
It needs a source of randomness, and [P3109] §4.7.4 fixes its form: an unsigned
integer `R` of `N` bits, `0 ≤ R < 2^N`.

Everything else follows from one quantity. After truncating the exact
significand onto the target grid, some fraction of an ulp is left over; call it
`ν`, with `0 ≤ ν < 1`. `ν = 0` means the value is exactly representable; `ν = ¾`
means the true value sits three quarters of the way toward the next datum. A
rounding mode is then a single predicate: **round away from zero, or not?**

For a deterministic mode that predicate reads `ν` alone — `RTZ` never rounds
away, `RTA` rounds away when `ν ≥ ½`. A stochastic mode reads `ν` *and* `R`. And
since `R` is uniform on `0:2^N-1`, the probability of rounding away is just the
count of `R` values satisfying the predicate, divided by `2^N`:

```math
P(\text{away}) = \frac{\#\{R : \mathrm{RoundAway}(ν, R)\}}{2^N}
```

That is the useful way to read the three variants. Ideally `P(away) = ν` exactly
— then the expected result is the exact value and rounding is unbiased. But `R`
takes only `2^N` values, so `P(away)` can only be a multiple of `2^-N`. **Each
variant is a different way of snapping `ν` onto that grid of `2^N` steps**, and
that is the whole of the difference between them.

### The three predicates

[P3109] §4.7.4 defines them directly. Counting the satisfying `R` gives the
probability in the third column:

| Mode | `RoundAway` iff | `P(away)` | `ν` is snapped by |
|:--|:--|:--|:--|
| [`RSA`](@ref)`{N}` | `⌊ν·2^N⌋ + R ≥ 2^N` | `⌊ν·2^N⌋ / 2^N` | truncation |
| [`RSB`](@ref)`{N}` | `⌊ν·2^(N+1)⌋ + (2R + 1) ≥ 2^(N+1)` | `⌊ν·2^N + ½⌋ / 2^N` | nearest, ties up |
| [`RSC`](@ref)`{N}` | `RNITE(ν·2^N) + R ≥ 2^N` | `RNITE(ν·2^N) / 2^N` | nearest, ties to even |

`RNITE` is the round-to-nearest-ties-even that [P3109] §4.7.4 defines alongside
these predicates.

**`RSA`** is the direct construction: compare the `N`-bit truncation of `ν`
against a uniform draw. Simple, and one shift, one floor, one compare.

**`RSB`** looks unlike the others until the counting is done. Evaluating at
*doubled* resolution and adding `2R + 1` places the comparison a half-step off
the grid, and a half-step offset is exactly what turns truncation into
round-to-nearest. It buys nearest-quantization **without a second random bit** —
`R` is still `N` bits wide. That is the trick the variant exists for.

**`RSC`** reaches nearest-quantization the direct way, by actually
round-to-nearest-even-ing the scaled fraction before the comparison. Same
accuracy as `RSB`, different tie-break, more work.

### Where they differ, concretely

`RSB` and `RSC` can only disagree when `ν·2^N` lands *exactly* halfway between
two grid points. Everywhere else they are identical; `RSA` differs almost
everywhere.

| `N` | `ν` | `RSA` | `RSB` | `RSC` | |
|--:|--:|--:|--:|--:|:--|
| 1 | 0.25 | 0 | ½ | 0 | tie at `0.5`: `RSB` up, `RSC` to even (down) |
| 1 | 0.75 | ½ | 1 | 1 | tie at `1.5`: both go to `2` |
| 2 | 0.125 | 0 | ¼ | 0 | tie at `0.5` again |
| 3 | 0.375 | ⅜ | ⅜ | ⅜ | on the grid: all three agree |
| 3 | 0.8 | ¾ | ¾ | ¾ | off the grid, no tie: `RSB`, `RSC` agree |

The last row is the one to remember. `ν = 0.8` is not representable on the
3-bit grid, so **every** variant rounds away with probability `¾`, not `0.8`.

!!! warning "No variant is exactly unbiased at finite `N`"
    Stochastic rounding is unbiased when `P(away) = ν`. At a finite budget that
    equality holds only for the `ν` that land on the grid. The residual bias is
    `P(away) − ν`, bounded by:

    | Mode | bias range | worst case |
    |:--|:--|--:|
    | `RSA` | `(−2^-N, 0]` — never positive | `2^-N` |
    | `RSB` | `[−2^-(N+1), +2^-(N+1)]` | `2^-(N+1)` |
    | `RSC` | `[−2^-(N+1), +2^-(N+1)]` | `2^-(N+1)` |

    `RSA`'s bias is **systematic**: it is one-signed, always toward zero, so it
    accumulates across many roundings rather than cancelling. `RSB` and `RSC`
    are centred, so their errors tend to cancel — except at exact ties, where
    `RSB` always goes up and `RSC` alternates by parity.

    AIFloats claims no bias figure beyond these bounds.

### Choosing a variant

Start from what your budget is really constrained by.

**`RSB` is the reasonable default.** It gets centred, nearest-quantization at
`RSA`'s bit cost and close to `RSA`'s arithmetic cost. If nothing in your problem
argues for another, use it.

**Choose `RSC` when many roundings accumulate and ties are common.** Ties are not
rare in practice: they occur whenever the exact value sits on a sub-grid
boundary, which is systematic in fixed-point-ish data, quantized activations, and
anything derived from a coarser format. `RSB` pushes every one of those upward;
`RSC` alternates by parity so they cancel. Pay for it only when you have reason
to think ties are frequent, because it is the most expensive of the three.

**Choose `RSA` when the random bits or the gate count are the binding
constraint**, and a known one-signed bias of at most `2^-N` is acceptable — or
when you are reproducing a result from the literature, where "stochastic rounding
with `N` bits" almost always means this construction. Its one-signed bias is a
real hazard in long accumulations; compensate by raising `N` rather than by
hoping.

**Choosing `N` matters more than choosing the variant.** The grid spacing `2^-N`
is the bias floor, and no variant escapes it. If the quantity you are trying to
preserve — a weight update, a residual — is around `2^-k` of an ulp, then `N` must
be comfortably above `k` or the update is invisible to *every* variant. The
package default is `N = 8`; the range is `1:60`.

```jldoctest algorithms
julia> nrandbits(RSA_SN), isstochastic(RSA_SN), isstochastic(RTE_SN)
(8, true, false)

julia> AIFloats.ρRSB{16}()          # a wider budget
RSB
```

**If you need determinism, do not reach for a pure mode by default.** A
stochastic projection is reproducible when you supply `R` outright, or a seeded
`rng` — see the [stochastic contract](@ref projections). Reproducibility and
randomness are not in conflict here.

### Citations

The three variants and the trade they represent are from **[Fitzgibbon2025]**,
which [P3109] cites at its §4.7.4 NOTE 2 for exactly this point — the
paper's subject is stochastic rounding on a small bit budget, which is why the
`RSB` half-step construction exists at all. **[Croci2022]** is the standard
survey of stochastic rounding, its error analysis and its applications.
**[Gupta2015]** is the result usually credited with establishing stochastic
rounding for low-precision training. **[Higham2002]** is the general reference
for accumulated rounding-error analysis.

The training motivation — that an update smaller than one ulp is discarded by
every deterministic mode but can accumulate under a random one — comes from that
literature. It is not a guarantee this package makes.

---

## [Interval enclosure](@id alg-enclosure)

### The problem: you cannot decide by computing harder

Ask for `Exp(x)` in a format with a 4-bit significand. The exact `e^x` is
irrational; the answer must be one of two neighbouring datums; and choosing
between them means knowing which side of the midpoint the true value falls on.

Computing `e^x` in double precision does not settle that. If the true value lies
close enough to the midpoint, a `Float64` approximation lands on the midpoint too
— and the approximation error, however small, is larger than the distance that
decides the answer. Increasing the working precision helps until it doesn't:
for any *fixed* precision there are inputs whose true results sit closer to a
rounding boundary than that precision can resolve. This is the **Table Maker's
Dilemma** [Muller2018].

The consequence is sharp, and it is why this section exists: **no approximate
evaluation, at any fixed precision, can be trusted to produce a correctly rounded
result.** A faster elementary function does not fix it. A wider carrier does not
fix it. What fixes it is not computing a better value — it is computing a value
*you can prove is good enough*, and knowing when you have not.

### The strategy: bracket, decide, refine

The standard answer is **Ziv's strategy** [Ziv1991]: evaluate at some working
precision, obtain a bracket that provably contains the true value, and check
whether the bracket is narrow enough to settle the question. If it is, you are
done and you have a proof. If it is not, raise the precision and try again.

AIFloats applies that with one adaptation that makes it cheap: **the question is
settled in the target format's code-point space, not in the carrier.** The
bracket does not have to be narrow in absolute terms. It only has to be narrow
enough that both of its endpoints project to the *same* code point.

```
prec ← starting precision
loop
    (lo, hi) ← evaluate f, giving lo ≤ truth ≤ hi     # directed MPFR endpoints
    if lo == hi
        return project(lo)                            # the result was exact
    c_lo ← project(lo, sticky = +1)                   # truth is above lo
    c_hi ← project(hi, sticky = −1)                   # truth is below hi
    if c_lo == c_hi
        return c_lo                                   # PROVED: any value in
                                                      # [lo, hi] rounds here
    if prec ≥ cap: error                              # never a wrong answer
    prec ← 2 · prec
```

The middle step is the whole argument. Projection is monotone, and the true value
lies somewhere in `[lo, hi]`. So if the two endpoints project to one code point,
every value in the interval projects to that code point — including the true one.
The result is correct *whatever* the true value is, and no further knowledge of
it is needed.

Two properties of that argument are worth drawing out:

- **It holds for every rounding mode**, including the stochastic ones at a fixed
  `R`, because it never assumes anything about projection beyond monotonicity.
  One loop serves all 27 projections.
- **It cannot silently fail.** The alternative to agreement is another rung, and
  the alternative to the cap is an error. There is no branch that returns an
  unproved answer.

The endpoints are projected with a **sticky direction** — `+1` on the lower
endpoint because the truth is strictly above it, `−1` on the upper because the
truth is strictly below. Without that, an endpoint landing exactly on a rounding
boundary would be judged as a tie, which it is not. That mechanism is
[the sticky protocol](@ref alg-sticky) below, and this is one of the two places
it is essential.

### What AIFloats does specifically

**Where the ladder starts.** At the operands' own width plus a margin — 72 bits
for `Float64` operands, 136 for `Float128` — rather than at a precision chosen to
resolve anything. Correctness does not depend on the starting point at all: the
loop escalates regardless. Only the number of MPFR calls does. Measured over a
sweep of every code point of ten enclosure-evaluated operations across three
formats, **97.6% of enclosures resolve on the first rung**, so a high start is
waste on almost everything and the 2.4% tail pays one extra doubling.

**How the bracket is obtained.** MPFR computes each of its primitives with
correct rounding [Fousse2007], so a single round-to-nearest evaluation `r`
satisfies `|truth − r| ≤ ½ulp(r)`, and `[prevfloat(r), nextfloat(r)]` therefore
strictly contains the true value. One MPFR call plus two cheap steps replaces two
directed evaluations and two rounding-mode round-trips. The enclosure is 2 ulps
wide instead of 1 — nothing against a target grid of at most 16 bits.

!!! warning "That shortcut has a precondition"
    It is sound only when the evaluated function is **one** MPFR primitive. A
    composite closure rounds more than once, its error can exceed `½ulp`, and the
    2-ulp bracket would no longer be a bracket. Composite rows use two directed
    evaluations instead. The precondition is not checkable at the call site, so
    it is a discipline in `ops/oracle.jl`, not an assertion.

**The fast stages are not shortcuts around the proof.** Before the ladder runs,
an eager `Float64` estimate may be tried — but it is accepted *only* when the
two-sided sticky projection of its error envelope agrees on one code point, which
is the same test the ladder uses. If it does not agree, the ladder runs.
`AIFloats.FAST_ENCLOSURE` switches the stage off, and the test suite pins both
paths to identical results.

!!! warning "`Float128` is a carrier, not an oracle"
    libquadmath's elementary functions are not assumed to be correctly rounded,
    and no Quadmath transcendental result is ever accepted as an answer on its
    own. `Float128` is used to *hold* values exactly; deciding a code point is
    the ladder's job. The pure-Julia `AIFloats.fma128` and `AIFloats.faa128`
    carry their own documented guarantees and are a separate matter.

**Which operations use it.** The registry records a group per operation
(see [Operations](@ref operations)). Group `A` and `C` operations —
`Add`, `Multiply`, `FMA`, the extremum family — have exact results reachable
without a ladder, so they never enter it. Group `B` — `Exp`, `Log`, `Sqrt`,
`Divide`, the trigonometric, hyperbolic and π-scaled families, `Hypot`,
`Softplus` — is what this section is for.

The quotients (`Divide`, `Recip`, `Sqrt`, `RSqrt`) sit between the two. They try
an exactness **proof** first: for a computed quotient `q`, a fused
multiply-add giving `fma(q, y, -x) == 0` establishes that `q·y` is exactly `x`,
so `q` is the exact quotient and no rounding decision is in doubt. Many quotients
of small-format datums are exact, and those cost one proof. The ladder runs only
when the proof fails.

### Citations

**[Ziv1991]** introduced the evaluate-and-refine strategy for correctly rounded
elementary functions. **[Muller2018]** is the standard reference for the Table
Maker's Dilemma and for correctly rounded function evaluation generally.
**[Fousse2007]** describes MPFR, whose correctly rounded primitives are what
make the 2-ulp bracket sound.

---

## [The sticky protocol](@id alg-sticky)

### The problem: the specification is written over exact reals

Every rounding predicate in [P3109] §4.7.4 is a statement about the exact
leftover fraction `ν`. Read them literally:

- `RoundAway(TowardPositive) = ν > 0 and X > 0`
- `RoundAway(NearestTiesToEven) = ν > 0.5 or (ν = 0.5 and not CodeIsEven)`
- `RoundAway(StochasticA) = ⌊ν·2^N⌋ + R ≥ 2^N`

These are exact-arithmetic conditions. `ν > 0` distinguishes "exactly
representable" from "inexact by any amount whatsoever". `ν = 0.5` means *exactly*
one half, not approximately.

An implementation computes `ν` on a carrier — `Float64`, `Float128`, a
fixed-point `Dyadic`. That carrier is finite, and `ν` frequently is not
representable in it. So the implementation holds some `ν̃`, and `ν̃` may be a
rounded version of a value that was never equal to it.

The failure this causes is not a rounding error. It is a **wrong answer to a
different question**. Suppose the true `ν` is a hair above `½`, and the carrier
rounds it to exactly `½`. Under `RTE` the specification says "greater than a
half, round away, unconditionally". The implementation sees a tie and consults
code parity, so half the time it rounds the wrong way — and it does so *silently*,
producing a plausible datum with no indication anything went wrong. The same trap
sits under `RTO` at `ν > 0`, and under the stochastic modes wherever `ν·2^N` lands
on a sub-grid boundary.

Widening the carrier does not fix this; it only moves which inputs trip it.

### The idea: carry a direction, not a better number

The protocol's move is to stop trying to represent `ν` exactly, and instead
represent it as a **pair**: a carrier value together with a direction saying
where the truth lies relative to that value.

```
νs = 0    the carrier value is exact — ν̃ IS ν
νs = +1   the true ν is strictly ABOVE ν̃
νs = −1   the true ν is strictly BELOW ν̃
```

Read the pair as the exact quantity `ν̃ + νs·ε`, where `ε` is infinitesimal —
positive, and smaller than any difference that could matter. Every predicate is
then evaluated on *that*, and each of the three comparisons the specification
needs has a two-line definition:

| Specification asks | Evaluated as |
|:--|:--|
| `ν > c` | `ν̃ > c`, or `ν̃ == c` and `νs > 0` |
| `ν == c` | `ν̃ == c` **and** `νs == 0` |
| `ν ≥ c` | `ν̃ > c`, or `ν̃ == c` and `νs ≥ 0` |

That is the entire mechanism. It is not an approximation of the specification —
it *is* the specification, evaluated exactly, on a carrier that cannot hold the
number the specification talks about.

### It resolves the ambiguity rather than guessing at it

Take the `RTE` case above. One carrier value `ν̃ = ½`, three different exact
situations, three different correct answers:

| `ν̃` | `νs` | true `ν` | `RTE` says | Why |
|--:|--:|:--|:--|:--|
| `0.5` | `+1` | just above ½ | round away | `ν > ½` is satisfied — not a tie at all |
| `0.5` | `−1` | just below ½ | round down | `ν > ½` fails and `ν = ½` fails |
| `0.5` | `0` | exactly ½ | consult `CodeIsEven` | a genuine tie |

Without the direction all three collapse into the third row, and two of them are
answered wrongly. With it, each gets the answer [P3109] §4.7.4 specifies.

The stochastic modes need the same care one level down, on the `2^N` sub-grid
rather than on the ulp. When the scaled fraction `ν̃·2^N` lands exactly on a grid
point but the truth is strictly below it, the floor must step down — the truth
has not reached that grid point. `_νfloorscaled` does that when `νs < 0`.
Symmetrically, `_νrnite` treats a sub-grid tie as rounding away when `νs > 0`,
because the truth is past the halfway point even though the carrier value is not.

### Where the direction comes from

Three sources, and every value reaching the rounding core carries one:

- **Exact carriers** report `νs = 0`. A `Dyadic` value inside its exact band, or
  a `Float64` operand whose decode is exact, knows it is exact and says so.
- **The enclosure ladder** supplies `+1` for its lower endpoint and `−1` for its
  upper, since the truth is bracketed strictly between them. This is why
  [interval enclosure](@ref alg-enclosure) can decide a code point at all: the
  endpoints are not values to be rounded, they are bounds, and the sticky
  direction is what tells the projector so.
- **The rung-3 `Add` protocol** produces an `AIFloats.Sticky` when a sum's tail
  falls past the exact accumulator's alignment band. Rather than widen the
  carrier to keep bits it will not need, it discards the tail and records which
  way it pointed.

### Why a direction is enough

That last case is the one that has to be argued, because it deliberately throws
information away. It is sound because of a width inequality: the accumulator's
alignment band is 94 bits, and `94 > P + N + 2` for every precision `P ≤ 16` and
every stochastic budget `N ≤ 60` that the package admits.

So a discarded tail is below the last bit of the target grid, below the finest
stochastic sub-grid step `2^-N`, and below any rounding threshold in play. It
cannot change which side of a boundary the value falls on — it can only say
*which* side, which is exactly what a direction records. Its magnitude is
provably irrelevant, so not carrying it costs nothing.

### The payoff

The rounding core is a direct transcription of [P3109] §4.7.4. There is no epsilon
tolerance anywhere in it, no "close enough to a tie" heuristic, and no carrier-
dependent behaviour — the same predicates, evaluated the same way, whether the
value arrived as a `Float64`, a `Float128`, an exact `Dyadic`, or a bound from an
MPFR ladder. That uniformity is what makes the whole projection path testable
against an independent reference, which is how it is verified.

---

## References

**Normative**

- **[P3109]** IEEE Working Group P3109, *Interim Report on Arithmetic Formats for
  Machine Learning*, version 4.0.3, 1 September 2026.
  <https://github.com/P3109/Public/blob/main/IEEE%20P3109%20Interim%20Report.pdf>
  — the sole normative source; see [`draft_identity`](@ref) for the PDF digest
  this release was compared against. An unapproved draft: its cover states it
  must not be used for conformance or compliance purposes.

**Cited by the report**

- **[Fitzgibbon2025]** A. W. Fitzgibbon and S. Felix, "On stochastic rounding
  with few random bits," in *IEEE 32nd Symposium on Computer Arithmetic (ARITH
  2025)*, El Paso, TX, USA, 4–7 May 2025, pp. 133–140.
  <https://doi.org/10.1109/ARITH64983.2025.00029> — reference [3] of [P3109],
  cited in its §4.7.4 NOTE 2 for the accuracy/complexity balance among
  `StochasticA`, `StochasticB` and `StochasticC`.
- **[Higham2002]** N. J. Higham, *Accuracy and Stability of Numerical
  Algorithms*, 2nd ed., SIAM, 2002 — reference [6] of [P3109].

**Background (not normative, and not a guarantee of this package)**

- **[Ziv1991]** A. Ziv, "Fast evaluation of elementary mathematical functions
  with correctly rounded last bit," *ACM Transactions on Mathematical Software*,
  vol. 17, no. 3, pp. 410–423, 1991.
- **[Muller2018]** J.-M. Muller et al., *Handbook of Floating-Point Arithmetic*,
  2nd ed., Birkhäuser, 2018.
- **[Fousse2007]** L. Fousse, G. Hanrot, V. Lefèvre, P. Pélissier and
  P. Zimmermann, "MPFR: A multiple-precision binary floating-point library with
  correct rounding," *ACM Transactions on Mathematical Software*, vol. 33, no. 2,
  article 13, 2007.
- **[Croci2022]** M. Croci, M. Fasi, N. J. Higham, T. Mary and M. Mikaitis,
  "Stochastic rounding: implementation, error analysis and applications,"
  *Royal Society Open Science*, vol. 9, no. 3, 211631, 2022.
- **[Gupta2015]** S. Gupta, A. Agrawal, K. Gopalakrishnan and P. Narayanan,
  "Deep learning with limited numerical precision," in *Proceedings of the 32nd
  International Conference on Machine Learning (ICML)*, 2015, pp. 1737–1746.

```@meta
DocTestSetup = nothing
```
