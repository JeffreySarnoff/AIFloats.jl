# Plan for replacing avoidable `BigFloat` work with `Float128`

## Status

Written against the tree after `docs/implmentplan.md` steps 0–10. Nothing here
is implemented yet. Two things from that work are load-bearing for this one:

- **`_FMA_EXACT_FLOOR` exists** (`ops/oracle.jl`) and is the worked template for
  the residual-floor proofs below — including *why* a floor is mandatory, which
  a failing test discovered rather than review.
- **The block reductions no longer use `BigFloat` when lanes are homogeneous
  Float64** — they accumulate in `Dyadic`. That makes the *mixed*-carrier path
  measured below the outlier it now is, and it is why `_samecarrier` has moved
  up this plan's priority list.

## Purpose

Replace `BigFloat` where a value can stay in a fixed-width carrier **without
changing any AIFloats result**. Lower latency and fewer allocations; not the
removal of MPFR. MPFR remains the correctness oracle and the required fallback
for unbounded exponents, values wider than 113 significant bits, and rigorous
transcendental enclosures.

The governing invariant:

> A fixed-width carrier may replace `BigFloat` only when the carried value is
> exact, or when it is used solely as a non-authoritative enclosure estimate.

This is stricter than checking that the final format has at most 16 precision
bits. Rounding an inexact intermediate to `Float128` and then projecting it can
double-round, including under directed and stochastic projections. Every fast
route below must either prove exactness or decline to the existing `BigFloat`
path.

No public API change. Deepen the existing carrier/oracle boundary with small
internal, proof-oriented helpers; keep all projection policy in `project` and
`project_interval`.

## The measurements that set the priorities

Taken on the current tree (i9-14900K, Julia 1.12.6, Quadmath 1.x, 4 threads).
Each row pairs the affected call with a control that does *not* take the
`BigFloat` route, so the gap is attributable.

| Call | Now | Control (same op, no BigFloat) | Gap |
|---|---:|---:|---:|
| `ConvertToBlockMaxAbsFinite`, B=16, **P=3 scale** | 17,069 ns / 1067 allocs | **141 ns / 0** with a P=1 scale | **121x** |
| `BlockReduceAdd`, mixed rung-1/rung-2 lanes | 7,724 ns / 645 allocs | 269 ns / 0 homogeneous | **29x** |
| `RSqrt`, rung 2 | 1,535 ns / 69 allocs | 8.5 ns rung-1 `Divide` | — |
| `Divide`, rung 2, exact quotient | 1,149 ns / 75 allocs | 1,602 ns inexact | 1.4x |
| `Recip` / `Sqrt`, rung 2 | 1,085 ns / 61 allocs | — | — |
| `BlockAdd`, B=16 (`_bp_element`) | 589 ns / 22 allocs | — | — |
| `ArcTanPi` at ±∞ (exact peel) | 583 ns / 32 allocs | — | — |
| `ArcSinPi` at 1.0 (exact peel) | 544 ns / 30 allocs | — | — |
| `Exp2` at integral input (exact peel) | 536 ns / 30 allocs | **22.7 ns** non-integral | **24x** |
| `Convert(::Integer)` above 2^53 | 506 ns / 27 allocs | 7.0 ns below the gate | 72x |
| `Log2` at a power of two (exact peel) | 499 ns / 28 allocs | **29.2 ns** non-exact | **17x** |
| `Float128(::Dyadic)` | 196 ns / 13 allocs | 3.3 ns `Float64(::Dyadic)` | **59x** |
| `ScaledAdd` (scalar `_bp_element`) | 178 ns / 7 allocs | — | — |

### The headline: the exact peels are pessimizations

`Log2` of a power of two, `Exp2` of an integer, and the π-scaled inverse-trig
peels at their exact points exist to *avoid* work — the enclosure would chase an
interior grid point forever. They are correct and necessary. But each builds its
answer as a `BigFloat`, and so **costs 17–24x the ordinary inexact input it is
meant to beat**. A user hitting `Log2(8.0)` pays 499 ns where `Log2(1.5)` costs
29 ns.

This is not a micro-optimization; it is an inversion, and it argues these leaves
go first regardless of their small absolute times. They are also the easiest
proofs in this document: `C(exponent(x))` and `ldexp(one(C), n)` are exact by
construction, with no residual argument needed at all.

### Two of these numbers do not mean what they look like

Both were chased and the result is recorded here so they are not chased again.

**`ConvertToBlockMaxAbsFinite`'s 17 µs is a non-MX scale.** With a `P = 1`
power-of-two scale — the MX/E8M0 case the format exists for — the same call is
**141 ns and allocation-free**. The 17 µs figure uses a `P = 3` scale, where
every lane quotient is a non-terminating binary fraction and `project_interval`
is doing genuinely required work for a correctly-rounded division. Attribution
inside the call: the `_exactbig` fold is 1,006 ns of it and `blockproject` is
14,776 ns. Fixing the fold (§6, done) is right on its own terms — 1,006 → 7.5 ns
and 113 allocations → 0 — but moves the public operation only 9%, and **no
Float128 quotient filter can help the rest**, because `1/96` is not exactly
representable in any binary format. The P3 `_bp_element` item is therefore worth
much less than its share of this number suggests.

**The mixed-carrier `BlockReduceAdd` does not route through `_samecarrier`.**
It uses `_reduce_add_value`/`_exactbig`. The §4 change was implemented against
this number and it did nothing here — see the rejection below.

## Findings and decisions

### Replace with `Float128` or a narrower exact carrier

Priority follows measured cost and proof difficulty jointly. P1 items need no
residual proof; P3 items each need one.

| P | Location | Present behavior | Correct replacement |
|---|---|---|---|
| 1 | `ops/oracle.jl` — exact `Log2`, π-scaled inverse-trig peels | Exact integers, halves, quarters built as `BigFloat` | Build in the input carrier with `one(C)`, `ldexp`, `copysign` |
| 1 | `ops/oracle.jl` — integral `Exp2` peel | Every exact power of two built as `BigFloat` | Return `Float64`/`Float128` when that power is finite and exact there; `BigFloat` outside the range |
| 1 | `carriers/heads.jl:120` — `Float128(::Dyadic)` | `Float128(BigFloat(x))` | Delegate to `DyadicNumbers._dyadic_to(Float128, x)`, already written and already used by the `Float64`/`Float32` methods |
| 1 | `ops/scalar.jl` — `Convert(::Integer)` | Above 2^53 always `BigFloat` | Add a Float128 rung between the existing Float64 gate and the `BigFloat` route, using the significant-bit predicate of §2 |
| 2 | `arrays/blocks.jl` — `ConvertToBlockMaxAbsFinite` | `map(x -> _exactbig(...))` lifts every lane, seed is `_cnan(BigFloat)` | Fold in the homogeneous decoded carrier; join mixed Float64/Float128 at Float128; seed with that carrier's NaN. `MaximumFinite` *selects* an operand, so the fold consumes no precision |
| ~~2~~ | `arrays/blocks.jl` — `_samecarrier` | A mixed Float64/Float128 lane pair is lifted to `BigFloat` | **Tried and rejected on measurement** — see below |
| 3 | `ops/oracle.jl` — `Divide`/`Recip`/`Sqrt`/`RSqrt` on `Float128` | Straight to an MPFR enclosure after the special rows | Accept a `Float128` result only after an exact residual proof; otherwise the current ladder |
| 3 | `arrays/blocks.jl` — `_bp_element` | Only a Float64 exact quotient avoids a directed MPFR interval | The same proof-certified Float128 quotient filter before `_encl_div_scale` |
| 3 | block reduction special rows | NaN/∞/zero manufactured as `BigFloat` | Carrier-native specials, or canonical `Float64` where only classification and sign are consumed |

### Keep `BigFloat` — these are load-bearing, not cleanup

- `_ladder1`, `_ladder2`, `_mpfr1`, `_mpfr2`, the π enclosures, and the final
  directed interval refinements. These supply *certified bounds*; a libquadmath
  value supplies only an estimate.
- Exact add/multiply/FMA/FAA fallbacks after the Float128, `Sticky`, and (since
  step 4) the Float64 proofs decline. The exact result can need more than 113
  bits or a wider exponent span.
- Rung-3 transcendental evaluation from `Dyadic`, and any operation on an
  external `BigFloat`.
- The finite block-sum/dot/product fallbacks at their derived precision. The
  `Dyadic` routes added in step 8 already cover the homogeneous Float64 case;
  this is what runs when they decline.
- Projection of a `BigFloat` not first proved exactly representable as
  `Float128`.
- Integral `Exp2` when the exact power lies outside the Float128 finite range.

### Rejected on measurement

**§4, the mixed `_samecarrier` join.** A Float64 does widen to Float128 exactly,
so the eight added methods were sound. They were also a net loss: they widened
`_samecarrier`'s inferred return at the generated `Block*`/`Scaled*` call sites,
and `ScaledAdd` went **192 → 312 ns and 7 → 15 allocations** with no measurable
gain anywhere — the mixed reduction that motivated the item does not call
`_samecarrier` at all. This plan's own warning ("avoid a broad implementation
until inference has been measured") turns out to apply just as well to a spray
of narrow methods. The rejection is recorded at the call site in `blocks.jl`.

### Deferred — a proof and a benchmark would have to come first

- **No `_fq1`/`_fq2` shortcuts for Float128 transcendental inputs** on
  differential evidence alone. The Float64 estimator envelopes
  (`_F64_RELEXP`, `_F128_RELEXP`) are calibrated constants; agreement between
  libquadmath and MPFR is evidence, not an error bound for binary128.
- **No wholesale replacement of `BlockReduceMultiply`'s accumulator.**
  Successive products consume the 113-bit significand quickly — the same
  arithmetic that keeps it on `BigFloat` after step 8, where `mul_dy`'s
  `nbits ≤ 96` precondition fails almost immediately at B = 16. Revisit only
  behind hit-rate instrumentation.
- **No general `BigFloat -> Float128 -> project` shortcut** until the
  exact-representability check is itself measured. Scanning a wide MPFR
  significand can cost more than the projection it avoids.
- **Not combined with a `BigExactF` result protocol.** That is an architectural
  change and would blur the attribution of every number above.

## Internal design

### 1. "Try exact, otherwise decline" is the seam

Narrow helpers returning a concrete `Float128` or `nothing`:

```julia
_try_div128(x, y)  -> Union{Float128,Nothing}
_try_recip128(x)   -> Union{Float128,Nothing}
_try_sqrt128(x)    -> Union{Float128,Nothing}
```

`nothing` is not an error; it means the caller runs the unchanged MPFR path.
Special-value algebra stays in the caller so each helper assumes finite,
domain-valid, nonzero operands. This refusal interface is easier to audit than
one generic "fast oracle" holding every operation's proof rules. Julia
union-splits a two-case result, but `@code_warntype` and allocation assertions
at the public call sites are still required.

Prove each candidate with `fma128` against an explicitly derived Float128
residual floor:

- division `q`: `q*y - x == 0`
- reciprocal `q`: `q*x - 1 == 0`
- square root `s`: `s*s - x == 0`
- reciprocal square root: prove the root and the reciprocal separately

**The floor is mandatory, and this is not hypothetical.** An FMA returning zero
is not a proof of exactness when the true residual can underflow to zero.
Step 4 shipped exactly this bug in review and it was caught by a written test
assertion, not by reading: for Float64, `fma(x, y, -p) == 0` only proves
`p == x·y` above `|p| ≥ 2^-915`, because a nonzero residual satisfies
`|d| ≥ |x·y|·2^-106` and that bound must clear `floatmin`.

Derive the Float128 analogue the same way — from precision 113, the maximum
exact product width 226, and binary128's normal/subnormal exponent limits — and
**write the inequality beside the constant**, as `_FMA_EXACT_FLOOR` does. Do not
scale the Float64 constant and do not accept an empirical value. Test the binades
immediately either side of it.

If that conservative floor turns out to reject a material share of useful
candidates, the *next* design — not the first — is to have `Float128FMA` report
whether the exact residual is zero before rounding. That removes the underflow
caveat but changes vendored arithmetic and needs new golden tests.

### 2. Test integer representability, not magnitude

A bound like `abs(x) <= 2^113` is safe but rejects `2^10000`, which is exactly
representable. For nonzero `x`:

```text
nbits   = bit length of |x|
sigbits = nbits - trailing_zeros(x)
e       = nbits - 1
```

Exact in Float128 when `sigbits <= 113` and `e <= exponent(floatmax(Float128))`;
zero is exact separately. The predicate must work for signed native integers,
`typemin`, `UInt128`, and `BigInt` without narrowing first. Order the gates
cheapest-first: the existing Float64 gate, then this predicate, then the
derived-precision `BigFloat` construction.

Tests: `2^53 ± 1`, `typemin(Int64)`, `typemax(UInt64)`, a value at exactly 113
significant bits, a 114-bit odd significand that must decline, powers of two
inside and outside the Float128 exponent range, and negative counterparts.

### 3. Exact constants in their natural carrier

For `C <: AbstractFloat`, no decimal literal and no division:

```julia
half    = ldexp(one(C), -1)
quarter = ldexp(one(C), -2)
```

Signs via `copysign` or unary minus. `Log2` of a carrier power of two may return
`C(exponent(x))`: every relevant Float64 or Float128 exponent is a small exactly
representable integer. This preserves the incoming carrier and removes both the
MPFR setup and the ambient-precision question.

`Exp2` differs — its exact answer can exceed the input carrier's range while
still mattering to a wider result format. Choose the narrowest fixed carrier in
which `ldexp(one(T), n)` is finite, nonzero when mathematically nonzero, and
exact: try Float64, then Float128, then the exact `BigFloat`. Test the minimum
subnormal power and maximum finite power for each carrier plus one exponent
either side. Never infer safety from the carrier of `x`.

### 4. Join only the provably exact mixed pair

Add explicit two- and three-argument `_samecarrier` methods for Float64/Float128
mixtures, each widening the Float64 operands. Avoid a vararg or abstract-union
implementation until inference is measured. Homogeneous methods stay; the
catch-all keeps calling `_exactbig` for wider combinations.

Deliberately smaller than changing the carrier lattice. `_samecarrier` is a
block-operation adaptation seam; public promotion and `datumcarrier` express
different contracts and stay separate.

### 5. Reuse the Dyadic conversion that already exists

Replace `heads.jl:120` with `DyadicNumbers._dyadic_to(Float128, x)`. Its exact
normal-range branch avoids MPFR; its BigFloat fallback handles subnormal
rounding and the range boundary with one rounding. Do not duplicate `_exact_in`,
and do not broaden it to subnormals here.

### 6. Float128 filters at the block boundaries

`_bp_element`: harmonize a finite `res` and a finite nonzero scale to Float128
only when both convert exactly, take the quotient only when the residual proof
accepts, and otherwise call the existing directed `_encl_div_scale`. No
approximate quotient may reach `project`.

`ConvertToBlockMaxAbsFinite`: decode once, take exact absolute values, select a
homogeneous fold carrier, seed with that carrier's NaN. Mixed Float64/Float128
joins at Float128; rung-3 and unsupported mixtures keep the exact fallback.
Because `MaximumFinite` selects an operand rather than combining significands,
the fold consumes no precision — this is the cheapest large win in the table.

Block reductions: replace BigFloat-only NaN/∞/zero construction first; their
classification and sign are exact in Float64 or Float128. Leave finite
accumulation alone — step 8 already routes the homogeneous case through
`Dyadic`, and the mixed case is item 2's job. Any later exact-Float128 fold must
prove *every* multiply and add exact and restart from the original lanes on the
first refusal; it may never continue from a rounded partial accumulator.

## Implementation sequence

Each step is a separately reviewable change with tests and a Chairmarks
comparison before the next begins.

1. **Baseline.** Add the benchmark rows named below to `benchmark/scalar.jl` and
   `benchmark/arrays.jl`, recording the environment the harness already prints.
   Run the full suite before editing.
2. **Exact leaves** (P1). Carrier-native constants, integral `Exp2`, exact
   integer conversion, `Float128(::Dyadic)`. Independent of each other, simplest
   proofs, and the ones that remove a measured inversion.
3. **Mixed block carrier join** (P2). Only the explicit Float64/Float128
   `_samecarrier` methods. Update the existing test that requires mixed `Add` to
   return `BigFloat`: it should compare the value and the projection, not
   preserve an internal return type.
4. **Maximum-finite fold and special rows** (P2). Verify all-NaN,
   all-infinity, mixed-special, signed-zero, and stochastic cases.
5. **Float128 scalar proofs** (P3). The residual floor and the `_try_*128`
   helpers, then `Divide`, `Recip`, `Sqrt`, `RSqrt`. Keep the MPFR branches
   textually intact as the refusal path.
6. **Block quotient proof** (P3). Reuse the scalar helper in `_bp_element`.
   Measure the public `Block*`/`Scaled*` operations: a fast private helper is
   irrelevant if tuple boxing or block projection dominates.
7. **Optional reduction experiment.** Instrument acceptance without changing
   results; implement only if the gates below pass.
8. **Final audit.** Re-grep `src/` for `BigFloat`, classify every remaining
   occurrence here, run the suite under several ambient BigFloat precisions,
   and record measured results in `docs/checkpoint.md`.

## Gates

Applies to every step; the performance gate applies to steps 2–7.

**Correctness**

- Compare final `codepoint` against the forced existing BigFloat/MPFR route for
  every projection in the registry, not only round-to-nearest.
- Exhaust small formats over their complete code space where feasible; cover
  representative rung-1, rung-2, and rung-3 formats, signed and unsigned, finite
  and extended.
- For stochastic projections pass identical explicit `R` to both routes. Never
  compare two independently advanced RNGs.
- Test accepted and forced-refusal cases separately. Boundaries must cover
  overflow, the normal/subnormal transition, cancellation, signed zero, NaN,
  both infinities, and maximum exponent spread.
- Validate the integer predicate independently: whenever it accepts, compare the
  Float128 value as an exact rational against the original integer.
- Run under several ambient `BigFloat` precisions (64, 113, 256, 4096). Results
  must not depend on ambient precision.
- Preserve and extend the `Float128FMA`/`Float128FAA` golden and randomized
  tests if their proof machinery is touched.
- `@inferred`/`@code_warntype` at the new refusal seams; allocation assertions
  only on warmed hot paths. Do not encode incidental carrier types in public
  behavior tests.
- Full `Pkg.test()` after each step and again after the final audit.

**Performance**

Rows to add: integer conversion at `2^53 + 1`, `typemax(Int64)`, an exact
`Int128`, an in-range exact `BigInt` power of two, and a deliberately inexact
`BigInt`; the `Log2`/`Exp2`/`ArcSinPi`/`ArcCosPi`/`ArcTanPi`/`ArcTan2Pi` exact
rows each with a neighbouring non-exact control; rung-2 exact and inexact
`Divide`/`Recip`/`Sqrt`/`RSqrt`; mixed Float64/Float128 block element
operations; `_bp_element` through public `BlockAdd`/`ScaledDivide`/conversion
calls with exact and refusing quotients; `ConvertToBlockMaxAbsFinite` at B = 16
and B = 32 for rungs 1 and 2.

At least five independent processes after warm-up; compare medians; record time
and allocations, and elements per second for throughput rows. **A change is
noticeable only if the public operation is at least 20% faster or removes an
allocation, with no more than a 5% median regression on its refusal control.**
Below that, the extra proof surface is not worth it unless the code simplifies.

For the optional block-product work, count acceptances in a throwaway branch,
not in production state. Proceed only if at least half of the intended real
workload reaches the exact Float128 result *and* the end-to-end operation meets
the 20% gate. Synthetic powers of two do not justify the path.

## Why the plan looks like this

The first pass proposed replacing `BigFloat` construction broadly and using
FMA-zero tests wherever a Float128 candidate looked plausible. Review and then
measurement corrected it:

- Exact halves, quarters, integers, zeros, and infinities belong in the natural
  carrier; forcing Float128 everywhere is itself unnecessary widening.
- Integer eligibility is significant bits after removing trailing zeroes, not an
  absolute-magnitude cutoff.
- Integral `Exp2` needs an exponent-range test, because a narrow input can have
  an exact result visible only to a wider output format.
- An FMA result of zero needs a proven underflow guard. Step 4 shipped this bug
  and a test caught it; the same mistake in Float128 would be found the same way
  or not at all.
- Mixed Float64/Float128 joining is safe; replacing the catch-all is not, because
  wider exact results and enclosures still occur.
- libquadmath/MPFR agreement is evidence, not a transcendental error bound, so
  Float128 estimators stay deferred.
- Block multiplication is not an initial target; it is an optional, hit-rate
  gated experiment.
- **Measurement then reordered the list.** The exact peels were a low-priority
  tidy-up until the controls showed them running 17–24x slower than the general
  path they shortcut, and `ConvertToBlockMaxAbsFinite` (17 µs, 1067 allocations)
  and the mixed-carrier reduction (29x its homogeneous twin) turned out to
  dominate everything the original ordering put first.

An earlier exploratory comparison — four formats across all three rungs, all 27
projections, exact quarter values — produced 972/972 identical Float128-versus-
BigFloat projections. That supports the exact-value peels; it does not substitute
for the operation-specific gates above.

## Completion criteria

Complete when the prioritized steps pass their gates, every retained `BigFloat`
in the affected paths has a documented reason, the full suite passes, benchmark
results are recorded with their environment, and no public operation,
projection, special-value rule, or stochastic result has changed. Optional steps
that fail their gates are removed cleanly and recorded as rejected experiments
rather than left as dormant complexity.
