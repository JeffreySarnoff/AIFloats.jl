# Plan for replacing avoidable `BigFloat` work with `Float128`

## Purpose

This plan covers places in `src/` where a value currently reaches `BigFloat`
but can sometimes remain in `Float128` without changing any AIFloats result.
The goal is lower latency and fewer allocations, not the removal of
`BigFloat`. MPFR remains the correctness oracle and the required fallback for
unbounded exponents, values wider than 113 significant bits, and rigorous
transcendental enclosures.

The governing invariant is:

> A fixed-width carrier may replace `BigFloat` only when the carried value is
> exact, or when it is used solely as a non-authoritative enclosure estimate.

This is stricter than checking that the final format has at most 16 precision
bits. Rounding an inexact intermediate to `Float128` and then projecting it can
double-round, including under directed and stochastic projections. Every fast
route below must therefore either prove exactness or decline to the existing
`BigFloat` path.

No public API change is needed. The implementation should deepen the existing
carrier/oracle boundary with small internal, proof-oriented helpers and keep
all projection policy in `project`/`project_interval`.

## Findings and decisions

### Use `Float128` or a still narrower exact carrier

| Location | Present behavior | Correct replacement | Priority |
|---|---|---|---|
| `ops/scalar.jl`, `Convert(::Integer)` | Integers outside `[-2^53,2^53]` always become `BigFloat` | Use `Float128` when the integer is exactly representable; otherwise retain the derived-precision `BigFloat` route | 1 |
| `ops/oracle.jl`, exact `Log2` and pi-scaled inverse-trig peels | Exact integers, halves, and quarters are constructed as `BigFloat` | Construct the result in the input carrier with `one(C)`, `ldexp`, and sign operations | 1 |
| `ops/oracle.jl`, integral `Exp2` peel | Every exact power of two is built as `BigFloat` | Return `Float64` or `Float128` only when that power is finite and exact in the chosen carrier; use `BigFloat` outside its exponent range | 1 |
| `carriers/heads.jl`, `Float128(::Dyadic)` | Always converts through `BigFloat` | Delegate to `DyadicNumbers._dyadic_to(Float128, x)`, whose exact normal-range route uses `ldexp` and whose boundary fallback already preserves one rounding | 1 |
| `arrays/blocks.jl`, `_samecarrier` | A mixed `Float64`/`Float128` lane tuple is lifted to `BigFloat` | Add exact mixed methods that widen only the `Float64` operands to `Float128`; retain the catch-all `BigFloat` join | 2 |
| `arrays/blocks.jl`, `ConvertToBlockMaxAbsFinite` | Every absolute value and the NaN seed are eagerly lifted to `BigFloat` | Fold in the homogeneous decoded carrier; join only mixed `Float64`/`Float128` inputs at `Float128`, and retain the exact-carrier/`BigFloat` fallback | 2 |
| `ops/oracle.jl`, `Divide`/`Recip`/`Sqrt`/`RSqrt` on `Float128` | Goes directly to an MPFR enclosure after special cases | Accept a `Float128` result only after an exact residual proof; otherwise use the current ladder | 3 |
| `arrays/blocks.jl`, `_bp_element` | Only a Float64 exact quotient avoids a directed MPFR interval | Add the same proof-certified Float128 quotient filter before `_encl_div_scale` | 3 |
| block reduction special rows | NaN, infinity, and zero are often manufactured as `BigFloat` | Use a carrier-native special, or canonical `Float64` where only classification/sign is consumed | 3 |

### Keep `BigFloat`

The following uses are essential, not cleanup candidates:

- `_ladder1`, `_ladder2`, `_mpfr1`, `_mpfr2`, pi enclosures, and the final
  directed interval refinements. These supply certified bounds, while a
  libquadmath value supplies only an estimate.
- Exact add, multiply, FMA, and FAA fallbacks after the Float128/Sticky proofs
  decline. The exact result can require more than 113 bits or a wider exponent
  span.
- Rung-3 transcendental evaluation from `Dyadic` and any general operation on
  an arbitrary external `BigFloat`.
- The exact finite block-sum, block-dot, and block-product fallbacks at their
  derived precision. The existing Dyadic routes remain preferable where they
  apply.
- Projection of a `BigFloat` that is not first proved exactly representable as
  `Float128`.
- Integral `Exp2` when the exact power lies outside the Float128 finite range.

### Defer unless a proof and benchmark justify it

- Do not add `_fq1`/`_fq2` result shortcuts for Float128 transcendental inputs
  based only on differential testing. The existing Float64 estimator constants
  do not establish a libquadmath error bound for binary128 inputs.
- Do not replace `BlockReduceMultiply`'s finite accumulator wholesale.
  Successive products normally consume the 113-bit significand quickly. An
  exact Float128 fold may be reconsidered only after hit-rate instrumentation
  on representative blocks shows that it reaches `_finish` often enough to
  repay its guards.
- Do not add a general `BigFloat -> Float128 -> project` shortcut until the
  exact-representability check itself is measured. Scanning a wide MPFR
  significand can cost more than the projection it is intended to avoid.
- Do not combine this work with a deferred `BigExactF` result protocol. That is
  a broader architectural change and would make the performance attribution
  unclear.

## Internal design

### 1. Make “try exact, otherwise decline” the seam

Use narrow helpers returning either a concrete `Float128` or `nothing`:

```julia
_try_div128(x, y)  -> Union{Float128,Nothing}
_try_sqrt128(x)    -> Union{Float128,Nothing}
_try_recip128(x)   -> Union{Float128,Nothing}
```

`nothing` is not an error; it means that the caller must run the unchanged
MPFR path. Keep special-value algebra in the caller so each helper can assume
finite, domain-valid, nonzero operands. This small refusal interface is easier
to audit than one generic “fast oracle” containing operation-specific proof
rules. Julia can union-split this two-case result, but `@code_warntype` and
allocation measurements are still required at public call sites.

The first implementation should use an explicitly derived Float128 residual
magnitude floor, analogous to `_FMA_EXACT_FLOOR` for Float64, and `fma128`:

- division candidate `q`: prove `q*y - x == 0`;
- reciprocal candidate `q`: prove `q*x - 1 == 0`;
- square-root candidate `s`: prove `s*s - x == 0`;
- reciprocal square root: separately prove the square root and reciprocal.

The floor is mandatory. A zero returned by an FMA is not an exactness proof if
a nonzero mathematical residual could underflow to zero. Derive the constant
from binary128 precision (113), the maximum exact product width (226), and the
normal/subnormal exponent limits; document the inequality beside the constant
and test the binades immediately on both sides. Do not copy the Float64
constant or accept an empirical value.

If this conservative floor rejects a material fraction of useful candidates,
the next design—not the first one—is to refactor `Float128FMA` so its existing
integer product/add core can report whether the exact residual is zero before
rounding. That would remove the underflow caveat, but it increases risk in a
vendored arithmetic module and needs new golden tests.

### 2. Test integer representability, not merely magnitude

The Float128 integer gate must account for trailing binary zeroes. A bound such
as `abs(x) <= 2^113` is safe but unnecessarily rejects `2^10000`, which is
exactly representable. For nonzero `x`, compute:

```text
nbits   = bit length of |x|
sigbits = nbits - trailing_zeros(x)
e       = nbits - 1
```

The integer is exactly representable in Float128 when `sigbits <= 113` and
`e <= exponent(floatmax(Float128))`; zero is exact separately. The predicate
must work for signed native integers, `typemin`, `UInt128`, and `BigInt`
without first converting to a narrower signed type. Keep the current Float64
gate first because it is cheaper, then try this predicate, and finally use the
current derived-precision `BigFloat` construction.

Tests must include `2^53 ± 1`, `typemin(Int64)`, `typemax(UInt64)`, values at
113 significant bits, a 114-bit odd significand that must decline, large
powers of two inside and outside Float128's exponent range, and their negative
counterparts.

### 3. Keep exact constants in their natural carrier

For `C <: AbstractFloat`, halves and quarters can be expressed without a
decimal literal or division:

```julia
half = ldexp(one(C), -1)
quarter = ldexp(one(C), -2)
```

Apply signs with `copysign` or unary minus. `Log2` of a carrier power of two
may return `C(exponent(x))`: every relevant Float64 or Float128 exponent is a
small exactly representable integer. This preserves the incoming carrier and
removes both MPFR setup and ambient-precision questions.

`Exp2` differs because its exact answer can exceed the input carrier's range
while still mattering to a wider result format. Choose the narrowest fixed
carrier in which `ldexp(one(T), n)` is finite, nonzero when mathematically
nonzero, and exact. Try Float64, then Float128, then construct the exact
`BigFloat`. Test the minimum subnormal power and maximum finite power for each
fixed carrier, plus one exponent on either side. Never infer safety merely
from the carrier of `x`.

### 4. Join only the mixed pair that is provably exact

Add explicit two- and three-argument `_samecarrier` methods for mixtures of
`Float64` and `Float128`; each converts the Float64 operands to Float128.
Avoid a broad vararg or abstract-union implementation until inference has been
measured. The existing homogeneous methods remain, and the generic catch-all
continues to call `_exactbig` for the other wider carrier combinations it
currently supports.

This is deliberately smaller than changing the global carrier lattice.
`_samecarrier` is a block-operation adaptation seam; public promotion and
`datumcarrier` already express different contracts and should remain separate.

### 5. Reuse the Dyadic conversion module

Replace the Float128 method in `carriers/heads.jl` with a qualified call to
`DyadicNumbers._dyadic_to(Float128, x)`. Its exact, normal-range branch avoids
MPFR, while its existing BigFloat fallback handles subnormal rounding and
range boundaries with one rounding. Do not duplicate `_exact_in`, and do not
broaden it to subnormals as part of this change.

### 6. Apply Float128 filters at block boundaries

For `_bp_element`, harmonize a finite `res` and finite nonzero scale to
Float128 only when both convert exactly. Try the quotient and project it only
when the residual proof accepts it. Otherwise call the existing directed
`_encl_div_scale`; no approximate quotient may reach `project` directly.

For `ConvertToBlockMaxAbsFinite`, avoid mapping every value through
`_exactbig`. Decode once, take exact absolute values, select a homogeneous fold
carrier, and seed with that carrier's NaN. A mixed Float64/Float128 tuple joins
at Float128. Rung-3 or otherwise unsupported mixtures retain the exact
fallback. Since `MaximumFinite` selects an operand rather than combining
significands, no precision is consumed by the fold.

For block reductions, first replace BigFloat-only NaN/infinity/zero
construction: their classification and sign are exact in Float64 or
Float128. Leave finite accumulation unchanged in the initial patch. A later
experimental `_try_product128` or Float128 dot route must prove every multiply
and every add exact and restart from the original lanes on the first refusal;
it may not continue from a rounded partial accumulator.

## Implementation sequence

Each step should be a separately reviewable change with tests and a Chairmarks
comparison before proceeding.

1. **Freeze the oracle and baseline.** Add focused benchmark rows and record
   Julia version, Quadmath version, CPU, thread count, minimum time, median
   time, and allocations. Run the full suite before editing.
2. **Exact leaves.** Change carrier-native constants, integral `Exp2`, exact
   integer conversion, and `Float128(::Dyadic)`. These are independent and
   have the simplest value proofs.
3. **Mixed block carrier join.** Add only the explicit Float64/Float128
   `_samecarrier` methods and update the existing test that currently requires
   mixed `Add` to return `BigFloat`; correctness tests should compare the
   value/projection, not preserve an obsolete internal return type.
4. **Maximum-finite fold and special rows.** Remove eager BigFloat conversion
   from `ConvertToBlockMaxAbsFinite` and use fixed-carrier special values in
   reductions. Verify all-NaN, all-infinity, mixed-special, signed-zero, and
   stochastic cases.
5. **Float128 scalar proofs.** Introduce the residual floor and `_try_*128`
   helpers, then use them for `Divide`, `Recip`, `Sqrt`, and `RSqrt`. Keep the
   MPFR branches textually intact as the refusal path.
6. **Block quotient proof.** Reuse the scalar proof helper in `_bp_element`.
   Measure public `Block*`/`Scaled*` operations, because a fast private helper
   is irrelevant if tuple boxing or block projection dominates.
7. **Optional reduction experiment.** Instrument candidate acceptance without
   changing results. Implement an exact Float128 finite fold only if the
   representative hit rate and end-to-end benchmark pass the gates below.
8. **Final audit.** Search `src/` again for `BigFloat`, classify every remaining
   occurrence in this document, run all tests under multiple ambient BigFloat
   precisions, and update benchmark/checkpoint documentation with measured
   results rather than estimates.

## Correctness gates

Every implementation step must satisfy all applicable gates:

- Compare final `codepoint` results with the forced existing BigFloat/MPFR
  route for every projection in the registry, not only round-to-nearest.
- Exhaust small formats over their complete code space where feasible, and
  cover representative rung-1, rung-2, and rung-3 formats. Include signed and
  unsigned formats and finite-only and extended special-value domains.
- For stochastic projections, pass identical explicit `R` values to both
  routes. Never compare two independently advanced RNGs.
- Test exact-candidate and forced-refusal cases separately. Boundary cases must
  cover overflow, normal/subnormal transitions, cancellation, signed zero,
  NaN, both infinities, and maximum exponent spread.
- Validate the integer predicate independently by comparing the Float128 value
  as an exact rational with the original integer whenever it accepts.
- Run with several ambient `BigFloat` precisions (for example 64, 113, 256,
  and 4096 bits). Results must not depend on ambient precision.
- Preserve and extend the `Float128FMA`/`Float128FAA` golden and randomized
  tests if their proof machinery is touched.
- Use `@inferred`/`@code_warntype` at the new refusal seams and allocation
  assertions only for stable, warmed hot paths. Do not encode incidental
  carrier types in public behavior tests.
- Run `julia --project=. -e "using Pkg; Pkg.test()"` after each step and once
  more after the final source-wide audit.

The earlier exploratory projection comparison—four formats spanning all three
carrier rungs, all 27 projections, and exact quarter values—produced 972/972
identical Float128-versus-BigFloat projections. That supports the exact-value
peels, but it is not a substitute for the operation-specific gates above.

## Chairmarks plan and acceptance criteria

Chairmarks stays in `benchmark/Project.toml`; it must not become a package
dependency. Add warmed public-API rows for:

- integer conversion at `2^53 + 1`, `typemax(Int64)`, an exact `Int128`, an
  exact in-range `BigInt` power of two, and a deliberately inexact `BigInt`;
- `Log2`, `Exp2`, `ArcSinPi`, `ArcCosPi`, `ArcTanPi`, and `ArcTan2Pi` exact
  rows, with neighbouring non-exact inputs as controls;
- rung-2 exact and inexact `Divide`, `Recip`, `Sqrt`, and `RSqrt` cases;
- mixed Float64/Float128 block element operations;
- `_bp_element` through representative public `BlockAdd`, `ScaledDivide`, or
  conversion calls with exact and refusing quotients;
- `ConvertToBlockMaxAbsFinite` at B = 16 and B = 32 for rung 1 and rung 2;
- any optional block-reduction experiment, split by accepted and refused
  candidates.

Run at least five independent benchmark processes after warm-up and compare
medians. Record time and allocations; throughput rows should also report
elements per second. A change is “noticeable” only if the public operation is
at least 20% faster or removes an allocation, with no more than a 5% median
regression on its refusal/fallback control. A result below those thresholds is
not worth extra proof surface unless it substantially simplifies the code.

For optional block-product work, add a representative acceptance counter in a
throwaway benchmark branch, not production state. Proceed only if at least
half of the intended real workload reaches the exact Float128 result and the
end-to-end operation meets the same 20% gate. Synthetic powers-of-two alone do
not justify the path.

## Review of the plan and resulting improvements

The first-pass idea was to replace hard-coded `BigFloat` construction broadly
and to use FMA-zero tests wherever a Float128 candidate looked plausible. That
was not safe or sufficiently focused. Review produced these corrections:

- Exact halves, quarters, integers, zero, and infinities should be built in the
  natural carrier; forcing Float128 everywhere would itself be unnecessary
  widening.
- Integer eligibility is based on significant bits after removing trailing
  zeroes, not an absolute-magnitude cutoff.
- Integral `Exp2` needs an exponent-range test because a narrow input can have
  an exact result visible only to a wider output format.
- An FMA result of zero needs a proven underflow guard before it certifies an
  exact product or quotient.
- Mixed Float64/Float128 joining is safe; general replacement of the catch-all
  join is not, because wider exact results and enclosures still occur.
- Differential libquadmath/MPFR agreement is evidence, not a transcendental
  error bound, so Float128 transcendental estimators remain deferred.
- Existing measurements and precision-growth analysis argue against making
  block multiplication an initial target; it is now an optional, hit-rate-
  gated experiment.

This revised order captures low-risk allocation wins first, centralizes the
new correctness proofs, preserves the MPFR oracle at every refusal point, and
makes each later optimization contingent on an end-to-end Chairmarks result.

## Completion criteria

The work is complete when the prioritized steps pass their correctness and
performance gates, every retained `BigFloat` occurrence in the affected paths
has a documented reason, the full suite passes, benchmark results are recorded
with their environment, and no public operation, projection, special-value
rule, or stochastic result has changed. Optional steps that fail their gates
should be removed cleanly and recorded as rejected experiments rather than
left as dormant complexity.
