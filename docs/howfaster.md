# Detailed approach to making AIFloats faster

## Purpose

This is the implementation playbook for `docs/faster.md`. It turns each
performance hypothesis into a repeatable sequence:

> characterize → benchmark → prove → implement behind a refusal path →
> differential-test → remeasure → keep or remove.

The existing scalar oracle, exact carrier paths, and MPFR ladders remain live
as references. Optimization tests should observe public code points and
documented side effects; internal carrier types are not public behavior.

## Enactment record — 2026-08-31

The first implementation pass has been completed on top of `81a7efb`. The
accepted changes are:

- truthful eager/adaptive/cached/refused `table_policy` reporting, including a
  prospective `nelems` without mutating the use counter;
- one exact allocation-free binary128 bit adapter used by Float128 projection;
- exact value-sensitive Float128-to-Float64 narrowing immediately before
  evaluation, with the original Float128 path as refusal;
- the default-saturation speculation guard for all Base integer-rounding
  veneers;
- direct identity-scale `ScaledOp` and `BlockOp` adapters;
- exact Float128 quotient reuse in block projection;
- exact Dyadic add/product reduction adapters for wider finite block lanes;
- named convenience operations and allocating `sort` in the precompile
  workload; and
- benchmark rows for carrier acceptance/refusal, Base rounding, and wider
  block reductions.

On the reference i9-14900K with Julia 1.12.6 and four threads, five sequential
fresh-process Chairmarks samples gave these medians:

| Path | Before | After |
|---|---:|---:|
| Float128 projection | about 54 ns | 10.8 ns |
| K=16 rung-2 Add | 132.6 ns | 40.0 ns |
| K=16 rung-2 Multiply | 419 ns | 40.6 ns |
| K=16 rung-2 Exp | 2004 ns, 62 allocations | 112.8 ns, 2 allocations |
| `round(x)` | 170–250 ns, 2 allocations | 7.6 ns, 0 allocations |
| unit-scale `ScaledAdd` | 141.3 ns, 7 allocations | 9.7 ns, 0 allocations |
| unit-scale `BlockAdd`, B=16 | 670–780 ns, 22 allocations | 140.1 ns, 0 allocations |
| first named Add/Exp/Log | 6–8 ms each | about 0.01 ms each |

The established K=8/K=12 scalar, table, packed, and threaded-array controls
remain essentially unchanged. The full focused differential suites passed,
including 110,605 binary128 projection comparisons and 6,990 evaluation
narrowing comparisons.

Two experiments were removed under the stop rules:

- the wider exact dot-product branch was correct but added 480 bytes to the
  existing rung-1 zero-allocation path; and
- type-specific `convert` methods measured 7.6 ns versus the existing roughly
  7.2 ns and therefore supplied no useful gain.

Binary-cache widening, scheduling/packed rewrites, and MultiFloats integration
were not promoted. The current evidence does not justify the added memory or
implementation complexity, and MultiFloats still lacks a locally established
outward-enclosure proof for this use. They remain experiments gated by the
criteria below, not unfinished correctness work.

## 1. Establish a reproducible baseline

Run from the repository root on a clean tree:

```bash
julia --project=benchmark -t 4 benchmark/runbenchmarks.jl scalar arrays
julia --project=benchmark -t 4 benchmark/runbenchmarks.jl latency
julia --project=. -e 'using Pkg; Pkg.test()'
```

The generated HTML currently records commit `026a468`; current work begins at
`81a7efb`. Preserve both reports. Do not overwrite the published baseline and
then compare against memory.

For each candidate, run at least five fresh benchmark processes. Record:

- commit and dirty state;
- Julia, package, and Quadmath versions;
- CPU, thread count, and thread pool;
- projection and mutable performance-policy settings;
- operand format and population construction;
- cache state (cold, earned, or warm);
- time, allocations, bytes, throughput, and candidate acceptance count; and
- minimum/median across processes.

Chairmarks operands must be interpolated. Warm compilation separately from
the operation being sampled. Latency probes remain fresh-process wall-clock
measurements because compilation happens once and is not a sampled steady
state.

### Harness additions

Add benchmark rows in small groups so a regression has an owner:

1. `scalar-carriers`: rung 1/2/3, exact and refusal controls, carrier
   conversion and projection.
2. `scalar-base`: `round`/`floor`/`ceil`/`trunc`, explicit `round` modes,
   `convert` input families, default and changed session saturation.
3. `arrays-sizes`: N = 64, 128, 256, 1024, 4096, 65536 at one and four threads.
4. `arrays-populations`: convenient values, uniform code points, finite-only,
   exponent-stratified, specials, and a recorded application-like population.
5. `blocks`: B = 1, 16, 32; unit/power-of-two/general scales; homogeneous and
   mixed rungs; finite and special lanes.
6. `tables-sequence`: first call, earning calls, build call, warm calls, total
   elapsed, cache bytes, and eviction.

Add an optional structured output beside the existing text. Do not make the
human-readable documentation depend on a plotting package.

### Repair performance introspection

Before tuning tables, make `table_policy` report the policy actually used by
the `table_for(..., nelems)` kernel path. It should distinguish:

- eager and present;
- adaptive but not yet earned, including cumulative use and threshold;
- adaptive and cached;
- over adaptive band;
- over byte budget; and
- stochastic refusal.

Keep its current interface if possible by improving the returned named tuple;
avoid a second public policy function unless callers genuinely need a different
question answered.

## 2. Use one exact binary128 representation seam

### Interface

Place binary128 layout knowledge in one internal module or one tightly grouped
section, preferably near `carriers/heads.jl` where external carrier conversion
already lives. Its interface should be no larger than:

```julia
_dyadic128(x::Float128) -> Dyadic
_try_f64_exact(x::Float128) -> Union{Float64,Nothing}
```

The implementation may share a private decomposition helper. Callers should
not know sign masks, exponent bias, implicit-bit rules, or subnormal layout.
The deletion test applies: without this module, those details would otherwise
reappear in projection, scalar evaluation, and blocks.

### Exact decomposition

For `u = reinterpret(UInt128, x)`:

1. read the sign bit, 15-bit biased exponent, and 112-bit fraction;
2. handle zero, infinity, and NaN explicitly;
3. add the implicit bit for normal values;
4. use exponent `biased - 16383 - 112` for normals and `-16494` for
   subnormals;
5. remove trailing zeroes from the significand and add them to the exponent;
6. apply sign; and
7. construct `Dyadic(S,Q)`.

The maximum finite significand is 113 bits, so it fits `Int128`. This path uses
no Quadmath function and performs no rounding.

For the first `_try_f64_exact` implementation, be conservative: accept only
normal Float64 results whose significant-bit count and exponent fit, and build
the Float64 bits directly. Refuse subnormal candidates until their bit assembly
and boundary proof are separately reviewed. A refusal loses speed, never
correctness.

### Tests

- Hand-check ±0, minimum/maximum subnormal, minimum normal, one, adjacent to
  one, maximum finite, ±Inf, and NaN.
- Compare exact rationals for all decoded values of representative rung-2
  formats and randomized raw finite UInt128 patterns.
- Assert `_try_f64_exact` accepts iff its returned Float64 converted to an
  exact rational equals the original; do not use a Float128 function round trip
  as the oracle.
- Preserve the package's single-zero semantics at projection and operation
  interfaces even though the carrier has signed zero.
- Run JET and `@code_warntype`; both helpers must remain allocation-free.

### Quadmath prohibition

Do not add `exp(Float128)`, `log(Float128)`, `sin(Float128)`, or another
Quadmath function to this module. Do not infer a correctness bound from
agreement on random samples. If a Float128 estimator is ever proposed, its
error enclosure must be justified independently and tested as containment,
not equality.

## 3. Make Float128 projection fixed-point

Change only the Float128 adapter to `round_to_precision`:

1. peel NaN, infinity, zero, and sticky-special rows exactly as now;
2. convert the finite value with `_dyadic128`;
3. call `_rtp_dyadic`; and
4. keep `_rtp_core(..., ::Float128, ...)` available under a test-only helper or
   local reference until the differential gate is complete.

Do not duplicate the rounding-mode predicates. The purpose is to reuse the
deep fixed-point rounding module already shared by Float64 bits and Dyadic.

Differential gate:

- every rounding mode, saturation mode, and relevant `R`;
- sticky = -1, 0, +1;
- every code of representative formats across exponent biases;
- raw Float128 boundary/random samples; and
- identical `Rounded` fields or final code points against `_rtp_core`.

Performance gate: benchmark `project` directly and public rung-2 Add,
Multiply, Divide, exact peels, and refusal paths. The exploratory target is
roughly 54 → 9 ns for direct projection, but acceptance depends on repeated
process medians and downstream benefit.

## 4. Add exact value-sensitive evaluation narrowing

### Placement

Put the seam immediately before `ωeval` in `apply_op`, not in `decode`.
`decode` has a valuable concrete return type determined by the format; making
it value-dependent would spread unions through every caller.

Implement arity-specific internal methods:

```julia
_eval_narrow(op, x::Float128)
_eval_narrow(op, x::Float128, y::Float128)
_eval_narrow(op, x::Float128, y::Float128, z::Float128)
```

Each tries `_try_f64_exact` on every finite operand. All accept: call the same
`ωeval(op, ...)` with Float64 values. Any refusal: call the unchanged Float128
method. Special values should initially retain their current methods; they are
already cheap and complicate NaN/sign rules unnecessarily.

The Float64 evaluator is allowed to return Float128, `Sticky`, `Enclosure`, or
BigFloat. Narrowing the inputs does not narrow the result contract and does not
skip its existing exactness/refusal logic.

### Correctness gate

- Exhaust every operation over small complete code spaces and representative
  rung-2 unary populations; use stratified/random subsets for binary/ternary
  operations.
- Compare final code points against a flag-forced original Float128 path for
  all projections.
- For stochastic modes, pass the same explicit `R`; never compare independent
  RNG draws.
- Exercise one-accept/one-refuse mixed operands, cancellation, exponent
  extremes, subnormals, and specials.
- Confirm the ordinary Float64 enclosure stage is being reused only for an
  exactly identical input value.

### Performance gate

Report accepted and refused cases separately, plus acceptance rates for whole
code populations. The exact-conversion guard must not regress refused Add or a
cheap selection operation by more than 5%. If a universal hook penalizes cheap
ops, restrict it by measured operation group rather than adding a global cost.

## 5. Fix the Base rounding veneers

Factor one internal helper that combines a compile-time rounding mode with the
session saturation:

```julia
_project_default_sat(F, ::Val{:RTN}, exact_integer)
```

Its common branch checks `DefaultSaturationMode() === SN` and calls the literal
constant (`RTN_SN`, `RTP_SN`, and so on). Its uncommon branch constructs the
dynamic projection and preserves current behavior. Use it from:

- `round(x)`, `floor(x)`, `ceil(x)`, `trunc(x)`; and
- supported `round(x, Base.RoundingMode)` methods.

Tests must set each session saturation mode and compare with the corresponding
explicit projection, including out-of-range values where saturation matters.
Allocation assertions apply only to the untouched-default branch. Target:
remove both allocations and approach the explicit projection cost.

## 6. Deepen the exact block path

### Exact datum/lane adapter

Introduce a private exact adapter returning a concrete `Dyadic` for a decoded
finite datum regardless of its format-wide carrier:

- Float64: existing exact `Dyadic` conversion;
- Float128: `_dyadic128`;
- Dyadic: identity.

For a block lane, multiply scale and element with `mul_dy`. The individual
lane product begins with at most 32 significant bits, so document why that
operation fits. Handle NaN, infinity, and zero using the existing fold algebra
before finite accumulation.

Generalize the existing guarded reducers to concrete Dyadic tuples:

- sum: refuse on alignment or Int128-width failure;
- product: refuse before `mul_dy` exceeds its width contract;
- dot: form exact lane products, then use the guarded exact sum.

On refusal, recompute from original inputs at the current derived BigFloat
precision. Never continue from a partial accumulator that may have rounded or
discarded a tail.

Measure homogeneous rung 1 as a regression control, then rung 2, rung 3,
mixed format, wide-spread, and special populations. Keep the existing Float64
specialization if it remains faster; the new adapter is for cases that
currently fall back, not a mandate to replace a winning path.

### Identity-scale adapter

In the registry-generated `BlockOp`/`ScaledOp` implementation, test whether all
input scales and the result scale are exactly one before materializing decoded
lane tuples.

- `ScaledOp`: call the corresponding scalar operation directly.
- `BlockOp`: generate a concrete result tuple by applying the operation to
  element datums lane by lane.
- Resolve stochastic RNG state once and consume one draw per output lane in
  increasing index order.
- Fall through to the existing general pipeline for any non-unit scale.

Test every registered arity through representative operations, not just Add.
Compare identity route with forced general route for all projections and
special values. Measure B = 1, 16, 32; the primary claims are removal of
`ScaledAdd`'s seven allocations and reduction of `BlockAdd`'s intermediate
allocations.

### General block fusion, only after profiling

If allocations remain important, use allocation attribution and
`@code_warntype` to identify the exact union seam among `blockdecode`,
`_samecarrier`, `ωeval`, and `blockproject`. Prefer a concrete fast adapter with
the general pipeline as fallback. Do not add mixed `_samecarrier` methods; that
experiment was sound but already measured as a regression.

## 7. Reuse the proven Float128 quotient in block projection

For finite nonzero scale and carrier-valued result:

1. convert both values to Float128 only when the conversion is exact;
2. call `_try_div128`;
3. project a returned exact quotient; and
4. on `nothing`, call `_encl_div_scale` unchanged.

Benchmark exact powers-of-two, exact non-power-of-two quotients, inexact
quotients such as `1/96`, overflow/underflow, and wide carriers. The inexact
control must remain within the 5% regression allowance. This step is removed
if public block calls do not improve materially.

## 8. Improve sustained table throughput safely

### Measure break-even as a sequence

For each candidate signature measure:

```text
cold compute calls → threshold-crossing/build call → warm gathers
```

Calculate cumulative time relative to always computing. Record the first call
count and element count at which the table strategy wins, plus peak and retained
cache bytes.

### Bound binary cache memory before widening it

The ternary cache has aggregate LRU eviction; binary eager/adaptive tables are
currently bounded per table but not in aggregate. Give the cache module one
internal byte-budget/LRU implementation shared across result widths before
raising `TABLE_ADAPTIVE_BITS`. Preserve double-checked build-outside-lock
behavior and race correctness.

### Candidate experiments

1. Ternary ΣK=24: K=8 FMA/FAA/Clamp. A 16-MiB table must earn itself through a
   threshold derived from measured build and compute costs.
2. Binary ΣK=19–24: test each band rather than jumping to the byte ceiling.
3. Operation-sensitive thresholds only if one global threshold demonstrably
   leaves large value across several workloads; avoid a cost-class interface
   based on one CPU.

Correctness is table-versus-scalar codepoint equality over every table entry.
Concurrency tests must cover duplicate builders, eviction across UInt8/UInt16
result caches, and `empty_tables!` resetting all use counters. Stochastic
projections remain an unconditional refusal.

## 9. Fix first-call latency at the called interface

Add to the precompile workload the exact forms measured by `latency.jl`:

- `Add(a,b)`, `Exp(a)`, and `Log(a)`;
- allocating `sort([a,b,a])`; and
- any new internal adapter reached by the standard rung-2 profile.

Run latency in fresh processes before and after. Also record `using AIFloats`,
precompile time, pkgimage size, and invalidations if available. Keep the change
only if the named calls become sub-millisecond and package load does not regress
materially. Do not add hundreds of format instances; precompile one standard
format per genuinely different method shape.

## 10. Run a proof-gated MultiFloats experiment

Do not add MultiFloats to `Project.toml` at the start. Put the experiment in a
temporary benchmark environment so a negative result leaves no runtime,
precompile, or dependency cost. Test the current supported Float64 expansions,
principally `Float64x2` and `Float64x4`; do not describe them as binary128 or
binary256. Use the guarantees and limitations documented by the
[MultiFloats repository](https://github.com/dzhang314/MultiFloats.jl) and its
[formal error analysis](https://theory.stanford.edu/~aiken/publications/papers/sc25.pdf),
not observed agreement, as the starting point.

The only admissible integration shape is an optional internal estimator:

```julia
_try_multifloat_enclosure(op, original_args...) -> Union{Nothing,Enclosure}
```

It must refuse special values, unsupported exponent ranges, and any operation
for which the published bound has not been translated into an outward-rounded
enclosure in an exact carrier. `nothing` invokes the current path from
`original_args`; an expansion value is never projected directly. Explicitly
test noncanonical normalized representations and the library's documented
infinity behavior. Do not experiment with transcendental functions first:
MultiFloats routes them through MPFR, so that is not a new low-cost oracle.

Benchmark three layers with Chairmarks:

1. raw MultiFloats arithmetic versus the current Float128 and MPFR operation;
2. arithmetic plus certified enclosure construction; and
3. the public AIFloats operation including acceptance tests, projection, and
   refusal.

Use stratified ordinary-range values, cancellation cases, and exponent/special
refusals. Report acceptance rate, median time, allocations, and containment
failures separately for `+`, `-`, `*`, `/`, and `sqrt`. Differential tests must
compare enclosure containment and final code points across all deterministic
rounding and saturation modes; equality on random samples is insufficient.

Promote the experiment only when its proof obligations fit behind the one
helper, the accepted public path is at least 20% faster, refusal costs at most
5%, and no supported range or special case changes. Otherwise preserve the
benchmark result in the review notes and remove the experimental dependency.
In either outcome, keep the exact bit-level Float64 narrowing work ahead of
this experiment.

## 11. Conditional micro-optimizations

### `convert`

Add type-specific float input methods only if ambiguity tests remain clean.
Use the constructor's default-projection speculation pattern and compare with
explicit `Convert`. This is a low absolute-time change and follows the larger
work.

### Thread scheduling

Compare current scheduling with `:static` over the size/thread matrix. Include
MPFR-backed operations because task-local precision is a correctness
requirement on Julia 1.12. Keep stochastic loops sequential. Do not optimize
away the scheduler's fixed allocations at the cost of lower throughput.

### Packed storage

Profile before editing. Boundary lengths around `_safe_count`, word crossings,
K = 3:16, and tabled versus compute operations are required. Preserve the
scalar tail and `GC.@preserve`; unsafe-load changes require exhaustive boundary
tests. A platform-specific BMI2 path needs runtime feature dispatch and a
portable adapter, and is justified only by a measured end-to-end win.

## 12. Review checklist for every patch

### Semantics

- Is every accepted carrier conversion exact?
- Is any Quadmath function result being treated as correctly rounded without
  an independent proof? If yes, reject the patch.
- Is a MultiFloats expansion being mistaken for an IEEE binary128/binary256
  value, or projected without a certified outward enclosure? If yes, reject it.
- Can an FMA residual underflow and falsely report exactness?
- Is there exactly one final projection?
- Are NaN, infinity, zero sign, saturation, sticky, and stochastic rules
  unchanged?
- Does refusal execute the old path from original inputs?
- Is RNG consumption identical in count and order?

### Implementation quality

- Is the new behavior behind one internal seam with a small interface?
- Are arity/type specializations concrete and inference-clean?
- Does the fast branch avoid heap allocation at public call sites?
- Are mutable policy reads hoisted out of element loops?
- Does a cache build occur outside locks, with insertion protected?
- Are unsafe memory and bit-layout assumptions stated next to the code?
- Did the patch remove an obsolete path rather than layer permanent duplicates?

### Evidence

- Public Chairmarks row, not only a private helper?
- Accepted and refused controls?
- Multi-process median and allocation counts?
- One- and four-thread results where relevant?
- Cold/build/warm totals for a table change?
- Full differential tests, JET/Aqua, package tests, and docs build?
- Rejected experiment recorded and removed?

## 13. Commit sequence and stop conditions

Use small commits in this order:

1. benchmark coverage and `table_policy` truthfulness;
2. Base rounding speculation guard;
3. binary128 bit adapter with tests only;
4. Float128 fixed-point projection;
5. value-sensitive rung-2 evaluation;
6. exact wider block reductions;
7. identity-scale block adapter;
8. block Float128 quotient filter;
9. named-form precompilation;
10. bounded-cache/table experiments;
11. optional, benchmark-environment-only MultiFloats experiment; and
12. optional conversion/thread/packed work.

Stop a work package when:

- a proof obligation cannot be stated locally;
- the fallback no longer begins from original inputs;
- final code points differ under any projection;
- a refused control regresses by more than 5%;
- the public path misses the performance gate;
- memory/load/code-size cost exceeds the measured benefit; or
- complexity leaks into multiple callers instead of remaining behind its
  internal interface.

After each kept commit, run the focused tests and benchmarks. At milestones 4,
7, and 10 run the full test suite and rebuild the documentation. At completion,
rerun the published benchmark suite on a clean tree, update the generated HTML,
and record both gains and rejected candidates with their environment.

## Final expected shape

The intended result is not a collection of unrelated fast branches. It is a
deeper implementation organized around four existing seams:

- exact carrier representation;
- evaluation with proof/refusal;
- projection as the single code-point write path; and
- table/cache policy outside array loops.

That shape gives scalar calls, array kernels, blocks, and Base veneers shared
leverage while keeping correctness proofs and regression tests local.
