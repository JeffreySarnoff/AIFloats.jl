# Performance and throughput improvement plan

## Status and scope

This plan was prepared from the source at commit `81a7efb` on 2026-08-31,
using the generated report at `docs/build/60-benchmarks/index.html` as the
published reference and fresh Chairmarks runs as the current-tree check. The
HTML report describes commit `026a468`; two later commits changed the MPFR
enclosure and endpoint-projection paths, so its numbers are a baseline, not a
complete description of the present implementation.

This document decides **what** to investigate and in what order. The companion
`docs/howfaster.md` specifies **how** to measure, prove, implement, review, and
accept each change.

The objective is lower latency, fewer allocations, and higher sustained
throughput without changing:

- any code point produced by any of the 27 projections;
- special-value, saturation, sticky, or stochastic behavior;
- the one-rounding rule;
- deterministic RNG consumption order;
- table/scalar equivalence; or
- the rigorous fallback used when a fast path cannot prove its result.

## Correctness rule

Every optimization must be one of these:

1. the same computation expressed more cheaply;
2. an exact value-preserving carrier change;
3. a candidate followed by an independent proof, with refusal to the existing
   oracle; or
4. a cache/table lookup populated by that same oracle.

An approximate intermediate may not be projected directly merely because the
target has at most 16 significant bits. That can double-round under ordinary,
directed, odd, and stochastic modes.

### Quadmath constraint

`Quadmath.Float128` transcendental functions are **not assured to be correctly
rounded**. A Float128 function result is therefore never, by itself, a proof,
an exact oracle, or a certified enclosure endpoint. It may be used only under
an independently justified error enclosure. Exact binary128 bit decomposition,
exact carrier conversion, pure-Julia `fma128`, and proofs about binary arithmetic
are separate matters; each still needs its own stated preconditions and tests.

## What the current measurements say

Reference machine: Intel i9-14900K, Julia 1.12.6, four threads. The published
report used commit `026a468`; the fresh run used `81a7efb`.

| Row | Published | Current check | Interpretation |
|---|---:|---:|---|
| `Add`, K=8 | 8.7 ns | 8.7 ns | Healthy scalar baseline |
| `Exp`, K=8 | 22.2 ns | 22.4 ns | Eager enclosure resolves without MPFR |
| `Exp`, `FAST_ENCLOSURE=false` | 2459.6 ns, 83 allocs | 1064.1 ns, 44 allocs | Later MPFR change is about 2.3x faster |
| `Add`, K=16 rung 2 | 132.6 ns | 132.6 ns | Carrier/evaluation/projection cost remains |
| `Multiply`, K=16 rung 2 | 422.0 ns | 419.0 ns | Float128 proof path dominates |
| `Exp`, K=16 rung 2 | 3125.8 ns, 83 allocs | 2004.4 ns, 62 allocs | Improved, still the largest scalar steady-state cost |
| K=12 `vmap! Add`, N=65536 | 0.274 Gelem/s | 0.274 Gelem/s | Already close to four-thread scalar throughput |
| K=8 table `vmap! Add` | 4.388 Gelem/s | 4.634 Gelem/s | Memory/gather path is healthy |
| packed unary K=5 | 5.45 Gelem/s | 5.53 Gelem/s | About 30% behind unpacked, not the former 3x gap |
| `BlockReduceAdd`, B=16 | 272.1 ns, 0 allocs | 269.5 ns, 0 allocs | Existing Float64/Dyadic path is healthy |
| `BlockAdd`, B=16 | 590.5 ns, 22 allocs | 0.67–0.78 µs, 22 allocs in exploratory runs | Allocation/inference path needs attribution; one-run timing is noisy |
| `ScaledAdd` | 146.6 ns, 7 allocs | 141.3 ns, 7 allocs | A small block still pays the general pipeline |
| `round(x)` | 230.4 ns, 2 allocs | 0.17–0.25 µs, 2 allocs | Dynamic default-saturation dispatch is avoidable |
| `using AIFloats` | 56.62 ms | 59.77 ms | Track, but do not trade steady-state quality blindly |
| first `Add(x,y)` / `Exp(x)` / `Log(x)` | 7.72 / 7.0 / 6.35 ms | 8.18 / 7.07 / 6.60 ms | Named convenience forms are missing from the workload |

The K=12 compute row is not evidence of a slow loop: four copies of a
13.8-ns scalar operation imply about 0.29 Gelem/s before scheduling and memory
costs, close to the measured 0.274. Improve the scalar engine or table policy
before rewriting this loop.

## Measurement omissions to fix first

The current suite is useful but not sufficient to choose the next changes.
Add these dimensions before accepting an optimization:

- rung-2 operations over a stratified code population, not only convenient
  values such as 1.5 and 0.25;
- accepted and refused fast-path controls;
- rung-3 scalar and block rows;
- all Base integer-rounding veneers and `convert` input families;
- `ConvertToBlockMaxAbsFinite`, mixed carrier blocks, non-unit scales, and
  identity-scale blocks;
- pure and stochastic array kernels, with an explicit fixed `R` control;
- adaptive-table sequences including build, warm reuse, memory, and total
  break-even—not just a warm gather;
- N below, near, and above the thread threshold, at one and four threads;
- fused, scalar-operand, and mixed-type broadcasts as explicit controls;
- several independent processes, reporting medians and allocations; and
- cache state and fast-path acceptance rates alongside timing.

`table_policy` must also be corrected as instrumentation. Its prose says it
reads the same predicates as the kernels, but its current result does not
describe the binary adaptive band used by the six-argument `table_for` method.
Performance introspection must not disagree with the implementation it is
intended to explain.

## Prioritized opportunities

### P0 — Make the benchmark evidence decision-grade

1. Extend the Chairmarks harness with the missing populations and controls
   above.
2. Add a comparison mode that records commit, policy settings, time,
   allocations, bytes, throughput, and acceptance counts in a machine-readable
   form as well as the current readable report.
3. Treat the latency suite separately: first-call compilation is measured in
   fresh processes, not sampled by Chairmarks.
4. Record multi-process medians before and after each change. Do not infer a
   regression from the current single noisy `BlockAdd` comparison.

### P1 — Remove dynamic dispatch from Base integer-rounding veneers

`round`, `floor`, `ceil`, `trunc`, and `round(x, mode)` form a projection from
an exactly rounded carrier integer. Their common-default path constructs a
projection with `DefaultSaturationMode()`, whose abstract global value causes
two allocations and roughly 0.2 µs of dispatch. An explicit `RTE_SN`
projection measured 6.5 ns and allocation-free.

Use the same speculation-guard pattern already used by constructors and scalar
operations: test identity with `SN`, call the literal projection constant on
the common branch, and keep the dynamic branch for a changed session default.
This changes neither rounding nor saturation.

### P1 — Add an exact binary128 bit adapter and use it for projection

The generic `Dyadic(Float128)` route calls `Base.decompose`, creates a `BigInt`,
and measured about 89 ns with nine allocations. A local read-only prototype
decoded the IEEE binary128 fields directly into `Dyadic` in 2.3 ns with no
allocation; projecting the same finite Float128 value through that exact
Dyadic took 8.6 ns versus 54.0 ns through `_rtp_core`. A 100,000-value random
finite-bit comparison against exact `BigFloat` conversion found no mismatch;
that is encouraging evidence, not the acceptance proof.

Create one internal carrier module with a very small interface:

- exact Float128 classification/decomposition to `Dyadic`;
- conservative “exactly representable as normal Float64” conversion or
  refusal; and
- no transcendental operation.

Use the adapter in `round_to_precision(::Float128)` so Float128 projection
shares the already-tested fixed-point rounding implementation. Keep the old
core available as a differential oracle until exhaustive gates pass.

### P2 — Value-sensitive exact narrowing at the evaluation seam

The format-wide carrier is chosen for the most extreme datum, but many actual
rung-2 datums are exactly representable in Float64. Exploratory complete-code
counts were 12.8% for `Binary(16,2,...)`, 51.17% for `Binary(16,4,...)`, and
100% for `Binary(16,5,...)`. On easy values, a Float64 evaluation of rung-2
`Multiply` and `Exp` was dramatically cheaper than the Float128/MPFR route.

At the internal `apply_op` seam, try an exact bit-proved narrowing of all finite
Float128 operands. If every operand accepts, evaluate the same operation on
Float64; the existing Float64 oracle may still widen or fall back when its
result needs it. If any operand refuses, run the current Float128 path
unchanged.

Do not prove this with `Float64(x)` followed by a Float128 round trip. Build or
refuse from the binary128 fields so the optimization does not depend on an
unpublished Quadmath function guarantee. Implement explicit arity-one,
arity-two, and arity-three helpers so tuples/unions do not reintroduce boxing.

### P2 — Extend exact Dyadic block reductions beyond Float64 lanes

Every P3109 datum is dyadic with at most 16 significant bits. A block lane is
the product of scale and element datums, so its exact significand begins at at
most 32 bits even when its format-wide carrier is Float128 or Dyadic. Decode
finite block inputs directly to the exact carrier, multiply with `mul_dy`, and
reuse the existing guarded Dyadic sum/product logic. The first failed width or
alignment precondition must restart from the original lanes on the existing
derived-precision BigFloat path.

This should cover many rung-2 and mixed-carrier reductions without invoking a
Float128 function at all. It is preferable to adding scattered Float128
reduction filters because the exact carrier already expresses the required
semantics.

### P2 — Add an identity-scale block adapter

`ScaledAdd` with unit scales still pays the seven-allocation general block
pipeline. When every input scale and the result scale are exactly one,
`BlockOp` is precisely the corresponding element operation and `ScaledOp` is
precisely the corresponding scalar operation. Add one generated internal
adapter at this seam for all registry operations rather than per-operation
special cases.

For stochastic projections, resolve the RNG once and draw exactly once per
result lane in index order. For non-unit scales, preserve the current pipeline.
After the identity route, profile whether fusing decode/evaluate/divide/project
for other common blocks removes the 22/38 intermediate allocations without
making the result carrier union worse.

### P3 — Finish the block quotient work only where it can prove exactness

Reuse `_try_div128` in `_bp_element` when the lane result and scale are both
exact Float128 values. A successful residual proof may project the quotient;
refusal must call the current directed interval. Non-power-of-two scale cases
such as `1/96` are not Float128 opportunities and should not be advertised as
such.

### P3 — Precompile the entry points the latency suite actually calls

The workload compiles explicit register calls and Base veneers, but the fresh
process probes call named convenience forms such as `Add(x,y)`, `Exp(x)`, and
`Log(x)`. Add those exact forms and the allocating `sort` wrapper to the
workload. Accept only if their first calls become sub-millisecond without an
unreasonable increase in package-load time or cache size.

### P3 — Evaluate wider adaptive tables for sustained workloads

Warm tables are 10–17x faster than compute for rows such as K=8 ternary FMA,
but building a 24-bit table costs time and 16 MiB of result storage. Extend the
adaptive bands only from end-to-end break-even sequences. Before widening the
binary band, add an aggregate byte cap/LRU comparable to the ternary cache;
otherwise many earned tables can grow memory without bound.

Candidates:

- ternary ΣK=24 for repeated K=8 FMA/FAA/Clamp workloads;
- binary bands above ΣK=18 for repeatedly used wider formats; and
- lower adaptive thresholds only when build cost, compute cost, and expected
  reuse justify them on more than one machine.

Never table stochastic projections. A warm-only benchmark is insufficient.

### P4 — Evaluate MultiFloats only as a bounded estimator experiment

[MultiFloats.jl](https://github.com/dzhang314/MultiFloats.jl) provides normalized
Float64 expansions (`Float64x2` through `Float64x4`) with verified error bounds
for its core arithmetic. Those types are not IEEE binary128 or binary256, do
not supply this package's directed correctly-rounded oracle, and have special
value behavior that differs from ordinary IEEE carriers. Because their limbs
are Float64, their useful exponent range is also not a replacement for the
binary128/BigFloat range required here. The linked
[formal analysis](https://theory.stanford.edu/~aiken/publications/papers/sc25.pdf)
establishes expansion error bounds under stated assumptions; it does not make
an expansion operation a correctly rounded binary128/binary256 operation.

This rules out replacing `BigFloat`, `Dyadic`, or the projection ladder with
MultiFloats. It may still be worth one isolated experiment as a finite,
ordinary-range estimator for `+`, `-`, `*`, `/`, or `sqrt` when an independently
derived bound can turn the result into a certified enclosure. It is unlikely
to help the transcendental bottleneck because MultiFloats documents those
operations as MPFR-backed.

Keep the experiment outside the package dependency graph initially. Measure
`Float64x2` and `Float64x4` against the existing Float128 and MPFR paths for:

- accepted finite inputs, rejected exponent/special inputs, and fallback cost;
- estimator time, enclosure-construction time, allocations, and end-to-end
  public-operation time;
- every deterministic projection mode and relevant saturation mode; and
- adversarial cancellation, overflow/underflow boundaries, and noncanonical
  expansion representations.

Proceed only if the enclosure proof is local and reviewable, refusal resumes
from original inputs, the accepted public path improves by at least 20%, and
the refused path regresses by no more than 5%. Otherwise record the result and
do not add MultiFloats as a dependency. The exact Float128-to-Float64 narrowing
experiment remains simpler and has higher priority.

### P4 — Small and conditional work

- Specialize `convert(T, ::Float64/Float32/Float16/BFloat16)` through the same
  default-projection guard as constructors. Current `convert(T, 1.3)` is about
  7.2 ns versus 1.8 ns for construction and 0.7 ns for explicit `Convert`.
- Test `Threads.@threads :static` and threshold changes across sizes and thread
  counts, but retain the current loop if end-to-end throughput does not improve.
- Revisit packed extraction only with a new profile. The direct table gather,
  unaligned safe window, and eight-lane path have already removed the former
  large gap.
- Clean duplicate annotations/statements (`@inline @inline`, repeated local
  assignment) when touching their files, but do not present cleanup as a
  performance result.

## Work that should not be pursued now

- Rewriting K=12 compute loops without first reducing scalar cost: they are
  already near the expected four-thread ceiling.
- Direct projection of an unproved Float128 transcendental result.
- Treating `Float64x2`/`Float64x4` as IEEE binary128/binary256, or using a
  MultiFloats result without translating its stated error bound into a valid
  enclosure for this package.
- Replacing rigorous MPFR intervals for genuinely inexact division or
  composite transcendental expressions.
- A general `BigFloat -> Float128 -> project` check; prior measurement showed
  a refusal regression and inadequate endpoint hit rate.
- Reintroducing mixed `_samecarrier` Float64/Float128 methods; that sound change
  previously worsened `ScaledAdd` from 192 to 312 ns and doubled allocations.
- Wholesale changes to packed storage, fused broadcast semantics, or public
  interfaces without a representative workload.
- Changing RNG order to enable threading of stochastic kernels.

## Review corrections incorporated into this plan

The initial hotspot list was revised after source attribution and measurement:

- The HTML report was tied to its commit and rerun on the current tree.
- K=12 array time was attributed to scalar work rather than presumed loop
  overhead.
- The packed path was demoted because the current source already includes the
  direct gather and vectorized extractor.
- Rung-2 narrowing was changed from a conversion round-trip to a bit-proved
  exact adapter, avoiding reliance on Quadmath function rounding.
- Float128 projection and rung-2 evaluation were separated: the former can use
  an exact bit representation even when no arithmetic narrowing is possible.
- Wider block reductions were redirected toward exact Dyadic datum decoding,
  not approximate Float128 accumulation.
- Warm table throughput was paired with build latency, cache memory, and reuse
  break-even.
- First-call latency was traced to missing interface forms rather than a broad
  request for more precompilation.
- `table_policy` drift was added as a prerequisite so later measurements are
  not explained by incorrect introspection.
- MultiFloats was limited to an estimator experiment because its expansion
  guarantees, exponent range, special-value semantics, and MPFR-backed
  transcendentals do not satisfy the carrier/oracle contract directly.

## Acceptance gates

Keep a change only when all correctness gates pass and at least one performance
gate is met:

- at least 15% and 5 ns improvement on a scalar hot path;
- at least 10% improvement on an array/block throughput path;
- removal of a steady-state allocation from a declared hot path;
- at least 5x reduction in a measured first-call latency; or
- a documented end-to-end table break-even with bounded memory.

No paired refusal/control may regress by more than 5% in the multi-process
median. Code size, load time, and memory are part of the result. A failed
experiment is removed and recorded with its measurement so it is not retried
without new evidence.

## Execution order

1. Benchmark/introspection corrections.
2. Base rounding speculation guard.
3. Exact binary128 bit adapter and Float128 projection.
4. Value-sensitive rung-2 narrowing.
5. Exact wider block reductions and identity-scale block adapter.
6. `_bp_element` exact Float128 quotient.
7. Named-form precompilation.
8. Wider adaptive-table experiments behind bounded caches.
9. Isolated, proof-gated MultiFloats estimator experiment.
10. Conditional small work and final source-wide audit.

This order earns early, low-risk wins, establishes one exact carrier seam used
by several later changes, and leaves memory-heavy or workload-dependent
throughput experiments until the benchmark evidence can decide them.
