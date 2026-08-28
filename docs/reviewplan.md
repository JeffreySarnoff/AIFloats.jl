# Review Plan — src/ correctness, consistency, and throughput

Supersedes an earlier survey, `docs/planreview.md`, since removed. That document
was a good map of the territory; this one is what to *do*, in order, with the
evidence that justifies each step. References to it below are kept because they
record which of its claims were checked and found stale. Anything not listed
here is deliberately out of scope for this pass.

**Enacted.** See [implmentplan.md](implmentplan.md) for the realization and
[checkpoint.md](checkpoint.md) for what each step actually changed and measured.

Evidence was gathered on the dirty worktree at `2a48515`, Julia 1.12.6,
Chairmarks 1.3.1, i9-14900K, `-t 4`, from a throwaway environment
(`Chairmarks` + path dependency on this package). No numbers below are release
baselines; they are large enough ratios that noise does not change the
conclusions.

## 1. How the review is organized

Review by **execution path**, not by file. Every file is owned by exactly one
path; each path has one external seam that tests and benchmarks exercise, and
one reference implementation that fast paths must agree with.

| Path | Files | External seam | Reference |
|---|---|---|---|
| P1 codec | `types/*`, `content/*`, `carriers/heads.jl` | `decode`, `encode`, `BinaryValue(x)`, `order_key` | exhaustive sweep in `test-codec.jl` |
| P2 projection | `projection/*`, `carriers/dyadic.jl`, `bigprec.jl` | `project(F, ρ, x; R, sticky)` | `project_interval` (MPFR) |
| P3 scalar engine | `ops/*`, `carriers/fma128.jl`, `faa128.jl`, `rules/defaults.jl` | `Op(F, ρ, x...)` and `Op(x...)` | `FAST_ARITH[]=false`, `FAST_ENCLOSURE[]=false` |
| P4 tables + arrays | `tables/*`, `arrays/kernels.jl` | `vmap!`, `vmap`, `get_table` | `_vmap_scalar!` (compute path) |
| P5 blocks + packed | `arrays/blocks.jl`, `arrays/packed.jl` | `Block*`, `PackedVector`, packed `vmap` | BigFloat block reductions; unpacked `vmap!` |
| P6 Base surface | `compat/*`, `rules/constraints.jl`, `conformance.jl`, `approx.jl`, `AIFloats.jl` | `+`, `convert`, `sort`, `rand`, `show`, load/precompile | the explicit-projection forms in P3/P4 |

Rule for every change: identify the seam, identify the reference, add or point
to the equivalence test, measure before/after with the same Chairmarks
expression in a fresh process, keep only if the gain clears the threshold in §5.

## 2. What the evidence says (measured, this tree)

Scalar, K=8 (`binary8p4se`), explicit projection unless noted:

| Call | Result | Reading |
|---|---:|---|
| `Add(T,RTE_SN,x,y)` | 8.6 ns, 0 alloc | Good; the Float64-exact path works. |
| `Add(x,y)` (session default) | 9.0 ns, 0 alloc | Good — the `ρ === RTE_SN` speculation guard in `scalar.jl:101` works. The 108 ns / 3-alloc figure in the earlier survey was **stale**. |
| `T(1.3)`, `convert(T, 1.3)`, `T(1.3f0)` | **82 ns, 2 allocs** | Bad. `Convert(T,RTE_SN,1.3)` is 0.7 ns. Cause: `scalar.jl:169` keyword `projection::Projection = DefaultProjection()` — abstract `Ref` read, no speculation guard. Same for `base.jl:368`. |
| `T(3)` (Integer) | **586 ns, 28 allocs** | Bad. Integer goes through a BigFloat-ish route. |
| `FMA(T,RTE_SN,x,y,z)` at Float64 rung | **451 ns, 0 alloc** | Bad. `oracle.jl:305` always widens to Float128 before checking whether the Float64 product/sum are exact. `Add`/`Multiply` are 9 ns. |
| `Exp`, `Exp2`, `Sqrt` | 18–22 ns, 0 alloc | Good; the eager Float64 envelope decides. |
| `Log`, `Log2`, `Sin`, `Cos`, `ScaledAdd` | **250–310 ns, 7 allocs, 128 B** | Bad. The stage-1 envelope decides here too (yd is finite), yet `_mpfr1(log, x)` itself costs 280 ns / 7 allocs where `_mpfr1(exp, x)` costs 2.5 ns / 0 allocs. Each component (`_ladder1`, `_fq1`, `_f64guard`) is cheap in isolation; the composite is not, so this is an inlining/closure-boxing failure specific to `f`s that can throw (`log`, `sin`, `cos`, `log2`, …), plausibly the `try/catch` in `_f64guard` blocking inlining. Hypothesis, not yet confirmed. |
| `ArcTan2Pi` | 36 ns | Fine. `Pkg.test()` on this tree passes all 16 test sets (exit 0), so the `ArcTan2Pi` interval failures the earlier survey reported were **stale**. |
| `decode` K=8 / K=9 / K=12 | 1.8 / 3.1 / 3.1 ns | Good. |
| `project(F, RTE_SN, 1.3)` K=8, K=12 | 1.05 ns | Good; the Float64 bit path is the hot path. |
| `x < y`, `Float64(x)` | 1.8 ns | Good. |

Arrays, N = 65,536, K=8 unless noted:

| Call | Result | Reading |
|---|---:|---|
| `vmap!(d, Val(:Add), RTE_SN, A, B)` warm table | 15 µs | Good. |
| `vmap!` Add K=12 compute, 4 threads / 1 thread | 242 µs / 927 µs | Good scaling; 22 allocs is the scheduler. |
| `vmap!` Exp K=8 warm / K=12 compute | 9.5 µs / 10.7 µs | Good (K=12 unary is 4096 entries: tabled). |
| **`A .+ B` broadcast** | **631 µs, 65 KB** | Bad: 40× slower than `vmap!`. Broadcasting hits the scalar veneer per element; nothing routes `.+`/`.*`/`exp.()` through the table gather. This is the largest throughput gap found. |
| `sort(A)` K=8 / K=12 | 30 / 40 µs | Good (counting sort). |
| cold `empty_tables!()` + build + Add on 4,096 elems | 150 µs | Table build is ~10× a warm 64k call; fine. |
| cold Exp build + 4,096 elems | 6.5 µs | Fine. |
| packed `vmap(:Negate, …, P)` vs unpacked | 46 µs vs 8.6 µs | 5.3× penalty for the tiled adapter. |
| `PackedVector(A)`, `collect(P)`, `P[i]` | 35 µs, 19 µs, 1.9 ns | Acceptable. |
| `blockdecode`, B=16 | 220 ns, 16 allocs | The P=1 exponent-add decode noted at `blocks.jl:15` is absent. |
| `BlockReduceAdd` / `BlockDotProduct` / `BlockAdd`, B=16 | 2.9 µs / 5.3 µs / 1.0 µs, 188 / 352 / 53 allocs | All lanes lift to BigFloat unconditionally. |

Consistency and documentation findings (confirmed by reading):

- `AIFloats.jl:16` says blocks and packed storage are "staged next"; both are implemented and exported.
- `singletons.jl:416, 426, 436, 469` say saturation modes and projection application are "not implemented yet"; `projection/*` implements all of them.
- `blocks.jl:15` calls the P=1 decode a deferred port; it is still absent (true), but the sentence claims "with the rest", and the rest has landed.
- `registry.jl:56` — `:CopySign` special case is unreachable (already caught by the `_EXACT_SELECTION` test on line 54).
- `oracle.jl:733–741` — π-scaled trig exact peels return bare `BigFloat` (uncontrolled precision, and not via `_czero(C)`-style helpers), so they bypass the Float64 fast path in `apply_op`. Cold, but inconsistent with the neighbouring peels.
- `tables/policy.jl:206` — `TERNARY_USE` counters only grow; `empty_tables!` should reset them or the docstring should say they are process-lifetime.
- `arrays/kernels.jl:227` — external-float `Convert` loop draws `R` with `_drawR(ρ, rng, nothing)` per element without resolving `rng` once first, unlike `_vmap_scalar!` at line 158. Same result, extra work; also a consistency smell.
- `arrays/packed.jl:29` — `>>` already bound tighter than `+` (no bug); parentheses added for clarity.
- `test/test-compat.jl:20` and `test/test-fastpaths.jl:14` both define `allcodes` in `Main` (overwrite warning under `Pkg.test`).
- The mixed UInt8/UInt16 ternary LRU budget defect the earlier survey reported is **already fixed**: `cache.jl:84–118` evicts the globally oldest entry across both caches (its comment records the old bug). Only a test is missing.

## 3. Phase 0 — correctness baseline (no performance work until green)

1. `Pkg.test()` is green on this tree (verified, `-t 4`). Nothing to repair
   before measuring; the only remaining Phase 0 items are the three below.
2. Add the mixed-width ternary eviction regression test (1,024-byte UInt16
   table, then a 512-byte UInt8 table, budget 1,024; assert total ≤ budget).
   The fix is already in `cache.jl`; the test is what is missing.
3. Move `allcodes` and any other shared test helper into `test/support/` and
   `include` it once.
4. Fix the stale docstrings/comments listed in §2. This is a documentation
   change, but it is Phase 0 because reviewers otherwise cannot trust comments
   as oracles.

Gate: `Pkg.test()` green, no overwrite warnings, docs build.

## 4. Phase 1 — benchmark harness

Put the throwaway recon into the repo so every later step is reproducible:

```
benchmark/
  Project.toml      # AIFloats (path ".."), Chairmarks
  runbenchmarks.jl  # includes the suites below, prints one line per case
  scalar.jl         # §2 scalar table + one op per registry group, K ∈ {8, 12}
  arrays.jl         # vmap!/broadcast/sort/packed/block, N ∈ {4096, 65536}
```

Rules: `@b` with interpolated operands; `evals=1` for cold-table cases; restore
every `Ref` (`FAST_*`, `THREADED_KERNELS`, `TABLE_EAGER_BITS`) in `finally`;
print `Threads.nthreads()` and `Sys.cpu_info()[1].model` at the top. Replace
the three duplicated `benchmark/bench_floats{1,2,3}.jl` files with this. No
baseline directory yet — run twice in fresh processes and compare by eye until
the suite is stable.

Gate: `julia --project=benchmark benchmark/runbenchmarks.jl` runs from a clean
checkout.

## 5. Phase 2 — the five fixes with measured payoff

Ordered by (benefit × certainty) / risk. Each is one commit, one benchmark
line before/after, one equivalence test.

| # | Change | Where | Expected | Equivalence test |
|---|---|---|---|---|
| 1 | Speculation guard on the constructor default: `ρ = DefaultProjection(); ρ === RTE_SN ? Convert(F, RTE_SN, x) : Convert(F, ρ, x)` as a function barrier; same for `convert(::Type{T}, ::Unsigned)` at `base.jl:368` | `scalar.jl:169`, `base.jl:368` | 82 ns → ~1 ns, 0 allocs, for `T(x)`, `convert`, and therefore every `setindex!` into a datum array from a Float | `test-fastpaths.jl` allocation assertions extended to constructors |
| 2 | Route broadcasting through the kernel: `Base.Broadcast.materialize(!)` for `Broadcasted{DefaultArrayStyle}` whose function is a registered veneer (`+ - * / fma exp …`) and whose args are same-format `AbstractArray{T}` → `vmap!`; fall back otherwise | new `arrays/broadcast.jl` after `kernels.jl` | `A .+ B` 631 µs → ~15 µs (table) / ~240 µs (compute) | `A .+ B == vmap(:Add, …)` over the K=8 grid; mixed-style and scalar-broadcast fallbacks still work |
| 3 | Float64-first FMA: before widening, `p = x*y; e = fma(x,y,-p)`; if `e == 0` the product is exact and the existing `Add` path finishes it; only otherwise widen | `oracle.jl:305` | 451 ns → ~15 ns on the common exact case; sticky/BigFloat escalation unchanged | exhaustive K=8 ternary sweep vs `FAST_ARITH[] = false` (already the pattern in `test-fastpaths.jl`) |
| 4 | Make `_mpfr1`/`_mpfr2` cost the same for `log`/`sin` as for `exp`: first test the hypothesis (`@b _f64guard(log, $x)` vs a variant with the domain checked up front and no `try`), then either add `@inline` to `_mpfr1/_mpfr2` or replace `_f64guard` by domain-predicated direct calls (the `ωeval` rows already exclude NaN, ±Inf, and out-of-domain inputs, so the `try` guards nothing on the Float64 tier) | `oracle.jl:47–60, 89, 96` | 300 ns / 7 allocs → ~25 ns / 0 allocs for the whole Group B | `FAST_ENCLOSURE[]=false` equivalence, already in `test-fastpaths.jl` |
| 5 | Integer constructor: convert `Integer` to the format's `promotecarrier` first (exact for `|n| < 2^53` in Float64, else Float128/BigFloat), then `Convert` | `scalar.jl:169` region | 586 ns / 28 allocs → ~2 ns | exact for all `Int` in the datum grid, and for `2^53 ± 1` |

Threshold to keep a change: ≥ 15 % and ≥ 5 ns on a scalar hot call, or ≥ 10 %
on a kernel, or removal of a steady-state allocation on a declared
allocation-free path; no paired regression > 5 %.

Gate: Phase 0 gate still green; the five benchmark lines show the expected
ratios in two fresh processes.

## 6. Phase 3 — blocks and packed (only after Phase 2)

These are real but smaller wins with more code motion; do them only with the
harness in place.

1. **Block lane arithmetic in the exact narrow carrier.** For B ≤ 32 lanes of
   K ≤ 8 elements with a scale datum, the exact product/sum fits comfortably in
   Float128 or a `Dyadic`; escalate to BigFloat only when `rung` says so
   (the machinery already exists in `heads.jl`). Keep the BigFloat path as the
   differential oracle. Target: `BlockReduceAdd` 2.9 µs / 188 allocs → < 300 ns
   / 0 allocs.
2. **P=1 `blockdecode`.** Implement the exponent-add decode that `blocks.jl:15`
   promises, gated by an exhaustive equivalence test over all scale × element
   codes for one K=8 P=1 format. Then delete the "deferred" comment.
3. **Packed gather.** Replace the tile-unpack adapter for the unary
   table-gather case with a direct loop: extract code → table lookup → write.
   Keep `PACK_TILE` for the compute case. Target: 46 µs → < 15 µs.
4. Decide, from a workload the user actually has, whether binary packed
   operands or bulk `BlockVector` kernels are needed. Do not build them
   speculatively.

## 7. Phase 4 — thresholds and load latency (cheap, last)

- Refit `THREAD_MIN_ELEMS` (currently 32,768) with the harness for one cheap
  (Add K=12 compute) and one expensive (Log K=12 compute) op. Keep one threshold
  if both agree within 2×.
- Confirm `TABLE_EAGER_BITS = 16` against measured build cost: K=9 binary Add
  (2^18 entries) is currently forced to compute at 237 µs; a one-time build
  would amortize in a few calls. Either raise the band to 18 for Group A ops or
  document why not.
- Measure `@time using AIFloats` and first-call latency for `Add`, `Exp`,
  `vmap!`, `A .+ B` (after fix 2), and add the broadcast path to the
  `@compile_workload`.
- Reset `TERNARY_USE` in `empty_tables!`.

## 8. What is explicitly not done in this review

- No change to public semantics, parameter order, or the 27 projection names.
- No raising of the 4,096-bit interval cap without a failing reproducer.
- No new public interfaces for packed/blocks without a workload.
- No dependency added to the package `Project.toml`; Chairmarks lives only in
  `benchmark/Project.toml`. (Separately: `Aqua`, `JET`, `SHA`, `Statistics`,
  `SmallCollections` appear under `[deps]` in the package `Project.toml`; move
  the test-only ones to `[extras]` once Phase 0 is green.)

## 9. Completion

Done when: Phase 0 gate green; `benchmark/runbenchmarks.jl` runs and its
scalar table shows no entry over 30 ns for a Float64-rung Group A/B call on the
common case; `A .+ B` is within 2× of `vmap!`; constructors and Base veneers
report 0 allocations in `test-fastpaths.jl`; every "deferred / not implemented /
staged" sentence in `src/` is either true or gone.
