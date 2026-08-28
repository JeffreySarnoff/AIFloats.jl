# Enactment checkpoint — structuralplan.md

*Session log for picking up without redoing work. Read together with
[structuralplan.md](structuralplan.md) and, for the current work,
[implmentplan.md](implmentplan.md). Newest entry first.*

## implmentplan.md Step 8 done — blocks: concrete lanes, Dyadic accumulation (2026-08-28)

Gate: full `Pkg.test()` green. `test-blocks` 14,404.

**The plan was rewritten before it was enacted.** Its first draft proposed
`_mexp` / `_sum_fixed` / `_fixed_to_carrier` — an Int128 fixed-point accumulator
with a hand-derived 126-bit overflow budget. A prototype showed that is a
reimplementation of `Dyadic` (`src/carriers/dyadic.jl`), which already *is*
`S::Int128 · 2^Q::Int64`, already has `add_dy` with the alignment and width
preconditions worked out, is already covered by `test-dyadic.jl`, and is already
accepted by `project` and `_finish`. Measured on the same lanes: Dyadic
accumulation 156 ns / 0 allocs against `_reduce_add_value`'s 2,173 ns / 151,
bit-identical. Writing a second exact accumulator would have been the riskiest
thing in the plan for no gain.

- `src/arrays/blocks.jl`:
  - `_f64_block(S, E)` — folds at compile time (both `datumcarrier` calls depend
    only on type parameters), so wider-carrier blocks pay nothing.
  - `_f64_lanes(b) -> (NTuple{B,Float64}, Bool)` — the lanes plus an fma proof
    they are exact. Returns a **concrete pair, never a union**, which is what
    makes it allocation-free.
  - `blockdecode` uses it for the common case. Its own return stays a union
    (`NTuple{B,Float64}` or the general carrier tuple) — that is its honest
    general-purpose type, and crossing it costs one box.
  - `_dyadic_sum` — mirrors `add_dy_checked`'s preconditions but *returns*
    `nothing` where that function throws, so the caller can fall back.
  - `_exact_lane_products` — fma-certified Float64 lane products for the dot
    product, reusing `_FMA_EXACT_FLOOR` from Step 4.
  - `BlockReduceAdd` and `BlockDotProduct` call `_f64_lanes` **directly rather
    than `blockdecode`**: merely crossing that union boundary boxed the tuple
    and cost the last allocation (144 B at B = 16). Bypassing it took both to
    exactly zero.
- `BlockReduceMultiply` deliberately unchanged: accumulating products grows the
  significand by `P_S + P_E` per lane, so `mul_dy`'s `nbits ≤ 96` precondition
  fails almost immediately at B = 16. BigFloat is the right carrier there.

### A real bug the existing suite caught

The first fast lane used raw `Sv * xs[i]`, which yields `−0.0` when the signs
differ. The draft has a **single zero** — `ωMultiply` returns `+0` — so the fast
and generic paths disagreed on the sign of zero. `test-blocks.jl`'s
"blockdecode ≡ lane semantics" testset failed immediately and named the case.
Both `_f64_lanes` and `_exact_lane_products` now normalize a zero product, with
the reason recorded at each site. This is the second time in this plan an
exactness shortcut was wrong in a way only a written-down assertion caught
(Step 4's underflow floor was the first).

### Verification

6,144 differential comparisons against the BigFloat oracle (4 scale formats × 4
element formats × B ∈ {1,4,16,32} × 3 projections, both reductions) — zero
mismatches, with the fast path genuinely exercised on 780 of 2,048 decodes and
the fallback on the rest. Plus 144 special-value combinations (NaN, ±∞, both
infinities, all-zero, max-magnitude, min/max mix, wide spread, exact
cancellation) across 4 scales. Plus three rung-1 formats — `(8,1)`, `(10,2)`,
`(12,2)`, whose lane spreads exceed Dyadic's 94-binade alignment band — asserted
to *decline* the fast path and still match the oracle.

| Row | Before | After |
|---|---:|---:|
| `blockdecode` B=16 | 249 ns, 17 allocs | **15.1 ns, 1** |
| `BlockReduceAdd` B=16 | 2,899 ns, 189 allocs | **267 ns, 0** |
| `BlockDotProduct` B=16 | 5,312 ns, 351 allocs | **297 ns, 0** |
| `BlockAdd` B=16 | 1,151 ns, 54 allocs | **605 ns, 22** |
| `BlockReduceAdd` B=32 | 5,136 ns, 347 allocs | **535 ns, 0** |
| `BlockDotProduct` B=32 | 9,743 ns, 673 allocs | **580 ns, 0** |
| `ScaledAdd` | 143 ns, 7 allocs | **150 ns, 7** (unchanged) |
| `BlockReduceMultiply` B=16 | 3,514 ns | 3,221 ns (out of scope) |

10.9x on `BlockReduceAdd`, 17.9x on `BlockDotProduct`, both allocation-free —
past the plan's ~200 ns / 0-alloc projection on allocations and close on time.

### Steps 0–8 cumulative

| Row | Baseline | Now |
|---|---:|---:|
| `T8(1.3)` | 98.6 ns, 2 allocs | 1.4 ns, 0 |
| `T8(3)` | 583 ns, 28 allocs | 1.8 ns, 0 |
| `FMA` K=8 | 452 ns | 12.7 ns |
| `Log` K=8 | 236 ns, 7 allocs | 27.5 ns, 0 |
| `A .+ B` N=65536 | 631,876 ns | 15,144 ns |
| `exp.(A)` N=65536 | 1,578,099 ns | 8,647 ns |
| packed `vmap` N=65536 | 52,348 ns | 26,958 ns |
| `BlockReduceAdd` B=16 | 2,899 ns, 189 allocs | 267 ns, 0 |
| `BlockDotProduct` B=16 | 5,312 ns, 351 allocs | 297 ns, 0 |

Remaining: Step 9 (thresholds and load latency), Step 10 (documentation
close-out). Both are measure-then-decide, no new machinery.

## implmentplan.md Step 7 done — broadcasting routes through the kernels (2026-08-28)

Gate: full `Pkg.test()` green, Aqua ambiguity check clean. `test-kernels` 56.

Base's elementwise loop called the scalar veneer once per element, so `A .+ B`
cost 631 µs where the `vmap!` gather over the same data cost 15 µs.

- `src/arrays/broadcast.jl` NEW: a `copyto!` method per veneer, matching
  `Broadcasted{<:DefaultArrayStyle, <:Any, typeof(f), <:Tuple{AbstractArray{T},…}}`
  with `T<:BinaryValue`, guarded at runtime by `axes(argᵢ) == axes(dest)`, then
  dispatching to `vmap!` under the same speculation guard the scalar veneers
  use. Anything else `@invoke`s Base's generic `copyto!`.
- **Include order correction.** The plan said to load this right after
  `arrays/kernels.jl`. That is impossible: the file builds its veneer table
  from `_BASE_UNARY`/`_BASE_BINARY`, which `compat/base.jl` defines, and
  `compat/base.jl` loads later. It goes AFTER `compat/base.jl`, which is also
  where it belongs conceptually. `docs/structuralplan.md` §5 and §7 updated,
  with the reason recorded so nobody "tidies" it back.
- Deriving the veneer list from the same tables `compat/base.jl` dispatches
  from means an op added to the registry cannot be silently missed here.

What deliberately does **not** match, each verified to keep Base's exact
semantics: fused chains `(A .+ B) .* C` (inner arg is a `Broadcasted`), scalar
operands `A .+ B[1]` (arg is a datum, not an array), mixed types `A .+ 1.0`
(promotes to `Float64`), predicates `A .< B` (dest is `Bool`), and shape
broadcasts `reshape(A,30,1) .+ M` (caught by the axes guard). Views, matrices,
in-place `d .= A .+ B`, and empty arrays all take the fast path correctly.

| Row (N = 65,536) | Before | After | vs `vmap!` |
|---|---:|---:|---:|
| `A .+ B` K=8 | 631,876 ns | **15,144 ns** | 1.01x (14,936) |
| `exp.(A)` K=8 | 1,578,099 ns | **8,647 ns** | 0.91x (9,525) |
| `A .+ B` K=12 | 948,560 ns | **241,223 ns** | 1.01x |
| `fma.(A,B,A)` K=8 | 1,029,984 ns | **234,426 ns** | ternary, untabled |

41.7x on `A .+ B`, 182x on `exp.(A)`; both now indistinguishable from calling
the kernel directly, which was the target (≤ 1.2x).

## implmentplan.md Step 6 done — packed direct gather (2026-08-28)

Gate: full `Pkg.test()` green. `test-blocks` 12,555.

Packed `vmap` unpacked a 256-element scratch tile and called the ordinary
`vmap!` on views of it, once per tile — 52.3 µs against 8.3 µs for the same
work on an unpacked vector. For the pure-ρ tabled case the scratch buys
nothing: the table is indexed by the code, and the code is exactly what the
packed words already hold.

- `src/arrays/packed.jl`: `_vmap_packed` now binds `op` in its `Val{op}`
  signature and, when ρ is pure and `table_for` grants a unary table, gathers
  straight out of `pv.data` — extract, index, store. No scratch, no views, no
  per-tile `vmap!` dispatch. The tiled adapter stays for stochastic ρ and for
  signatures policy declines to tabulate.
- `test/test-blocks.jl`: NEW testset "packed vmap ≡ unpacked vmap" — 6 K
  values × 2 precisions × 2 (signedness, domain) × 6 lengths chosen at and
  either side of 64-bit word boundaries × 3 ops × 2 projections, plus
  stream-identity for the three stochastic modes and the forced-untabled
  fallback. Ad-hoc sweep before committing: 1,232 configurations, zero
  mismatches.

| Row | Before | After |
|---|---:|---:|
| `vmap Negate` packed, K=5, N=65536 | 52,348 ns | **26,958 ns** |
| `vmap Exp` packed, K=5, N=65536 | 52,329 ns | **27,009 ns** |
| (unpacked reference) | 8,290 ns | 8,321 ns |

1.94x, short of the plan's < 13 µs target. The gap to the unpacked path is the
bit extraction itself, and the plan's suggested next move was tried and
**rejected on measurement**: carrying the word index and bit offset across
iterations removes a multiply per element but introduces a loop-carried
dependency, and the out-of-order engine loses far more to the serial chain than
the arithmetic ever cost — **65.1 µs carried vs 26.9 µs recomputed**, 2.4x
worse. `_wordpos(K, i)` derives each position independently from `i`, which is
what lets the loop run wide. The reverted experiment is recorded as a
"do not optimize this" comment at the loop, with both numbers.

## implmentplan.md Step 5 done — Group B enclosure builders inline (2026-08-28)

Gate: full `Pkg.test()` green, docs build clean. `test-fastpaths` 784.

`Exp` cost 22 ns and allocated nothing; `Log`, `Log2`, `Sin` cost ~240 ns and
allocated 7 objects / 128 bytes each — for the same shape of work, with stage 1
of `_finish` deciding in both cases and the MPFR ladder never called. Every
component measured cheap in isolation (`_ladder1` 1.2 ns, `_fq1` 1.2 ns,
`_f64guard` 2.5–8 ns); only the composite was slow, which is the signature of a
failed inline, not of slow arithmetic.

Cause: `_mpfr1`/`_mpfr2` were not inlined for any `f` that can throw
(`log`, `sin`, `cos`, `log2`, …), so their three closures were boxed and the
`Enclosure` heap-allocated even though it was consumed immediately and
discarded. `exp` happens to inline, which is why it looked fine and hid the
problem.

- `src/ops/oracle.jl`: `@inline` on `_mpfr1`, `_mpfr2`, `_mpfr_pitrig`,
  `_mpfr_divpi`. Four annotations, no logic change.
- The `try`/`catch` in `_f64guard` was the suspect in the plan and is
  **not** the cause — it costs ~3 ns and it is what turns an out-of-domain libm
  call into `NaN` (stage 1 skipped) instead of a throw. Kept.
- `test/test-fastpaths.jl`: `@allocated == 0` for 18 Group B ops spanning every
  libm family, plus `ArcTan2Pi` and `Hypot`.

| Row | Before | After |
|---|---:|---:|
| `Log`, K=8 | 235.7 ns, 7 allocs | **27.5 ns, 0** |
| `Log2`, K=8 | 249.9 ns, 7 allocs | **29.2 ns, 0** |
| `Sin`, K=8 | 245.8 ns, 7 allocs | **24.8 ns, 0** |
| `Log`, K=12 | 238.1 ns, 7 allocs | **30.8 ns, 0** |
| `log(x)` veneer | 236.2 ns, 7 allocs | **28.2 ns, 0** |

Unchanged and correct: `Exp` 22.3 ns, `ArcTan2Pi` 35.8 ns (already inlining).
`Exp` at K=16 stays ~4.1 µs — rung 2 has no Float64 estimator by design
(`_yd1(f, x) = NaN` for non-Float64 operands, `oracle.jl:42–52`), so it always
runs the MPFR ladder. That is the documented rung-2 cost, not a regression.

### Steps 0–5 cumulative

| Row | Step 0 baseline | Now |
|---|---:|---:|
| `T8(1.3)` | 98.6 ns, 2 allocs | 1.4 ns, 0 |
| `T8(3)` | 583.0 ns, 28 allocs | 1.8 ns, 0 |
| `convert(T8, 1.3)` | 96.8 ns, 2 allocs | 7.2 ns, 0 |
| `FMA` K=8 | 451.9 ns | 12.7 ns |
| `Log` K=8 | 235.7 ns, 7 allocs | 27.5 ns, 0 |
| `Sin` K=8 | 245.8 ns, 7 allocs | 24.8 ns, 0 |

Not yet done, next up: Step 6 (broadcasting through the kernels — `A .+ B` is
still 631 µs against `vmap!`'s 15 µs at N=65,536, and `fma.(A,B,A)` improved
only because Step 4 fixed the scalar FMA), Step 7 (blocks), Step 8 (packed),
Step 9 (thresholds and latency), Step 10 (documentation close-out).

## implmentplan.md Step 4 done — FMA peels the Float64-exact product (2026-08-28)

Gate: full `Pkg.test()` green. `test-fastpaths` 764.

`ωeval(::Val{:FMA}, ::Float64, ::Float64, ::Float64)` widened to `Float128`
before it knew whether it needed to. Small formats multiply few significant
bits, so the product is usually exact in Float64 already — and then `x·y + z`
is just an exact two-operand sum that `Add`'s cascade resolves with the same
proofs. 452 ns for what `Add` does in 9.

- `src/ops/oracle.jl`: after the NaN/∞/zero rows and the `FAST_ARITH[]` escape,
  a Float64-only peel — `p64 = x * y`, and if `fma(x, y, -p64) == 0` the
  product is exact, so `return ωeval(Val(:Add), p64, z)`. Everything else falls
  through to the Float128 path untouched.
- **The magnitude floor is load-bearing, not defensive.** A nonzero residual
  `d = x·y − p` satisfies `|d| ≥ |x·y|·2^-106` (an exact product of two
  Float64s has ≤ 106 significant bits). Only above `|p| ≥ 2^-915` does that
  bound clear `floatmin`, making `fma(x, y, -p) == 0` a *proof*; below it the
  residual can itself underflow to zero and certify an INEXACT product. Found
  by a test assertion that failed — `2.0^-1060 * 2.0^-20` underflows and the
  first draft of the peel accepted it. New `const _FMA_EXACT_FLOOR`, with the
  derivation at the use site. Every rung-1 datum product clears the floor by
  ~130 binades (a rung-1 format has 2B ≤ 1024 and P ≤ 16), so it never fires
  in practice.
- `test/test-fastpaths.jl`: `both(FAST_ARITH, …)` over four WHOLE code cubes —
  `(5,2,S,E)`, `(4,2,S,F)`, `(6,3,U,F)`, `(5,4,S,E)` — plus directed cases for
  exact product/exact sum, exact cancellation, an inexact Float64 product, and
  both sides of the magnitude floor. Ad-hoc sweeps before committing: 2.4M
  triples over five formats and 8 projections, zero mismatches.

| Row | Before | After |
|---|---:|---:|
| `FMA` explicit ρ, K=8 | 451.9 ns | **12.7 ns** |
| `FMA` explicit ρ, K=12 | 458.0 ns | **18.3 ns** |
| `fma(x, y, z)` veneer | 453.1 ns | **13.3 ns** |

Noted, not acted on: `FAA` is still 166 ns. It has no Float64/Float128
specialization at all — the generic method goes straight to `_exact_sum3`. The
same shape of peel probably applies, but it is a separate change with its own
equivalence sweep.

## implmentplan.md Step 3 done — Integer conversion without BigFloat (2026-08-28)

Gate: full `Pkg.test()` green. `test-compat` 1,831,781 · `test-fastpaths` 755.

`Convert(fr, ρ, ::Integer)` built a `BigFloat` for every integer, however
small — 583 ns and 28 allocations for `T(3)`.

- `src/ops/scalar.jl`: `|x| ≤ 2^53` (new `const _F64_EXACT_INT`) now widens to
  `Float64` and reuses the `::Float64` method. The widening is EXACT at that
  magnitude, so the projection below it is still the one and only rounding —
  this is not a double rounding. Everything wider (BigInt, the top of
  Int64/UInt64) keeps the BigFloat route unchanged. The bound comparisons are
  exact for every Integer type, including `BigInt` and `UInt64`, because Julia
  compares mixed integer types by value rather than by a lossy promotion.
  Method is `@inline`; `Bool` and the sized integer types take the same path.
- `test/test-compat.jl`: NEW testset "Integer conversion is exact at every
  width" — 4 formats × 5 projections × 615 integers (all of −300:300, both
  sides of ±2^53, `typemax`/`typemin` of Int64 and UInt64, ±2^80 as BigInt,
  `UInt8`/`Int8`/`Int16`/`Bool`) against the BigFloat route evaluated at 4,096
  bits. All identical.
- `test/test-fastpaths.jl`: `@allocated T(3)` and `@allocated convert(T, 0x03)`
  are now 0 (the assertion deferred from Step 2).

| Row | Before | After |
|---|---:|---:|
| `T8(3)` | 583.0 ns, 28 allocs | **1.8 ns, 0** |
| `convert(T8, 0x03)` | allocated | **0 allocs** |

## implmentplan.md Step 2 done — constructor default-projection guard (2026-08-28)

Gate: full `Pkg.test()` green, no warnings. `test-fastpaths` 753.

The value constructor spelled its keyword default as
`projection::Projection = DefaultProjection()`. Julia evaluates that default on
every call, so every construction read the abstract `Ref{Projection}` and made
the dynamic, boxing call through it — 98.6 ns and 2 allocations to do work the
explicit `Convert(F, RTE_SN, 1.3)` does in 0.7 ns.

- `src/ops/scalar.jl`: the keyword is now
  `projection::Union{Nothing, Projection} = nothing`. `nothing` means "ask the
  session", and the ask carries the same **speculation guard** the generated op
  methods use (`scalar.jl:100–104`): `ρ === RTE_SN` is tested by identity and
  the literal constant is passed, so the untouched default is a static call.
  An explicit `projection = ρ` bypasses the read entirely. Method is `@inline`.
- `src/compat/base.jl`: `convert(::Type{T}, ::Unsigned)` got the same guard.
- `test/test-fastpaths.jl`: `@allocated` assertions for `T(1.3)`, `T(1.3f0)`,
  `convert(T, 1.3)`; plus behavior tests that the non-default branch is live
  (`DefaultProjection!(RTZ_SF)` changes the result) and that an explicit
  `projection =` keyword still wins.

| Row | Before | After |
|---|---:|---:|
| `T8(1.3)` | 98.6 ns, 2 allocs | **1.4 ns, 0** |
| `T8(1.3f0)` | 136.1 ns, 2 allocs | **1.6 ns, 0** |
| `convert(T8, 1.3)` | 96.8 ns, 2 allocs | **7.2 ns, 0** |

`convert` keeps a few ns over the direct constructor: it goes through
`convert(::Type{T}, ::Real) = T(x)` (`base.jl:366`), one extra hop. Zero
allocations, so it is left alone.

Deferred to Step 3: `convert(T, 0x03)` still allocates — an `Unsigned` is an
`Integer` and takes `Convert`'s BigFloat path. Its `@allocated` assertion is
written in Step 3, not here.

## implmentplan.md Step 1 done — benchmark harness (2026-08-28)

`benchmark/` is now a real, isolated suite. Chairmarks stays out of the
package's dependencies; the harness has its own `Project.toml` with a path
source on `..`.

    julia --project=benchmark -t 4 benchmark/runbenchmarks.jl          # all
    julia --project=benchmark -t 4 benchmark/runbenchmarks.jl scalar   # one

- Deleted `bench_floats{1,2,3}.jl` — three byte-identical copies of the same
  ad-hoc script.
- `benchmark/runbenchmarks.jl` NEW: `row(label, sample; elems)` (ns, allocs,
  bytes, and Gelem/s for array rows), `withflags(f; ...)` which sets and
  **restores in a `finally`** every mutable policy Ref (`FAST_ARITH`,
  `FAST_ENCLOSURE`, `THREADED_KERNELS`, `TABLE_EAGER_BITS`,
  `THREAD_MIN_ELEMS`, `DefaultProjection`) and empties the table cache, a
  header recording julia/threads/CPU/commit+dirty/policy values, and suite
  selection from `ARGS`.
- `benchmark/scalar.jl` NEW: codec and projection, construction, one operation
  per registry group at K=8, the same at K=12 and K=16 (rungs 1 and 2), the
  `FAST_ARITH=false` / `FAST_ENCLOSURE=false` reference rows, and the Base
  veneers.
- `benchmark/arrays.jl` NEW: `vmap!` table-gather vs compute (threaded and
  1-thread) at N ∈ {4096, 65536}, broadcasting, `sort`, cold `empty_tables!` +
  build with `evals=1`, packed storage, and blocks at B ∈ {16, 32}.

### Baseline recorded by this harness (i9-14900K, julia 1.12.6, 4 threads)

The rows Steps 2–8 exist to fix, at their pre-change values:

| Row | Before |
|---|---:|
| `T8(1.3)` / `convert(T8, 1.3)` | 98.6 / 96.8 ns, 2 allocs |
| `T8(3)` (Integer) | 583.0 ns, 28 allocs |
| `FMA` explicit ρ, K=8 / K=12 | 451.9 / 458.0 ns |
| `Log` / `Log2` / `Sin`, K=8 | 235.7 / 249.9 / 245.8 ns, 7 allocs |
| `A .+ B` K=8, N=65536 | 631,876 ns vs `vmap!` 15,524 ns |
| `fma.(A,B,A)` K=8, N=65536 | 30,795,071 ns |
| packed vs vector `vmap`, K=5, N=65536 | 52,348 vs 8,290 ns |
| `blockdecode` B=16 | 249.0 ns, 17 allocs |
| `BlockReduceAdd` / `BlockDotProduct` B=16 | 2,899 / 5,312 ns, 189 / 351 allocs |

Rows already good and worth not regressing: `project` 0.7 ns, `decode` K=8
1.4 ns, `Add`/`Multiply`/`Divide` 8.4–8.9 ns (session default 9.0 — the
speculation guard works), `Exp`/`Exp2` 22 ns, `vmap!` warm gather 4.2 Gelem/s,
K=12 compute 0.275 Gelem/s on 4 threads vs 0.070 on one (3.9x).

## implmentplan.md Step 0 done — hygiene (2026-08-28)

No behavior change. Gates: `test-tables` 1,007 · `test-ops` 816,706 ·
`test-compat` 1,819,475 · `test-quality` 35 — all pass, no overwrite warnings.

- `test/support/helpers.jl` NEW: `allcodes`/`subcodes`, included once via
  `isdefined(Main, :allcodes) || include(...)` from `test-compat.jl` and
  `test-fastpaths.jl` (they redefined them in the shared `Main`, so a full
  `Pkg.test()` printed `WARNING: Method definition ... overwritten`).
- `src/ops/registry.jl`: deleted the unreachable `op in (:CopySign,) ? :A`
  arm — `:CopySign ∈ _EXACT_SELECTION`, so the `:C` arm above it always wins.
  Group assignment is unchanged (asserted by the existing registry tests).
- `src/AIFloats.jl` module docstring: blocks and packed storage are no longer
  "staged next"; both are implemented and exported.
- `src/types/singletons.jl`: `SF`/`SP`/`SN` and `Projection` docstrings said
  the projection rules were "not implemented yet". They are, in
  `src/projection/saturate.jl`; each now states its actual rule.
- `src/arrays/blocks.jl:15`: the deferred-ports sentence now names what is
  really absent (the Float128 quotient cascade, the homogeneous-Float64 lane
  decode, integer-accumulated reductions = Step 7).
- `test/test-tables.jl`: NEW testset "ternary LRU spans both code widths" —
  a 4,096 B UInt16 ternary table then a 2,048 B UInt8 one under a 4,096 B
  budget; the older other-width table must be the victim. The eviction fix
  itself already existed (`cache.jl:84–118`); only the test was missing.
- `Project.toml`: dropped `SmallCollections` and `Statistics` from `[deps]`
  and `[compat]` (nothing in `src/` or `test/` uses them) and from the test
  target; `test-quality.jl`'s Aqua `stale_deps` ignore list shrank to match.

## State: ALL PHASES 0–7 COMPLETE + the deferred performance ports LANDED

Everything below is done, gated, and green. Read "Remaining phases" and
"Deviations" before continuing; the deferred performance ports are listed and
deliberate.

### Phase 0 done (all gates green: 8,966 tests, doctests pass)

- `src/types/constants.jl`: added `KMIN=3`, `KMAX=16` (IntParam), `DEFAULT_RBITS=8`.
- `src/types/binaryformats.jl`: `validformat` now `KMIN <= K <= KMAX` (ceiling in
  ONE place); docstring updated; `TrailingSignificantBitsOf` gained instance
  method and is now exported.
- `src/types/singletons.jl`: `ρRSA{N}`/`ρRSB{N}`/`ρRSC{N}` with
  `_check_nrandbits` inner-constructor validation (1..60); outer `ρRSA(N)`
  constructors; `const RSA = ρRSA{DEFAULT_RBITS}()` etc. so all 27 Projection
  constants unchanged; `isstochastic`/`nrandbits` on mode types/values and
  Projection types/values (exported, with jldoctests).
- `src/types/traits.jl` NEW: `ExponentBiasOf`, `ExponentBitwidthOf` (exported),
  `codemask` (via `_unitmask` by complement), `signmask`, `orderkeytype`
  (unexported). All with type+instance methods.
- `src/AIFloats.jl`: include traits.jl; exports extended.
- `test/test-traits.jl` NEW: 8,610 assertions — full 504-format grid (bit budget,
  bias = 2^(w−1), masks, key widths), ceiling, stochastic budgets.
- `test/test-binary-format.jl`: `(32,24,UNSIGNED,FINITE)` case → `(16,16,…)`
  (32 now exceeds the ceiling).

### Phase 1 done (gate green: 208,623 assertions; doctests pass)

- `src/carriers/heads.jl` NEW: Head/HeadF64/HeadF128/HeadExact, rungindex,
  joinhead, `_rungindex_span(2B)` (1024/16384 boundaries), `rung`,
  `datumcarrier` (**BigFloat placeholder at rung 3** until Dyadic, Phase 2),
  carrier-generic `_cnan/_cinf/_cninf/_czero`.
- `src/types/binaryvalue.jl` NEW: `BinaryValue{F,U}` (isbits; inner ctor checks
  U===CodeType(F) and code<=codemask; unchecked `rawvalue` is a global fn
  defined INSIDE the struct — the only door around the checks);
  `Base.codepoint` extension (NOT a new function — clashes with Base);
  `BinaryFormatOf`; trait forwarding loop (all format traits answer on datum
  type + datum).
- `src/content/codepoints.jl`: `nan_code` (signed: signmask ≡ the −0 slot;
  unsigned: codemask), `posinf_code`, `neginf_code`, `_maxfinite_code`,
  `_minfinite_code`; `MaxFiniteOf/MinFiniteOf/MinPositiveOf/MaxSubnormalOf/
  MinNormalOf` (values built FROM codes); `encode(F, sign, S, Q)` canonical→code.
- `src/content/floatvalues.jl`: `decodepolicy` (TableDecode UInt8 /
  ComputeDecode UInt16), `_decode_compute` (NaN tested FIRST), `_finite_datum`
  dispatched on code-unit seam (bit assembly → Float64 for UInt8; ldexp
  generic), `@generated` 2^K constant-tuple tables for K ≤ 8, `decode`,
  `_canonical(F,c)` integer-space field split.
- `src/content/datums.jl`: Base predicates (iszero/isnan/isinf/isfinite/
  signbit/issubnormal), `order_key` (NaN key 0 — NaN FIRST; key space has a
  deliberate GAP at signmask, keys ordered not contiguous), `FPClass`/`Class`,
  `NextGreaterThan`/`NextLessThan` as CODE arithmetic with explicit pivots
  (key±1 stepping falls into the gap — found and fixed during this phase).
- `src/compat/show.jl`: 4 styles (:value default), `set_show_style!`/
  `get_show_style`/`VALID_SHOW_STYLES`, IOContext override, ONE dispatcher
  behind both show methods; datum-type shows as alias name with TypeVar guard.
- `src/rules/constraints.jl`: `formatname`, `_NAMED` registry, 504 lowercase
  aliases = datum types (`binary8p4se === BinaryValue{Binary(8,4,SIGNED,EXTENDED),UInt8}`),
  `Formats` opt-in submodule.
- `src/content/gentables.jl`: real `codetable`/`printcodetable` (by=:code|:value).
- `src/AIFloats.jl`: rewritten module root — include order per plan §7, new
  exports, K ≤ 8 alias export loop, module docstring updated.
- Tests NEW: `test-binaryvalue.jl` (132,857) — construction discipline,
  predicates, total-order walk (NextGreaterThan visits all 2^K exactly once,
  NextLessThan inverts), classification, show styles, aliases;
  `test-codec.jl` (66,700) — **exhaustive 7,602,160-code-point sweep of all 504
  formats**: `_canonical`∘`encode` round-trip + decode ≡ sign·S·2^Q in
  Rational{BigInt}; layout spot checks (0x45→1.625 on binary8p4se); monotone
  decode.
- `docs/src/50-status.md` rewritten to the new truth.
- Suite totals: Binary Format 122 · Binaryvalue 132,857 · Codec 66,700 ·
  Singletons 334 · Traits 8,610. Doctests pass.

### Corrections made mid-phase (worth knowing)

- `codepoint` must EXTEND `Base.codepoint`, else export clash with Base.
- binary3p1uf value table is [0,⅛,¼,½,1,2,4,NaN] (B=4) — an early docstring/
  test had it shifted one octave up. binary8p4sf MaxFinite = 240 (not 248);
  binary8p4uf MinPositive = 2^-18.

## Phase status

| Phase | Status |
|---|---|
| 0 groundwork | **DONE** |
| 1 datum+codec | **DONE** |
| 2 projection | **DONE** (generic family; see deviations) |
| 3 ops | **DONE** (scalar register; see deviations) |
| 4 tables/kernels | **DONE** |
| 5 compat | **DONE** |
| 6 blocks/packed | **DONE** |
| 7 governance | **DONE** |

### Phase 2 done (gate green: suite total 6,683,101 assertions; doctests pass)

- `src/projection/rounded.jl`: `Rounded` (kind, sign, S, Q), KIND_* consts,
  `HUGEQ` finite-beyond-every-format sentinel, sticky protocol documented.
- `src/projection/round.jl`: the GENERIC rounding family — sticky-aware
  `_νgt/_νeq/_νge`, `_codeiseven` (P==1 → biased-exponent parity),
  `_νfloorscaled`/`_νrnite` stochastic helpers, one `_roundaway` method per
  mode (RSA/RSB/RSC take N from the type), `_rtp_core` with the step-down
  block and next-binade carry, `_floorexp` via frexp (subnormal-safe on every
  carrier), `round_to_precision` for Float64/Float128/BigFloat (BigFloat gets
  +8 guard bits).
- `src/projection/saturate.jl`: `saturate` returns a CODE POINT; `_extremal_SQ`
  from the maxfinite code; (Q,S)-lexicographic range test; `_saturate` rows for
  SF (clamps even genuine Inf) / SP (propagates genuine Inf only — over-large
  FINITE clamps) / SN (directed-back → extremal finite; extended spends Inf;
  else NaN).
- `src/projection/project.jl`: `project(F, ρ, X; R, sticky)` pipeline (exported,
  with jldoctests); `project_interval` Ziv loop, `_intervalcap = max(4096,
  bigprec+64)`.
- `src/carriers/bigprec.jl`: `bigprec(F) = 2(B+P)+64`.
- `test/support/refimpl.jl` NEW: independent ALL-BigInt reference — dyadic
  (num, q2) values, refround (pure shifts/compares, no floats, no shared
  code), refsaturate_code with independent encode; module RefImpl.
- `test/test-projection.jl` NEW (6,474,478 assertions):
  * rounding vs reference: every (P,B,S,E) cell of K ≤ 8, all 6 deterministic
    modes + 3 stochastic (N=3, all 8 R), eighth-step dyadic offsets at
    subnormal/mid/top binades + carry midpoints + deep under/overflow, ± —
    3,594,240 comparisons;
  * end-to-end project vs reference incl all 3 saturations + specials —
    2,163,024 comparisons;
  * carrier agreement (Float64 ≡ Float128 ≡ BigFloat code points);
  * idempotence on datums (projecting a datum is identity, all det modes ×
    sats, representative formats, every code);
  * interval oracle (π under RTE/RTZ/RTP/RTN, stochastic fixed-R, exact
    enclosure);
  * stochastic expectation (mean over full draw space ≈ value).
- `docs/src/50-status.md`: projection behavior moved to Implemented.
- Suite: Binary Format 122 · Binaryvalue 132,857 · Codec 66,700 · Projection
  6,474,478 · Singletons 334 · Traits 8,610.

### Phase 3 done (suite total 7,499,807 assertions; doctests pass; docs build green)

- `src/ops/registry.jl`: OP_REGISTRY (30 unary + 18 binary + 3 ternary +
  Convert), `factors` column, `_EXACT_SELECTION`/`_EXACT_ARITH`/`_QUOTIENT_OPS`/
  `_LADDER_OPS` (derived by exclusion), `opfactors` Val trait.
- `src/ops/oracle.jl`: the ωeval catalog — Group A exact (twosum fast case,
  exact-BigFloat escalation at derived precision), exact selections parametric
  in the carrier (IEEE-754-2019 extremum semantics, marked [interp]), quotient
  family (Float64 fma-exactness proof, else ladder; x/0 → NaN one-zero rule),
  Group B via directed-MPFR `Enclosure` closures (`_mpfr1/2`, `_mpfr_pitrig`
  4-combo, `_mpfr_divpi` sign-aware, `_mpfr_halfpi`), π-trig exact `_mod2` +
  Niven quarter-integer peels, Exp2/Log2 exact-power peels, **Softplus split
  form** (`x + log1p(exp(-x))` for x > 0 — the plain form overflows MPFR's
  exponent range at rung-2/3 maxfinite; found by the totality sweep).
- `src/ops/scalar.jl`: `_drawR` (pure ρ never touches RNG), `_finish`
  (carrier → project; Enclosure → project_interval), `apply_op`, the generated
  register (`Op(F, ρ, x...)` + datum-type-as-F + same-format under
  DefaultProjection, all exported), `Convert` (datum/Float64/32/16/BFloat16/
  Float128/BigFloat/Integer; Rational+Irrational REFUSED), and the
  `BinaryValue{F,U}(x::Real; projection, rng, R)` value constructor.
- `src/rules/defaults.jl`: `_DEFAULT_PROJECTION` Ref + coupled setters
  (DefaultProjection!/DefaultRoundingMode!/DefaultSaturationMode!); consumer
  reads ONE Ref.
- `src/compat/rand.jl`: rand (RTZ_SN floor semantics, `< 1` guaranteed,
  SamplerTrivial hook so `rand(T, dims)` works), randn (RTE_SF, signed only),
  seeded-stream reproducibility incl stochastic ρ drawing from the same rng.
- `test/test-ops.jl` (816,706): exhaustive Add/Subtract/Multiply vs the BigInt
  reference over ALL code-point pairs of every K ≤ 5 format × 4 rounding × 3
  saturation modes (815,616 comparisons); G10-style totality sweep (every op ×
  every rung rep × datums incl specials — this is what caught Softplus);
  known-value checks (e→2.75, ln2→11/16, sin1→13/16 on binary8p4se; peels;
  extremum corners); defaults coupling; value construction; rand/randn.
- `test/Project.toml`: + Random.
- `docs/src/95-reference.md`: + explicit `@docs AIFloats.Formats` block
  (submodule docstring is not reached by `@autodocs Modules=[AIFloats]`).
- `docs/src/50-status.md` + module docstring updated to the new truth.
- Suite: Binary Format 122 · Binaryvalue 132,857 · Codec 66,700 · Ops 816,706 ·
  Projection 6,474,478 · Singletons 334 · Traits 8,610 = **7,499,807**.

### Phase 4 done (tables 998 + kernels 34 assertions green at 1 and 4 threads)

- `src/tables/cache.jl`: `TableKey`/`TernaryKey` (all-value keys), TWO caches
  per arity selected by DISPATCH on `CodeType(fr)` (`Memory{UInt8}` vs
  `Memory{UInt16}` — a `Union` return would put a type check in every hot
  loop), one `TABLE_LOCK`, ternary `TernaryEntry` LRU (tick stamps; eviction
  spans both code-unit caches), accounting (`table_bytes/table_count/
  ternary_count/table_keys/empty_tables!` — all through one path so
  conformance can never under-report).
- `src/tables/policy.jl`: the two budgets — `TABLE_MAX_BITS` (memory, log2
  bytes, compared AS BITS so `1 << ΣK` is never materialized) and
  `TABLE_EAGER_BITS` (time, log2 entries); ternary eager(18)/adaptive(21,
  earned at `TERNARY_BUILD_ELEMS` = 2M elements)/never bands + 32 MiB LRU
  byte budget; `get_table` (contract: return a table or THROW — stochastic ρ
  and over-byte-budget refuse loudly, naming the numbers) vs `table_for`
  (kernel gate: table or `nothing`, no prejudice); `table_policy`
  introspection reads the same predicates the kernels do; `_cached_table`
  double-checked lock pattern (build OUTSIDE the lock; racing duplicate
  benign).
- `src/tables/build.jl`: `_scalar_code` = one trip through the SAME path
  Shape B runs (via `_kernel_result`; Convert = bare projection, R = 0 safe —
  stochastic never reaches a builder); `_operand_datums` by decodepolicy
  (tuple for UInt8 formats, materialized vector for wide operands inside
  affordable tables); `Val(op)` passed as ARGUMENT into `_fill_unary!/
  _binary!/_ternary!` (the 13× function-barrier lesson); threaded fill
  partitioned over the OUTER code loop (contiguous spans), gated by
  `TABLE_BUILD_MIN_ENTRIES` (2^12) + `THREADED_TABLE_BUILDS`; sound because
  pure-ρ only + MPFR setprecision function-form is ScopedValue/task-local on
  Julia ≥ 1.12 + builds already run outside the lock.
- `src/arrays/kernels.jl`: `_kernel_result` (registry ops → apply_op;
  `Val(:Convert)` → bare project) serving builders and both kernel shapes;
  `vmap!`/`vmap` (EXPORTED) — Shape A gather (unary `c+1`, binary
  `(c1<<K2)+c2+1`, ternary via `_ternary_table_for` with element count),
  Shape B compute loops that thread (`THREAD_MIN_ELEMS` 2^15,
  `_should_thread` written ONCE, unit-range only); the STOCHASTIC kernel is a
  separate sequential FUNCTION (single rng stream, index order — carried by
  which-function-you-are-in, not a hoistable branch); registry-generated
  array surface `Op(F, ρ, A...)` + datum-type-as-F + same-format under
  DefaultProjection; `Convert` array forms (datum arrays ride the gather;
  Float16/32/64/BFloat16 arrays run Shape B with exact widening).
- `src/AIFloats.jl`: includes wired per plan §7 (after ops/scalar.jl, before
  compat/rand.jl); `public` grew get_table/table_for/table_policy/
  table_bytes/table_count/table_keys/empty_tables!; vmap/vmap! exported.
- `test/test-tables.jl` NEW (998): table entries ≡ scalar path exhaustively
  (unary/binary/Convert × 3 projections, mixed formats, UInt16 cache);
  BOTH budget refusals + `table_for` declining without throwing; policy
  agreement; ternary eager/adaptive earning/LRU eviction; accounting +
  cache-hit identity.
- `test/test-kernels.jl` NEW (34): Shape A ≡ Shape B MEASURED (all 1024
  operand pairs of 5p3se × {Add,Multiply,Divide} × 3 projections; 5 unary
  ops; FMA; cross-format); threading-changes-nothing (forced threaded vs
  sequential on a wide 9-bit compute path); stochastic kernel reproducible
  AND stream-identical to the scalar-call sequence, builds no table; vmap
  surface incl DimensionMismatch refusals; Convert array forms; warm-path
  allocation pinned LENGTH-INDEPENDENT (100 vs 100,000 elements allocate
  identical bytes).
- `docs/src/50-status.md`: kernels + tables moved to Implemented.
- Full `Pkg.test()` and docs build deliberately NOT rerun yet (user
  directive: once, after all phases).

### Phase 5 done (compat 1,819,475 + quality 28 assertions green; Aqua + JET clean)

- `src/carriers/heads.jl`: `promotecarrier` trait (public; Float64/Float128/
  BigFloat by rung — never the internal carrier); forwarded on datum types
  with `rung`/`datumcarrier` in binaryvalue.jl's trait loop.
- `src/compat/base.jl` NEW: (1) Base veneers from the registry — `_BASE_UNARY`/
  `_BASE_BINARY`/`_BASE_OPERATOR`/`_BASE_TERNARY` + `_NO_BASE_COUNTERPART`
  (partition asserted exhaustive over OP_REGISTRY), composites sincos/sincospi/
  minmax, `Op(ρ, x)` / `Op(ρ, A)` projection-first convenience for unary ops;
  (2) NaN-first `isless` on order_key, `==`/`<`/`<=` unordered on NaN,
  `CodeCountingSort` (defalg for datum arrays; counts only at length ≥ 2^K,
  Forward/Reverse only, else DEFAULT_UNSTABLE), nextfloat/prevfloat =
  NextGreaterThan/NextLessThan; (3) AbstractFloat contract — zero/one/eps(T)/
  typemin/typemax/floatmin/floatmax/precision, `decompose` from
  round_to_precision (pure extraction on a datum) so hash/Dict/Set work,
  widen = promotecarrier, exponent/significand (refused when B == 1 extended —
  binade [1,2) truncated by Inf)/frexp/ldexp/eps(x) (ulp = 2^Q), round/floor/
  ceil/trunc + per-mode `round(x, RoundX)` (one method per Base mode — a
  generic one is ambiguous), `_unsupported` refusals for rem/mod/
  RoundNearestTiesUp/RoundFromZero; (4) conversions Float64/32/16/BFloat16/
  Float128/BigFloat/Integer/Bool, `convert` with VALUE semantics for Unsigned
  (plan §4 exception), `BinaryValue{F}(x::Real)`, identity ctor, Rational
  refused with EXACT-signature methods (`Rational{R}` typevar — the loose
  form is ambiguous with Base's AbstractFloat(::Rational)), promote_rule →
  promotecarrier (Float128/BigFloat joins); (5) `similar` (3 signatures:
  Base fixes the dimension) normalizing `BinaryValue{F}` to the concrete
  type, checked `reinterpret`.
- `src/types/binaryvalue.jl`: `BinaryFormatOf(::Type{Union{}})` throws —
  JET's whole-package pass probes the bottom type through the forwarding loop.
- `src/ops/scalar.jl`: `nrandbits(ρ)::Int` in `_drawR` (JET widening).
- `src/AIFloats.jl`: include after arrays/kernels.jl, before compat/rand.jl;
  `public` + promotecarrier, CodeCountingSort; module docstring updated.
- `test/test-compat.jl` NEW: partition; veneers ≡ register over ALL 32×32 pairs
  of 5p3se for every mapped op (session default honored); NaN-first pins
  (isless/==/hash/Dict; sort both paths + rev + sortperm on 8p4se/5p2uf/9p4se);
  constants on all 504 formats; decompose reconstructs every datum (Rational{
  BigInt}) on 5 formats incl rung 2 and 3; exponent family vs carrier; round
  family vs BigFloat on every finite datum, all 5 Base modes; refusal messages;
  conversion/promotion at all 3 rungs; similar/reinterpret; @inferred pins.
- `test/test-quality.jl` NEW: Aqua.test_all (stale_deps ignores Aqua/JET/
  PrecompileTools/SHA/SmallCollections/Statistics — declared in Project.toml
  ahead of use), JET report_package (0 reports), JET @test_call on 16 entries.
- `docs/src/50-status.md`: Base surface moved to Implemented.
- Existing suites rerun after the Base methods landed: Binaryvalue, Ops,
  Kernels, Tables — see "How to verify" (full Pkg.test still deferred).

### Phase 6 done (blocks 11,687 assertions green)

- `src/arrays/blocks.jl` NEW: `Block{B,S,E}` (datum types as parameters; B ≥ 1
  by signature), `blocksize`/`scaleformat`/`elemformat`, `==`/`isequal`/show;
  `_samecarrier` (lanes from different blocks may sit on different carriers —
  identical types pass, else exact lift to BigFloat); `blockdecode` (ωMultiply
  per lane); `_bp_element` (S-special rows, then the ONE cheap filter — a
  Float64 quotient certified by fma, which is what makes P == 1 scales exact —
  else `_encl_div_scale` directed-MPFR enclosure with an EXACT divisor at its
  own width, resolved by project_interval); `blockproject`; generated
  `BlockOp(FR, ρ, blocks..., sr)` and `ScaledOp(FR, ρ, (s, x)...)` for all 51
  ops (+ datum-type-as-format forms, all exported); reductions with exact
  BigFloat accumulators at DERIVED precision (`_lane_sum_prec`/
  `_lane_prod_prec`); ConvertFromBlock/ConvertToBlock/
  ConvertToBlockMaxAbsFinite (NaN seed at the fold's carrier); `BlockVector`.
- `src/arrays/packed.jl` NEW: `PackedVector{T}` (64-bit words, mask by
  complement, cross-word splice), `packing_saves`, `PACK_TILE` = 256,
  `vmap(op, F, ρ, pv)` tile loop (one rng across tiles ⇒ stream-identical to
  the unpacked call).
- **Phase 3 defect found by the block gate**: `ωeval(MaximumFinite/
  MinimumFinite)` returned NaN when neither operand was finite; the draft's
  §4.11.3 table says infinities beat NaN and two infinities compare. Fixed in
  ops/oracle.jl (ConvertToBlockMaxAbsFinite NOTE 2 depends on it).
- `test/test-blocks.jl` NEW: blockdecode vs lane reference; BlockAdd/BlockExp
  vs a 3000-bit reference composition over B ∈ {1,2,3,16,32} × 3 ρ × 2 scale
  formats (E8M0 included), rung-3 scale; S-special rows; ScaledOp ≡ B=1 BlockOp
  (Add/Divide/FMA); reductions vs references; the five NOTEs; stochastic
  reproducibility; BlockVector; packed round trip exhaustive over n ∈ 0:70 for
  9 formats incl UInt16-coded, vmap-through-packed ≡ unpacked (pure and
  stochastic).
- Test-reference lesson: MPFR `exp` underflows to exactly 0 past its exponent
  floor; a reference must substitute a positive infinitesimal or directed modes
  disagree with it (implementation was right).

### Phase 7 done (governance 330 assertions green)

- `src/rules/approx.jl` NEW: `codedistance`, `measure_kappa` (exhaustive ≤ 2^22
  inputs else sampled and SAID so; stochastic ρ refused), `ApproxImpl`,
  `APPROX_REGISTRY` + lock, `register_approx!` (understatement rejected; NaN κ
  needs explicit `κ = NaN`), `approx`/`kappa`/`kappa_measured`/`list_approx`/
  `unregister_approx!`, `ftz_variant` (Annex worked example).
- `src/rules/conformance.jl` NEW: `DRAFT_IDENTITY` (retained
  `docs/other/IEEE_D1.md`, sha256 checked by the suite), `_ROUNDING_MODE_
  DECLARATIONS`/`_SATURATION_MODE_DECLARATIONS` (declared, never `subtypes`),
  `_INTERPRETATIONS` (the oracle's [interp] marks), `ConformanceDeclaration`,
  `conformance()` live from OP_REGISTRY + `table_keys()` (both caches) + κ
  registry, `conformance_dict`, `conformance_report` (K range read from
  KMIN/KMAX).
- `docs/other/IEEE_D1.md`: the draft transliteration retained from SmallFloats
  (same digest).
- `src/AIFloats.jl`: PrecompileTools workload (hot scalar/Base/array/block/
  packed entries at 8p4se + one rung-2 and one rung-3 format; `empty_tables!`
  at the end so the image carries no table); includes + exports for Phases 6–7.
- `test/test-governance.jl` NEW; `test/Project.toml` + SHA.

### Performance ports done (dyadic 268,530 · rounding-paths 35,427,476 · fastpaths 744 · quality 35)

- `src/carriers/dyadic.jl` NEW: `DyadicNumbers` adapted from SmallFloats
  (provenance header: commit 7f864f08, 2026-08-27; algorithms unchanged;
  AIFloats additions marked — copysign/isone/significand/frexp/
  RoundNearestTiesAway/Integer/Bool for the Base veneers at rung 3).
  `<: Real`, not AbstractFloat; `float(::Dyadic)` deliberately undefined.
- `src/carriers/fma128.jl`, `faa128.jl` NEW: vendored verbatim with headers
  (`Float128FMA`/`Float128FAA` submodules; `fma128`/`faa128` public).
- `src/carriers/heads.jl`: `carriertype(HeadExact) = Dyadic`; `CarrierValue`
  union; `_cnan…` rows for Dyadic; `_isposinf/_isneginf` (moved from blocks);
  `lift` (UPWARD ONLY — absence of narrowing asserted); `_headof/_joinheads`;
  Float128/BFloat16 from Dyadic.
- `src/ops/registry.jl`: `rung(op::Val, Fs...)` — join of operand bound and
  monomial bound (`opfactors`).
- `src/projection/round.jl`: the fixed-point family `_rab` (UInt128 fraction +
  `lost`), `_rtp_f64` bit path (normal Float64 inputs; specials/zero/subnormal
  to the core), `_rtp_dyadic` (shift-out ν), `_rtp_zero_sticky`; Float64 and
  Dyadic entry points. **Gate** test/test-rounding-paths.jl: bit ≡ generic
  over every (P, B) cell × 14 modes (stochastic N ∈ {1,3,8,60}, every R at
  small N) × both stickies × boundary-structured inputs — 11.8M comparisons;
  Dyadic ≡ generic 23.6M (incl. un-normalized spellings and rung-3-range
  values vs the BigFloat core); zero-sticky row; carrier agreement.
- `src/ops/oracle.jl`: `Sticky{T}` result (one neglected tail of known
  direction; sound because DYADIC_ALIGN_MAX 94 > P+N+2 ≤ 77 — `_STICKY_MIN`);
  Dyadic-native Add/Subtract/Multiply/FMA/FAA (FAA drops to exact MPFR when
  a sticky would have to compose); Dyadic → BigFloat fallbacks generated for
  every ladder/quotient op; selections typed `::CarrierValue`; `_nosticky`
  for block lanes (the sticky protocol does not survive division by a scale).
  **Fast layers**: `Enclosure{F,G}(f, fq, yd)` with eager Float64 (2^-45) and
  Float128 (2^-90) envelope stages, built only for Float64 operands (`_fq1/
  _fq2/_yd1/_yd2`, guarded); Group A on Float64/Float128 with DIRECT proofs
  (twosum128 residual, fma residual) then `Sticky` past `_STICKY_MIN`
  (`_sum_wide`, `_faa_wide` distillation) then exact BigFloat; quotient rows
  carry their CR quotient as `yd`; π-trig rows carry the Base `*pi` natives.
  Switches `FAST_ARITH`/`FAST_ENCLOSURE` (Refs) — disabling costs speed only.
- `src/ops/scalar.jl`: staged `_finish(Enclosure)`; `apply_op` with the
  explicit `res isa Float64` union split and `@noinline _finish_slow`;
  `Vararg{Any,N}`. The same-format convenience methods (scalar and array)
  now carry the plan's SPECULATION GUARD for real: `ρ === RTE_SN` → call with
  the literal constant (the Ref{Projection} read is abstract; without the
  guard `Add(a, b)` boxed 48 B per call — found by the allocation pin).
- `test/test-quality.jl`: `_vmap_packed` exempted from the package-wide JET
  pass (known generic-parameter widening) and verified by concrete
  `@test_call`s instead; rung-2/3, FAA, and block entry points added.
- **Phase 3 defects found by the gates**: (a) `ArcTan2`/`ArcTan2Pi` rows did
  not follow the draft table — `(0,0)` and `(±∞,±∞)` must be NaN, and the axis/
  infinity rows are exact constants (½, 1, −½, −1 are GRID POINTS the interval
  ladder can never resolve — `project_interval` threw at 4096 bits; the fast
  layer had been hiding it). Rewritten row for row, in table order, with
  `_mpfr_pi`. (b) `MinNormalOf(::Type{Union{}})` etc. guards for JET.
- `src/arrays/packed.jl`: output datum type as a type parameter of the tile
  loop (JET-clean views).
- `test/support/dyadic_digest.jl` (module-parametrized digest sweep),
  `test/support/dyadic_capture.jl` (run against SmallFloats),
  `test/support/dyadic_golden.sha256` (captured 2026-08-28);
  `test/test-dyadic.jl` (golden ≡, carrier contracts incl. the add-band
  coverage assertion, lift/rung(op) lattice, fma128/faa128 vs libquadmath and
  an exact reference at derived precision); `test/test-rounding-paths.jl`;
  `test/test-fastpaths.jl` (FAST_ARITH ≡ exact over ALL pairs of 8p1uf (B=128,
  spreads cross the sticky band) and 8p2se × 7 modes incl. stochastic at fixed
  R, triples on subsets, rung-2 subsets; FAST_ENCLOSURE ≡ ladder-only over
  every code point of 5 formats × every ladder/quotient op × 4 modes, binary
  ladder ops on subsets; the stages are built for Float64 and dropped for
  wide operands; zero warm-path allocation on Add/FMA and the compute kernel).
- Measured (this machine): 8p4se `Exp` 90 ns (ladder-only 4.7 µs), `Sin`
  357 ns (4.8 µs); 8p1uf wide-spread `Add` 146 ns (exact-BigFloat 951 ns);
  16p1se (rung 3, Dyadic) `Add` 96 ns, `Multiply` 93 ns, `decode` 13 ns, all
  0 bytes; rung-3 `Exp` still the MPFR ladder (4.5 µs) — the recorded
  property of that tier.
- Test-side lessons: stochastic ρ needs an explicit `R` when comparing two
  paths (different draws are not a disagreement); Dyadic has no promotion, so
  compare through `BigFloat`/`Rational{BigInt}`; a fixed-precision BigFloat
  reference for `fma128` was wrong on wide-exponent operands — derive the
  precision from the exponent span.
- `docs/structuralplan.md` §7 rewritten to the real include order (lift.jl
  and protocol.jl did not become files: `lift` lives in heads.jl, the result
  protocol is `Sticky`/`Enclosure` in oracle.jl).

### Post-port review fix (tables 1,003)

- `src/tables/cache.jl`: ternary LRU eviction claimed to span both code-unit
  caches (the byte budget is one number) but selected victims only from the
  current result-width cache and stopped when THAT cache emptied — a UInt16
  table could never be evicted by a UInt8 insert (and vice versa), and the
  budget was silently exceeded. Now `_evict_oldest_ternary!` takes the
  globally least-recent entry of either cache; the loop guard is "both
  empty". Pinned by a cross-width case in `test/test-tables.jl` (older UInt16
  table evicted by a UInt8 insert under a 6 KiB budget, then the reverse).

## Remaining work

- Nothing from the plan. Candidates: BigExactF-style deferral of exact
  BigFloat escalations (SmallFloats has it; here the escalation is eager),
  the P == 1 exponent-add `blockdecode` fast path and the Float128 division
  cascade in `_bp_element` (blocks still use one exact-quotient filter then
  the interval), Float128 filters in the block reductions, BMI2 packed tiles.

## Deviations from the plan so far

1. `carriers/heads.jl` landed in Phase 1 (decode needs `datumcarrier`), with
   BigFloat as the rung-3 carrier until the performance ports replaced it with
   Dyadic (BigFloat remains the differential oracle in the gates).
2. Phase 2 shipped the generic rounding family only; the bit path and the
   fixed-point family landed with the performance ports, pinned bit-identical.
3. `rules/constraints.jl` (aliases) landed in Phase 1, not Phase 0/3 — the
   aliases needed `BinaryValue` to exist.
4. `codepoint` is `Base.codepoint` extended, not a new export (Base owns the
   name for `Char`).
5. Phase 3 shipped without the performance layers; they landed afterwards
   (see "Performance ports done"). BigExactF-style DEFERRAL of the exact
   BigFloat escalation was not ported — the escalation is eager here.
   `rules/defaults.jl` and `compat/rand.jl` landed in Phase 3 as planned.
6. `lift` lives in heads.jl rather than its own file; `fma128/faa128` are
   vendored submodules under carriers/.

## How to verify current state

All phases complete: full `Pkg.test()` and the docs build are the standing gate.
Recapturing the Dyadic golden digests (only after a reviewed semantic change):
`julia --project=$HOME/github/SmallFloats.jl test/support/dyadic_capture.jl`
with `AIFLOATS_DYADIC_OVERWRITE=1`.

```bash
julia --project=. -e 'using Pkg; Pkg.test()'        # ~7.5M assertions, ~3 min
julia --project=docs docs/make.jl                    # docs + doctests
```
