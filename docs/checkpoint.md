# Enactment checkpoint

*Session log for picking up without redoing work. Two plans are tracked here:
[improveapi3.md](improveapi3.md), in progress, and
[structuralplan.md](structuralplan.md) with
[implmentplan.md](implmentplan.md), complete. Newest entry first within each.*

---

# improveapi3.md — progress

Updated as each step completes. A step is "done" only when its own gate is
green; anything short of that is recorded as in progress with what is missing.

| Phase | State | Gate |
|---|---|---|
| 0 — freeze contract, inventory | **done** | inventory recorded below |
| 1a — add `fromcode`/`_rawvalue`, migrate callers | **done** | 10 focused test files green |
| 1b — diagnostic trap for missed unsigned construction | **done** (not committed, by design) | focused groups + doctests |
| 1c — canonical format/datum model | **done** | ambiguity + inference clean |
| 2 — scoped projection default | **done** | zero alloc steady state; scoped/nested/task tests |
| 3 — scalar/array conversion parity | **done** | edge-population code-point equality |
| 4 — queries and `formatinfo` | **done** | type stability, no Base shadowing |
| 5 — table service | **done** | coherent snapshots under concurrency |
| 6 — packed serialization and collections | **done** | round trips, aliasing, Aqua ambiguities |
| 7 — registry validation and error taxonomy | **done** | one validation per call, not per element |
| 8 — residue removal and consumer alignment | **done** | zero residual deleted forms |

## Phase 8 — done (2026-09-01)

**Residue scan.** Every deleted form is at zero in live code; the only remaining
matches are comments explaining the removal and negative assertions pinning it:

| Form | Live occurrences |
|---|---|
| `BinarySpecifier`, `_formattype` | 0 |
| `::Binary` instance methods | 0 |
| `F()` format tokens | 0 |
| public `rawvalue` | 0 |
| projection setters | 0 (3 `@test !isdefined` + 1 docstring mention) |
| `table_bytes`/`table_count`/`ternary_count`/`table_keys` | 0 (1 `@test !isdefined` loop + 1 comment) |
| `PackedVector{T}(words, n)` | 0 (1 `@test_throws MethodError`) |

**`docs/structuralplan.md` is revised, not silently left wrong.** It recorded
the total instance surface and the bridge rule as *deliberate design*; leaving
that would have made the documented interface contradict itself. Invariant 4
and §9.2a are now marked superseded, with the original text kept — the
reasoning is what justifies the removal, and the failure it describes (a bridge
written as a self-recursion Julia cannot diagnose) is real and will recur in
any future two-spelling surface. A "What replaced it" note states the trade
plainly: keeping an instance surface total is a standing obligation on every
method anyone adds; removing the instances discharges it once.

**Examples.** Every code literal is now visibly introduced by `fromcode` —
`40-technical.md`'s `T[T(UInt8(c)) for c in …]` was the last site where an
unsigned literal silently meant a code point. `40-technical.md`'s cache example
uses the one `table_stats()` snapshot, and `30-advanced.md` gained a portable
wire-form section.

**Version 0.2.0 and a CHANGELOG that names every break** with its direct
replacement, grouped by the reason for the break, plus a five-step migration
checklist. The entry states the one thing a reader most needs: the `Unsigned`
change is the most likely to be *silently* wrong, because both spellings still
compile — `T(codepoint(y))` used to reinterpret and now converts. Classify each
site; do not rewrite mechanically.

---

# `convert(T, x)` at 14.1 ns, and a benchmark convention that was lying (2026-09-01)

The published `convert(T8, 1.3)` row read **14.1 ns** against `T8(1.3)`'s
**3.5 ns**, for two spellings that reach the same constructor. Two causes, one
real and one a measurement artifact — and the artifact was the larger.

## The real cause: `convert` was the only uninlined seam

```julia
Base.convert(::Type{T}, x::Real) where {T<:BinaryValue} = T(x)    # before
@inline Base.convert(::Type{T}, x::Real) where {T<:BinaryValue} = T(x)::T   # after
```

Every neighbour on that seam — the value constructors, `BinaryValue(F, x)`,
`Convert` — is `@inline` with a concrete return assertion. The three
`Base.convert` methods were not. So `convert` stayed an out-of-line call: it
could not fold where a literal source makes folding legal, and it did not hand
the caller a concrete result type.

Measured per call on a **non-constant** source (loop difference, 64 vs 4096
iterations, so nothing hoists):

| | before | after |
|---|---:|---:|
| `T8(v)` | 6.10 ns | 6.40 ns |
| `convert(T8, v)` | 7.39 ns | **6.42 ns** |

The gap is gone. On the literal form the same change reads 14.1 ns → 1.93 ns,
because `convert` can now fold exactly as its neighbours already did.

## The artifact: literal sources fold, and the suite was measuring the fold

`@b T8(1.3)` and `@b Convert($F8, RTE_SN, 1.3)` write the value as a **literal**.
Chairmarks interpolates `$F8` but not the number, so the compiler constant-folds
the entire projection and the row reports the fold. `Convert(F8, RTE_SN, 1.3)`
read **1.3 ns** — for a projection that actually costs 6.3.

That is why the 14.1/3.5 gap looked like a 4× defect: one of the two was
inlinable and therefore foldable and the other was not, so the row was
comparing folding against not-folding rather than work against work.

**Fix: every measured value in the scalar suite is now interpolated.** The
construction and projection rows changed accordingly, and now agree with each
other arithmetically:

```
project Float64 → K=8            6.3 ns     the projection itself
Convert(F8, RTE_SN, v)           6.3 ns     explicit ρ, no default read
T8(v)        (Float64 value)     7.6 ns     + the scoped-default guard
convert(T8, v)                   7.6 ns     identical, as it should be
fromcode(T8, c)  (code point)    2.1 ns     no projection at all
```

6.3 + ~1.3 = 7.6. Before the change those five rows could not be reconciled at
all, which is itself the tell.

## The generalizable rule, now twice-earned

This is the same trap as the allocation isolation, from the other side.
**`const` or literal arguments** let the compiler hoist boxes and fold work, so
such a measurement **understates** cost — for allocations and for time alike.

Neither honest method is exact on its own, and they bracket the truth from
opposite sides:

| Method | Bias | Why |
|---|---|---|
| loop difference, `(t(n₂) − t(n₁)) / (n₂ − n₁)` | **under** | anything loop-invariant hoists out — including the `ScopedValue` read |
| Chairmarks with interpolated values | **over** | the harness reloads each interpolated value from closure state per iteration |

Measured spread on the scoped `Add(x, y)` seam: 36 ns by loop difference, 77 ns
by interpolated Chairmarks. Both are *correct* for a real caller — the first
describes a loop over many calls, the second an isolated one. Quote which was
used; do not treat either as the number.

What neither method distorts is a **ratio between two rows measured the same
way**, which is why the benchmark page says to read it that way and why the
`convert`/constructor comparison above is trustworthy at 7.6 ns against 7.6.

# The guard ladder: what it took, and what it could not reach (2026-09-01)

Question asked: can a scoped `RoundToOdd` or `RoundTowardZero` `Add` run nearly
as fast as the `RTE` one? Built it and measured, because the previous entry's
argument against it was an unmeasured one.

## What it is

`_GUARDED_PROJECTIONS` in [`ops/scalar.jl`](../src/ops/scalar.jl) lists all 27
exported projection constants. The generator emits one identity arm each:

```julia
ρ === RTZ_SN && return Add(BinaryFormatOf(T), RTZ_SN, x1, x2; rng, R)::T
```

A matched arm is a **static** call, so there is no dynamic dispatch and
therefore none of the `arity + 1` boxes it entailed.

## Measured, per call in a loop

| | before | after |
|---|---|---|
| scoped `Add(x, y)` | 76.5 ns, 48 B | 26.9 ns, **0 B** |
| unscoped RTE `Add(x, y)` | 8.8 ns, 0 B | 9.2 ns, 0 B |
| explicit `Add(F, ρ, x, y)` | 7.7 ns, 0 B | 7.6 ns, 0 B |
| precompilation | 9.5–11 s | 9.6 s |
| first scoped `Log` (TTFX) | 404 ms | 369 ms |

Allocations are gone on every laddered projection, including the stochastic
ones. Nothing else regressed.

## The residual is `Base.ScopedValues`, not us

Subtracting the scoped read from the seam leaves a constant:

| | read | `Add` | difference |
|---|---:|---:|---:|
| unbound | 0.53 ns | 9.22 ns | 8.7 |
| bound `RTZ_SN` | 16.96 ns | 26.91 ns | 9.9 |
| bound `RTO_SN` | 48.07 ns | 58.88 ns | 10.8 |
| bound `RTA_SP` | 35.11 ns | 43.44 ns | 8.3 |
| explicit ρ | — | 7.57 ns | 7.6 |

~8–11 ns in every case, against the explicit call's 7.6. **The arithmetic is
already at explicit-projection speed.** All of the remaining gap is
`ScopedValue` walking its scope: 0.53 ns unbound against 17–48 ns bound, a
30–90× difference that also varies per projection *identity* rather than per
arm position (`RTZ_SN` measured 17 ns in one run and 48 in another, with the
ladder unchanged).

So the answer to the question as asked is **no, and not for a reason this
package can fix**: a scoped non-RTE call cannot match the unscoped RTE one
while the bound read costs 20–90× the arithmetic. What the ladder does achieve
is that everything *after* the read is now identical to the explicit path.

For callers who need the explicit-ρ floor, that spelling still exists, is
1.2 ns faster than even the unscoped default, and does not depend on scope at
all.

## Would a `Ref` be faster than the `ScopedValue`?

Asked because the answer bears on whether Phase 2 traded away throughput.
Measured with the *same* two-arm ladder on both, so only the read differs:

| | read | full `Add` seam |
|---|---:|---:|
| `Ref[]`, holding the default | ~0 ns (hoisted) | 8.67 ns |
| `ScopedValue[]`, unbound | 0.53 ns | 9.03 ns |
| `Ref[]`, set to `RTZ_SN` | ~0 ns (hoisted) | 8.09 ns |
| `ScopedValue[]`, bound to `RTZ_SN` | 23.47 ns | 32.90 ns |

**At the default the two are the same** — 8.7 against 9.0 ns, noise. That is the
path the overwhelming majority of calls take.

**Under a non-default projection the `Ref` is ~4× faster**, entirely because its
read is a plain memory load the optimizer can hoist, while a `ScopedValue` read
goes through `Core.current_scope()`, which is opaque to it. So Phase 2 did cost
throughput, but only on the path a caller reaches by explicitly asking for a
non-default projection.

That cost was known and is not the deciding term. A projection changes numeric
**results**, so a process-global `Ref` lets two concurrently running tasks fight
over what arithmetic means — silently, and with no way for either to notice.
Correctness of concurrent work is not tradeable against 24 ns.

A caller who needs both task safety and the floor has the explicit spelling,
which reads nothing at all: 7.6 ns, less than either default path.

## Coverage: which seams get the ladder, and which do not

`_GUARDED_PROJECTIONS` lists **all 27 exported projection constants** — every
one of the 9 rounding modes (`RTA`, `RTE`, `RTN`, `RTO`, `RTP`, `RTZ`, `RSA`,
`RSB`, `RSC`) crossed with all 3 saturation modes. Nothing exported is missing.
What cannot be covered is `Projection(ρRSA(n), σ)` at a non-default stochastic
budget: that is an unbounded family with no constant to match, so it falls
through to the barrier, which is why the barrier still exists.

Applying it to every *seam* is a separate question, and the answer is not
uniform:

| Seam | Laddered | Why |
|---|---|---|
| 51 generated scalar ops | **yes** | per-value; 76.5 ns/48 B → 26.9 ns/0 B |
| value constructor (`F(x)`, `T(x)`, `convert`) | **yes** | per-value; 35.9 ns/32 B → 25.8 ns/0 B |
| array op convenience `Op(A...)` | no | resolves once per call |
| `Convert(F, A)` | no | resolves once per call |
| broadcast `copyto!` veneers | no | resolves once per call |

### The constructor gap, and two ways to get it wrong

The constructor was the real omission — a per-value seam like the ops, still
paying 35.9 ns and 32 B under a bound projection. Two attempts failed first,
both instructive:

1. **A shared helper taking `::Type{F}`, asserting `::BinaryValue{F, CodeType(F)}`.**
   6.5 → **101 ns**. `CodeType(F)` in the assertion is a call the assertion
   cannot fold, so every arm paid a runtime type computation.
2. **The same helper with the witness argument, asserting `::BinaryValue{F,U}`.**
   101 → 15.5 ns, still allocating: a 27-arm body exceeds the inliner's budget,
   so the helper stayed an out-of-line call.

What works is what the op seam already does: **the arms written directly in the
method body**, with one ladder serving both the scoped default and the
`projection` keyword — which needed it too, being declared
`Union{Nothing,Projection}` and therefore just as abstract. Result: 25.8 ns,
0 B scoped; 6.7 ns, 0 B unscoped, unchanged.

### Broadcast: built, measured, reverted

Prototyped the ladder in the broadcast veneers and the two array seams.

**Benefit**, per call, stable across runs — a constant, because those seams
already resolve the default once:

| n | scoped overhead before | after | recovered |
|---:|---:|---:|---:|
| 16 | 28.1 ns | 21.3–23.3 ns | ~6 ns |
| 64 | 33.1 ns | 24.1–25.6 ns | ~8 ns |
| 256 | 33.5 ns | 25.3–27.4 ns | ~7 ns |
| 1024 | 37.5 ns | 27.9–29.0 ns | ~9 ns |

As a share of the whole call that is 9% at n = 64 and 3% at n = 1024. The
residue is the ~20 ns `ScopedValue` read, which no ladder touches.

**Cost**: precompilation **9.6 s → 13.0 s**, and isolating the two showed
broadcast alone accounts for essentially all of it (13.25 s with the array
seams reverted).

That is the compile-time explosion the scalar ladder was wrongly accused of, in
the one place it is real — and for the same reason the scalar case escaped it.
A scalar arm ends in `::T`, so inference takes the assertion. A broadcast arm
ends in `vmap!(dest, Val(op), ρ, args...)`, which has no cheap assertion
available, so inference descends into the Shape-A gather and its table lookups,
27 times per veneer.

**Reverted.** 7–10 ns per array call does not buy 3.4 s of precompilation. The
rule the two results together give: a ladder arm is free when it ends in a
concrete return assertion and expensive when it does not — which is a property
of the callee, not of the number of arms.

**Revisited and settled — see "TTFX, the workload, and why the ladder was the
wrong lever" below. The revert stands, but the reasoning below was aiming at
the wrong target: the workload, not the ladder, is what buys the latency.**

**Caveat on that revert, and it is a real one.** Precompilation time is a
one-time cost paid into a cache, and it is partly a *choice* — what
`@compile_workload` in `AIFloats.jl` names is what gets compiled ahead of
time. Treating 3.4 s of it as decisive against a measured runtime gain is the
weaker half of this argument. Two things would have to be measured before the
revert is settled rather than merely defensible:

* whether the 3.4 s buys back **TTFX** on the first scoped broadcast — the
  arms are compiled either way, just earlier;
* whether trimming or re-shaping the workload absorbs the cost, since the
  broadcast veneers are in it (`A .+ B`, `exp.(A)`, `d .= A .+ B`).

Recorded as open rather than closed. The gain itself is not large — 3–9% of a
whole scoped broadcast call, ~20–27% of its scoped *overhead* — and no reverted
change exceeded 15% of total call time at any array size.

## TTFX, the workload, and why the ladder was the wrong lever (2026-09-01)

Measured cold, deleting `~/.julia/compiled/v1.12/AIFloats` before each run,
because `touch` does not invalidate the cache.

| Config | cold precompile | first scoped `A .+ B` | second, different ρ |
|---|---:|---:|---:|
| baseline | 10.85 s | 283.6 ms | 230.7 ms |
| broadcast ladder | 13.02 s | 160.0 ms | 221.9 ms |
| workload names 1 ρ | 11.22 s | **6.9 ms** (that ρ) | 278 ms (others) |
| workload names 4 ρ | 12.19 s | **4.0–6.9 ms** (those) | 274 ms (others) |

### The finding that reframes everything

**A first scoped broadcast costs ~280 ms**, and the workload never covered it.
That is a far bigger number than any of the throughput deltas argued over
above, and it was invisible until measured.

**The specialization is per CONCRETE PROJECTION TYPE.** The decisive probe:
with `RTZ_SF` in the workload and nothing else,

```
RTZ_SF    6.9 ms     ← named in the workload
RTZ_SN  282.2 ms     ← not named
RTZ_SF    0.0 ms     ← cached
RTP_SN  231.4 ms     ← not named
```

40× on the named one, nothing for its neighbours. So precompiling one
projection does not help another, and no ladder changes that — the ladder only
caches *inference*, which is why it bought 124 ms on the very first call and
nothing on the second.

### The comparison that decides it

| Lever | precompile cost | latency bought |
|---|---:|---|
| broadcast ladder | +2.17 s | −124 ms, once |
| workload, 4 projections | +1.34 s | −275 ms **each**, ≈ −1.1 s |

The workload is roughly **7× better value**, costs less, and is a data change
rather than 27 arms in every veneer. The two are not complementary: the
ladder's benefit was inference caching, which the workload also provides.

### Decisions

1. **Broadcast and array ladders stay reverted.** Their unique contribution is
   7–10 ns per call of steady-state throughput, for 2.17 s of precompilation.
   That trade is bad on its own terms, and worse once the workload is doing the
   latency job better.
2. **Four scoped projections added to `@compile_workload`** — `RTZ_SF`,
   `RTZ_SN`, `RTP_SN`, `RTN_SF`, the directed rounding modes in both saturation
   flavours, which is what `with_projection` is mostly for. Cost ~0.33 s each,
   1.34 s total; those first uses drop from ~280 ms to ~5 ms.
3. The list is a **policy knob**, documented as such at the workload. Naming all
   27 would cost roughly 9 s of precompilation and is not worth it; a caller
   scoping some other projection pays the ~280 ms once per session.

### Correction to the record

The earlier entry treated 3.4 s of precompilation as decisive against a
measured runtime gain, and flagged that as the weaker half of its own argument.
It was — but not in the direction it guessed. The workload was not a way to
*absorb the ladder's cost*; it was a better lever than the ladder for a much
larger cost nobody had measured. The prompt to go and measure it was the user's.

## Why the compile-cost objection was wrong

The earlier entry argued 27 arms × 51 ops would explode inference. Measured:
precompilation unchanged, TTFX slightly better. Two reasons the estimate failed:

1. **Every arm carries `::T`.** Inference takes the assertion rather than
   descending into the callee, so an arm costs almost nothing to type.
2. **Julia compiles method bodies lazily.** An arm nobody reaches costs one
   pointer compare in the emitted code and no compilation at all.

The general lesson is the one this log keeps re-learning: an argument from
plausible mechanism is not evidence. This one was stated with more confidence
than it had earned.

## Test

`test-ops.jl` pins the ladder as a pure performance device: for all 18
deterministic constants, five unary and five binary ops over five operands and
three second operands, the scoped call must be `===` the explicit spelling; the
laddered scoped calls must allocate nothing; and the non-default-budget
`ρRSA{4}` fallback must still be correct through the barrier.

# Where the scoped seam's allocations come from (2026-09-01)

Isolation run, after the Phase 2 entry left two of three allocations
unexplained. Two findings, one of which corrects a measurement.

## The rule: `arity + 1` boxes

A dynamic call goes through `jl_apply_generic`, whose ABI passes and returns
`jl_value_t*`. So it boxes the isbits **return value** *and* every isbits
**argument** it cannot constant-fold. Measured per call, arguments read from a
`Vector` so nothing folds:

| Seam | Operands | Measured |
|---|---:|---|
| `Negate(x)` | 1 | 32 B, 2 allocs |
| `Add(x, y)` | 2 | 48 B, 3 allocs |
| `FMA(x, y, z)` | 3 | 64 B, 4 allocs |
| `F(v)` constructor | 1 (the `Real`) | 32 B, 2 allocs |
| `Add(F, ρ, x, y)` explicit ρ | — | 0 B, 0 allocs |
| `Add(x, y)` unscoped RTE | — | 0 B, 0 allocs |

`arity + 1`, exactly, with the constructor fitting too: its barrier's format
witness and its `nothing` keywords are compile-time constants, so only the
`Float64` argument and the return box.

**This answers the open question.** The three allocations are not three
separate causes with two of them unaccounted for; they are one cause. A static
ladder would remove all of them, because a static call passes isbits arguments
and returns in registers — which is what the explicit-ρ row already
demonstrates at 0 B.

## The measurement trap: constant arguments hide argument boxes

`@allocated` over a closure on `const` globals reports **1 alloc, 16 B** for the
same `Add(x, y)` that costs 3 allocs and 48 B with ordinary arguments. The
`const` values are loop-invariant, so the compiler hoists their boxes out of the
measurement loop and only the return box remains.

That makes the benchmark suite's `@b Add($a, $b)` the *honest* form here and my
ad-hoc `const`-global probes the misleading ones — the opposite of the usual
advice, and the reason the earlier "3 allocs" and "1 alloc" readings disagreed.
The published row in `60-benchmarks.md` was right all along.

The generalizable check, used above: run the call in a loop `n` times, measure
at two values of `n`, and divide the difference. Nothing that is hoisted or
amortized survives that subtraction.

## What this does and does not change

The ladder reaches 0 B. It does not touch the dominant cost: most of the scoped
seam is the `ScopedValue` read itself, which no amount of dispatch work removes.
And it cannot be total — `ρRSA{N}` at a non-default budget has no constant to
match against, so a dynamic fallback arm stays.

> **Superseded 2026-09-01 — the ladder was built and measured; see "The guard
> ladder" below.** The paragraph that stood here argued against it on
> compile-time grounds: 27 arms in each of 51 generated ops, with inference
> walking all 27 on first compile. **That was wrong, and measurement refuted
> it.** Precompilation is unchanged and first-call latency slightly improves.
> The reasoning failed to account for the `::T` assertion on each arm, which
> lets inference take the assertion instead of descending into the callee, and
> for Julia compiling method bodies lazily.

# Final verification (2026-09-01)

**Full suite, all 16 focused files: green.** 38,518,000+ assertions, zero
failures.

| File | Assertions | Time |
|---|---:|---:|
| `rounding-paths` | 35,538,086 | 1m57s |
| `compat` | 1,833,844 | 48s |
| `ops` | 913,318 | 1m41s |
| `blocks` | 26,391 | 3m09s |
| `fastpaths` | 7,787 | 2m42s |
| `tables` | 1,056 | 8s |
| `governance` | 381 | 5s |
| `singletons` | 334 | 3s |
| `kernels` | 197 | 16s |
| `quality` (Aqua + JET) | 35 | 40s |
| plus `binary-format`, `binaryvalue`, `traits`, `codec`, `dyadic`, `projection` | | |

**Docs build with benchmarks: clean.** Doctests, cross-references, and document
checks all pass; the only two warnings are the local-environment ones (no CI
repo URL, no deployment context). `docs/src/60-benchmarks.md` is regenerated
from a live `benchmark/runbenchmarks.jl` run during the build, and the page's
header records the commit, CPU, thread count, and policy defaults.

Two defects the final build caught, both introduced by earlier phases of this
same plan:

* **`withflags` restored a 5-tuple from a 4-tuple.** Phase 2 removed the
  projection from `benchmark/runbenchmarks.jl`'s saved state and took
  `THREAD_MIN_ELEMS` with it, while the `finally` block still indexed
  `saved[1:5]`. Nothing but a real benchmark run reaches that path.
* **`Convert`'s docstring detached — the third time this failure has appeared
  in this log.** Phase 3 collapsed six `Convert` methods into one, and the
  docstring that had sat above the first of them ended up above a comment and
  then `const _F64_EXACT_INT`. Documenter caught it as four unresolvable
  `@ref`s. The docstring is now immediately above the single method and
  documents the array forms too.

The benchmark suite gained the scoped-projection rows Phase 2's measurements
justify, so the seam's cost is recorded in the published page rather than only
in this log:

```
Add       explicit ρ                                 15.5 ns
Add       task default ρ                             16.6 ns
Add       scoped non-RTE ρ                           77.2 ns  allocs=3 bytes=48
DefaultProjection() bound                            46.3 ns
DefaultProjection() unbound                           4.1 ns
```

## Phase 7 — done (2026-09-01)

**Gate.** `governance` (new taxonomy testset) · `kernels` · `tables` · `ops` ·
`blocks` · `quality` · doctests — green.

**Registry metadata is frozen.** `opinfo` was a `findfirst` linear scan of a
vector that is, in principle, still `push!`-able. It is now a hash probe into
`_OP_BY_NAME`, built once after the last `register_op!` and never rebuilt, and
an unknown symbol gets an `ArgumentError` naming `operations()` instead of an
index error. Added `operationinfo(op)` — `(name, arity, group, factors)` — and
`operations()`, sorted by name so the listing is deterministic rather than
registration-ordered.

**The runtime-symbol boundary validates once.** `vmap(op::Symbol, …)` and
`vmap!` passed straight to `Val(op)`; an unknown symbol surfaced as a
`MethodError` from deep inside a kernel, naming nothing a caller could act on,
and a wrong operand count found whatever method happened to match. Both now
call `_validate_runtime_op` first — operation exists, arity matches — and cross
into `Val(op)` only after, so inner loops keep static dispatch and no element
pays for a lookup. A 100k-element call costs the same single lookup a
three-element call does, and the test says so.

The error taxonomy is now pinned as a table of assertions rather than a
paragraph of intent:

| Condition | Exception | Asserted on |
|---|---|---|
| unknown operation | `ArgumentError` naming the alternative | `operationinfo`, `vmap`, `vmap!`, `table_policy`, `measure_kappa`, `register_approx!` |
| wrong operand count | `ArgumentError` with expected **and** actual | `vmap`, `table_policy` |
| incompatible shapes | `DimensionMismatch` | `vmap!`, packed and block `copyto!` |
| invalid index | `BoundsError` via Base | `PackedVector` |
| size arithmetic overflow | `OverflowError` | `PackedVector{T}(undef, typemax(Int))` |
| refused `Rational`/`Irrational` | `ArgumentError` explaining the risk | `Convert` |
| unsupported input type | `MethodError` | `Convert(F, ρ, "1.5")`, `F(nothing)` |
| IEEE invalid arithmetic | **returns the prescribed NaN** | `Sqrt(-1)`, `Log(-1)`, `0/0` |

That last row is the one worth stating out loud: an invalid operation the
*format* represents is a value, not an error, and `Sqrt(F, ρ, F(-1.0))` must
return the format's NaN code rather than throw.

## Phase 6 — done (2026-09-01)

**Gate.** `blocks` (two new testsets) · `kernels` · `compat` · `governance` ·
`quality` (Aqua ambiguities, re-run after each new `copyto!` signature) ·
doctests — green.

### Two real defects, not just an interface tidy

**`similar(pv)` packed uninitialized datums.** It was
`PackedVector(Vector{T}(undef, pv.n))`. There is no such thing as an
uninitialized *datum*: a `BinaryValue` read out of undef memory can carry bits
above `K`, and the packing loop writes `UInt64(codepoint(v)) << off` — so those
stray high bits land in the **neighbouring element's** share of the shared
word. `getindex` masks what it reads, so the corruption is silent and shows up
as a wrong neighbour. `similar` is now zero-filled, and so is every new
`BlockVector` scale and element array.

**Padding was never validated.** `getindex` masks, but `setindex!` on a
cross-word element writes into the next word assuming its high bits are
canonical, and the byte form copies its final unit verbatim. Non-canonical
padding therefore turns into wrong neighbouring elements and a wire form two
readers disagree about. `_validate_packed` now checks it in one place, and both
deserializers refuse it — a reader cannot tell a corrupt stream from a
differently-conventioned writer and must not guess.

### Serialization is now portable, and says so

`PackedVector{T}(words, n)` is gone: it could not say whether it validated,
copied, or took ownership, and it was public. In its place four functions with
one meaning each:

| | |
|---|---|
| `packedfromwords(T, words, n)` | validates and **copies** `cld(n*K, 64)` logical words |
| `packedwords(pv)` | an independent `Vector{UInt64}` |
| `packedfrombytes(T, bytes, n)` | the canonical little-endian wire form |
| `packedbytes(pv)` | exactly `cld(n*K, 8)` bytes |

Both forms are **logical**, defined independently of host byte order — byte `j`
holds bits `8j..8j+7` of the bit stream. Exposing the in-memory bytes of a
`Memory{UInt64}` would not have been a serialization interface at all, only a
description of this host. The byte form is the shorter one whenever the payload
does not fill its final word (20 bytes against 24 for 32 datums at `K = 5`),
which is the reason to have it.

`_rawpacked` is the single ownership-taking door, now the struct's only inner
constructor. Every public entry point copies.

### Collections

`copy` is an independent packed copy; `collect`/`Vector` unpack. `copyto!` is
spelled at the three most specific signatures that do the job — packed→unpacked,
unpacked→packed, packed→packed — and the same three for `BlockVector`. A
broader signature is ambiguous with Base's (`PermutedDimsArray` among them);
narrowing was the fix, not a catch-all. `similar` preserves packed or SoA
storage only for a one-dimensional result of the right element type.

The tests round-trip **all codes exhaustively for `K ≤ 6`** and boundary-crossing
lengths (0, 1, 7, 8, 63, 64, 65, 127, 128, 129, 1000) for every `K` in 3:16,
both wire forms, plus aliasing in both directions, nonzero-padding refusal,
`OverflowError` on length overflow, and every `copyto!` shape refusal.

One measurement note for the log: `Vector(pv) == collect(pv)` **fails** on a
population containing the format's NaN datum, because `==` on a NaN is false by
IEEE rule and array `==` inherits it. The assertions compare code points.

## Phase 5 — done (2026-09-01)

**Gate.** `tables` (with the new snapshot testset) · `governance` · `kernels` ·
`quality` · doctests — green.

**Four introspection functions became two coherent ones.** `table_bytes`,
`table_count`, `ternary_count` and `table_keys` each took `TABLE_LOCK`
separately, so a caller assembling a report from several of them could describe
three different moments of a cache another task was filling, and then print
totals that do not add up. `table_stats()` and `table_entries()` each take the
lock **once** and read everything inside it. The test asserts the property
directly: `by_arity` and `by_codeunit` each sum to `entries`, and the per-entry
`bytes` sum to `bytes`.

`table_entries()` returns public named tuples — `(op, arity, result, operands,
rounding, saturation, bytes)` — naming **format types** and the mode names a
caller actually writes. The internal key struct stores `(K,P,S,D)` tuples and
the singleton's *type* name (`:ρRTE`); both are now unmapped at the boundary
rather than leaked through it.

`get_table`, `table_for`, and the key structs left the `public` list. The
kernels still call them; they are simply no longer part of the surface.

`table_policy` now **validates the operation and its arity before computing a
key**. A key built from an unregistered symbol, or from the wrong operand
count, is a well-formed key for a signature that can never be built — and the
policy answer derived from it would be a confident lie rather than an error.

**`conformance()` had the coherence bug this phase exists to fix.** It captured
`table_keys()` into the declaration, and then `conformance_report` called
`table_bytes()` again *at print time* — so the count and the size it printed
came from two different moments. The declaration now carries `cached_bytes`
from the same snapshot, and the report prints that field. `conformance_dict`
and `ConformanceDeclaration.cached_specializations` moved to the public named
tuples with it.

One placement note worth keeping: `const TableEntry` had to be introduced
*before* `table_entries`'s docstring, and with a plain comment rather than a
docstring of its own. Inserted after, it sat between that docstring and its
function and silently retargeted it — the same failure mode already recorded
twice in this log.

## Phase 4 — done (2026-09-01)

**Gate.** `traits` (with the new query testset) · `binary-format` · `quality` ·
doctests — green.

**The Julia-style names are bindings, not wrappers.** `const bitwidth =
BitwidthOf`, and so on for `formatof`, `signedness`, `domain`, `codetype`,
`valuetype`. Writing them as forwarding methods would have been the obvious
thing and the wrong one: two names would then have two method tables that can
drift apart in what they accept, and a method added for one would not be a
method for the other. Bound to the same function object, `formatof ===
BinaryFormatOf` is literally `true`, and there is no second call to elide.

`formatof(F) === F`, so internal code has one total normalization query
whatever it is handed — format, datum type, or datum.

**`Base.precision` now covers formats**, not just datums. §4.2 declines to
export a `precision` of AIFloats' own: shadowing Base's would change the
meaning of a name every Julia program already has. The test asserts the name
is absent from `names(AIFloats)`.

**`formatinfo(F)`** returns the stable 14-field named tuple. Two details:

* It lives in the new `types/queries.jl`, loaded late, because it binds names
  from `types/binaryvalue.jl`, `carriers/heads.jl` and `rules/constraints.jl`.
  `types/traits.jl` is loaded before all three — the format machinery needs it
  first — so the block could not stay there.
* It carries `Base.@assume_effects :foldable`, and the promise is honest: the
  body is pure, terminates, and every component of the result is interned or
  immortal. Without it the call does **not** fold — `formatname` builds its
  Symbol through a String, which inference will not prove consistent on its
  own — and the tuple costs ~900 bytes on every call. With it: 0 bytes, and
  `formatinfo(F).bitwidth` compiles to a literal. Both are asserted.

**Phase 1c's instance sweep was incomplete**, and Phase 4 is where that
surfaced: `datumcarrier(b::Binary)` was needed by `formatinfo` and turned out
to still exist. The original inventory grep was truncated by a `head -40`.
Re-run without it, twelve more adapters were found and deleted — in
`gentables.jl`, `heads.jl`, `scalar.jl`, `project.jl`, `policy.jl` and
`approx.jl`. `grep -rn '::Binary\b' src/ | grep -v 'Type{' | grep -v '<:Binary'`
is now empty.

## Phase 3 — done (2026-09-01)

**Gate.** `kernels` (with the new §8.3 parity testset) · `ops` · `compat` ·
`fastpaths` · `projection` · `codec` · `quality` — green.

The array surface carried a **private copy of the carrier ladder**,
`_array_convert_value`, alongside the scalar one in `Convert`. The two agreed
today; nothing made them agree tomorrow. Both now call one
`_convert_value(F, ρ, x, R)` family, and the scalar `Convert` collapsed from
six near-identical methods to one:

```julia
Convert(fr::Type{<:Binary}, ρ::Projection, x::ConvertSource; rng, R) =
    _convert_value(fr, ρ, x, _drawR(ρ, rng, R))
```

`ConvertNumber` and `ConvertSource` name the closed accepted set. Closed
deliberately: a generic `Real` fallback would reach `BigFloat` through
`convert`, and for a type whose own conversion rounds, that is a double
rounding this package can prove nothing about. `Rational` and `Irrational`
keep their explicit refusals, and an array whose element type is outside the
set is refused by message rather than by `MethodError` — spelled on bare
`AbstractArray` so `Vector{Any}` gets the message too, not just `Vector{Real}`.

Added `Convert(F, A)`, the default-projection array convenience, which resolves
`DefaultProjection()` **once before the loop** and never per element.

**The parity testset is the point of the phase.** For every accepted source
type — `Float64`, `Float32`, `Float16`, `BFloat16`, `Float128`, `BigFloat`,
`Integer`, `BinaryValue` — over edge populations (signed zeros, subnormal
boundaries, lattice ties, finite extrema, infinities, NaN, `typemin`/`typemax`,
`Int128(1) << 100` which needs `Float128`, `big(2)^600 + 1` which needs
`BigFloat`) and five projections, every element of the array conversion must
equal the scalar conversion of that element **by code point**. Comparing
decoded values would pass even if the two ladders picked different carriers,
since both answers decode near the source; the code point is what distinguishes
them. Shape, axes, a `view` source, the identical refusals at both boundaries,
and the stochastic one-draw-per-element-in-index-order property are pinned in
the same testset.

Also removed here: a dead `Convert(fr::Binary, ρ, A)` instance adapter that
Phase 1c's sweep missed.

## Phase 2 — done (2026-09-01)

**Gate.** `ops` · `compat` · `fastpaths` · `kernels` · `binaryvalue` ·
`projection` · `blocks` · `tables` · `governance` · `quality` (Aqua + JET) ·
doctests — all green.

`rules/defaults.jl` is now one `ScopedValue{Projection}(RTE_SN)`. The three
mutable `Ref`s and all three setters are gone; `DefaultRoundingMode` and
`DefaultSaturationMode` derive from the single value, so they cannot be read
torn. `with_projection(f, ρ)` and `with_projection(f, μ, σ)` are exported.

The abstract parameter on the `ScopedValue` is required: `ScopedValue(RTE_SN)`
would infer `ScopedValue{Projection{typeof(RTE),typeof(SN)}}` and reject every
other projection at bind time.

Performance-policy `Ref`s (`FAST_ARITH`, `FAST_ENCLOSURE`, threading, table
budgets) stay process-wide, and the reason is stated in the file: they select
an implementation *strategy* rather than a *result*. Display keeps its
`IOContext`/`DEFAULT_SHOW_STYLE` pair, because display context travels with
`IO` rather than with task scope.

### The function barrier, and three things that silently defeat it

Measured on Julia 1.12.6, one thread:

| Path | Time | Allocated |
|---|---:|---:|
| explicit `Add(F, ρ, a, b)` | 1.3 ns | 0 B |
| `DefaultProjection()` unbound | 4.1 ns | 0 B |
| RTE convenience `Add(a, b)` | 4.1 ns | 0 B |
| RTE constructor `F(1.35)` | 3.1 ns | 0 B |
| explicit-projection constructor | 1.3 ns | 0 B |
| `DefaultProjection()` bound | 31.4 ns | 0 B |
| scoped convenience `Add(a, b)` | 61.2 ns | 48 B |
| scoped constructor `F(1.35)` | 60.9 ns | 32 B |
| scoped `a + b` (Base veneer) | 70.4 ns | 48 B |
| RTE array `Add(A, B)`, n = 4 | 140.4 ns | 64 B |
| scoped array `Add(A, B)`, n = 4 | 177.7 ns | 64 B |

Every steady-state path — explicit projection, and the unscoped RTE default —
allocates nothing. The scoped seam went from the plan's measured 272 ns naive
figure to 61 ns.

Three properties of the barrier are load-bearing, and each was found by
measurement after the obvious spelling failed:

1. **It must not be `@inline`.** Inlining it back into the guard puts the
   abstract projection exactly where it was; the barrier does nothing. First
   attempt: no change at all.
2. **It must match `Projection{RM,SM}`, not `ρ::P where P<:Projection`.** An
   argument statically typed `Projection` *satisfies* `P<:Projection`, so Julia
   binds `P = Projection`, makes a static call to an abstract specialization,
   and the barrier compiles away. Inspecting `Base.specializations` showed the
   method instance with `specTypes` naming plain `Projection` — that is the
   tell. `Projection{RM,SM}` cannot be satisfied statically, which forces the
   runtime dispatch the seam is paying for.
3. **The format must arrive on a datum, not as a leading `::Type{F}`.** A
   `Type` argument in a dynamically dispatched call is expensive to match:
   148 ns with it against 28 ns without, same body. For value construction,
   where there is no datum argument, the barrier takes a witness — the zero
   datum of `F`, isbits and free to make (169 ns → 24 ns).

**The residual allocations are `arity + 1` boxes, all entailed by the single
dynamic dispatch.** *(Corrected 2026-09-01 after a dedicated isolation run —
see "Where the scoped seam's allocations come from" below. The first account
here identified only the return box and called the rest unexplained.)* Julia's
generic calling convention passes and returns through `jl_value_t*`, so a
dynamic call boxes its isbits return **and** every isbits argument it cannot
constant-fold. Removing them means removing the dispatch: a static ladder over
all 27 projections in each of the 51 generated ops. The plan's §9.2 gate
accepts "the one dynamic dispatch and measured latency of the non-RTE
convenience seam"; these are the allocations that dispatch entails.

Array kernels and broadcasting resolve the default **once per public call**,
never per element — the four-element figures above differ by 37 ns, and the
difference does not grow with n.

**Call-site migration.** `test-ops.jl`'s session-default testset became a
scoped one and now also pins nesting, restoration through an exception, sibling
task isolation, child task inheritance, and the absence of all three setters.
`test-fastpaths`, `test-binaryvalue`, `test-kernels` and `test-compat` lost
their save/restore `try`/`finally` scaffolding. `benchmark/runbenchmarks.jl`'s
`withflags` no longer saves the projection at all: a measured body that wants a
different one runs under `with_projection` and cannot leak it.

## Phases 1b and 1c — done (2026-09-01)

Committed together, on purpose: the plan forbids committing 1b's interface
(improveapi3.md §6 Phase 1b, "never to be the committed interface"), and 1c is
what replaces it. 1b existed only to *find* call sites, and its findings are
carried in 1c's diff.

**Gate.** `binary-format` · `binaryvalue` · `codec` · `projection` · `ops` ·
`blocks` · `compat` · `dyadic` · `traits` · `kernels` · `tables` · `fastpaths` ·
`governance` · `singletons` · `rounding-paths` · `quality` (Aqua ambiguities,
undefined exports, piracies, stale deps + JET) — all green.

### 1b — what the trap found

The trap was an inner `BinaryValue{F,U}(::Unsigned)` that threw, installed on
every code-point constructor spelling. It had to exist: deleting the code-point
constructor outright gives no `MethodError`, because the value-taking `Real`
constructor accepts the identical argument, so each missed site would have
silently become a *number* instead of a code point — `T(0x45)` meaning 69.0
rather than 1.625.

Sites it caught, all in tests, each classified rather than rewritten
mechanically:

| Site | Was | Meant |
|---|---|---|
| `test-binaryvalue.jl` total-order sweep | `BV(U(c))` over `0:2^K-1` | code points |
| `test-binaryvalue.jl` show styles | `BinaryValue(F)(0x45)` | code point |
| `test-binaryvalue.jl` NaN probe | `BinaryValue(F)(nan_code(F))` | code point |
| `test-codec.jl` layout spot checks | `BinaryValue(F)(0x45)`, `(0xff)`, `(0x00)` | code points |
| `test-codec.jl` monotone decode | `BV(U(c))` | code points |
| `test-projection.jl` idempotence | `BV(c)` | code points |
| `test-ops.jl` probe set | `BV(zero(U))`, `BV(U(maxfinite>>1))` | code points |
| `test-blocks.jl` packed round trip | `T(U(i % nc))` | code points |
| `test-dyadic.jl` rung-3 decode sweep | `BinaryValue(F, UInt16(c))` | code points |
| `test-binaryvalue.jl` two-arg testset | `BinaryValue(F, 0x03) !== BinaryValue(F, 3)` | pinned the OLD split |

Every one became `fromcode`, except the last: it asserted the very distinction
1c removes, so it was rewritten to assert the new contract instead — that all
constructor spellings agree, and that `fromcode(F, 0x03)` differs from
`F(0x03)`.

### 1c — the canonical model

**`Binary` has no instances.** `struct Binary{K,P,S,D}` now declares an inner
zero-argument constructor that throws, which suppresses Julia's generated one.
The error names all four things a caller might have wanted:

```
Binary{8, 4, SIGNED, EXTENDED} is already the format; formats have no instances.
  a format:      Binary{8, 4, SIGNED, EXTENDED}
  the number x:  Binary{8, 4, SIGNED, EXTENDED}(x)
  a code point:  fromcode(Binary{8, 4, SIGNED, EXTENDED}, c)
  the datum type: BinaryValue(Binary{8, 4, SIGNED, EXTENDED})
```

That deletion is what earns the rest. With no instances there is nothing for an
instance overload to serve, so `BinarySpecifier`, `_formattype`, and **31**
`::Binary` one-hop adapters are gone: the trait forwarders in
`types/binaryformats.jl` and `types/traits.jl`, `decodepolicy`, `bigprec`,
`formatname`, the two generated families in `content/codepoints.jl`, and the
kernel/block/packed/table/approx/scalar entry points. Each was a real
liability, not clutter — one of them, `BinaryValue(fmt::Binary, code)`, had
already been written as a self-recursion Julia cannot diagnose, because the
signature legitimately matches itself. It presented as `StackOverflowError`.

**Construction has one semantic axis.** The inner `Unsigned` constructor is
gone with the trap, so `Unsigned` now falls through to the ordinary `Real`
value path. Every spelling agrees:

```julia
F(0x03) === T(3) === BinaryValue(F, 3.0) === BinaryValue{F}(3) === convert(T, 0x03)
```

and `fromcode(F, 0x03)` is the different question with the different answer.
`Base.convert(::Type{T}, ::Unsigned)` was deleted for the same reason: it
existed only to override the old code-point meaning, and `convert(T, ::Real)`
now carries unsigned values through the same guarded constructor.

`_rawvalue` is the sole remaining door into `new`. `rawvalue` (the truncating
`%` variant) had no callers left after 1a and was deleted.

**Two spellings, two questions.** `BinaryValue(F)` is the datum *type*;
`_datumtype(F)` is its internal name, used where a kernel needs a concrete
element type and "the datum type of F" reads better than a constructor call.
`F(x)` constructs a *datum*, so `F(x) isa F` is `false` — the one deliberate
exception to the ordinary type/instance relationship, now stated in both
docstrings and asserted directly in `test-binary-format.jl`.

**Test surface.** The testset that pinned "the instance surface has no holes"
became "a format is type-level information: one spelling, no instances" — it
asserts the suppressed constructor by message, that every accessor is
`applicable` to the format type, and the `F(x) isa BinaryValue(F)` /
`!(F(x) isa F)` pair.

## Phase 1a — done (2026-09-01)

Gate for what is done: `test-binary-format` 273 · `binaryvalue` 133,055 ·
`codec` 66,700 · `kernels` 62 · `tables` 1,025 · `quality` 35 (Aqua + JET).

**`fromcode(F, code)` / `fromcode(T, code)`** — the checked public code seam,
exported. Any `Integer` of any width: the range is checked against
`codemask(F)` *before* narrowing, so `fromcode(F, UInt16(300))` on an eight-bit
format raises rather than truncating to 44. Negative and over-range throw
`ArgumentError` naming the numeric alternative, since the whole point is that
`F(3)` and `fromcode(F, 3)` now differ. Round trip
`fromcode(typeof(x), codepoint(x)) === x` is asserted in the docstring as a
doctest.

**`_rawvalue(F, code)`** — the internal fast path (§4.2.5). The plan spells its
contract `code::CodeType(F)`, which **Julia cannot express**: a signature is
evaluated at definition time, where `F` is still a `TypeVar`, so
`CodeType(::TypeVar)` is a `MethodError` at load. Enforced by CONVERSION
instead — `new` converts into the field type, so an out-of-range code raises
`InexactError`. That is stricter than the plan's intent, not weaker:
`rawvalue`'s `%` truncates silently, and this checks the representation
invariant rather than merely the storage width.

**Caller migration, classified.** All 45 `rawvalue` sites in `src/` are proven
internal raw construction — the code comes from `nan_code(F)`,
`_maxfinite_code(F)`, a table index, code arithmetic already in `CodeType(F)`,
or an explicit narrowing — so all became `_rawvalue`. The migration checks its
own classification: `_rawvalue` raises `InexactError` where `rawvalue`'s `%`
truncated, so a site that was NOT canonical would now fail loudly.

The 9 sites in `test/test-blocks.jl` import known code points
(`nan_code`/`posinf_code`/`neginf_code`) and became `fromcode`, per 1a.2's
split between implementation loops and tests.

`rawvalue` is no longer `public` (starting 1c.6). Its definition stays until
Phase 1c, when the code-point constructor is deleted with it.

**1a.4 re-run: zero residual.** No `T(codepoint(x))` reconstruction anywhere.
The two `codepoint` occurrences inside calls are `UInt64(codepoint(v))` in the
packing kernels — a code being written into a word, not a datum being rebuilt.

Gate: `binary-format` 273 · `binaryvalue` 133,055 · `codec` 66,700 · `blocks`
23,528 · `tables` 1,025 · `ops` 913,307 · `compat` 1,833,843 · `kernels` 62 ·
`governance` 336 · `quality` 35 (Aqua + JET).

## Phase 0 — done (2026-09-01)

Baseline `cb45103`, clean tree.

**Already satisfied by earlier work** (commit `cb45103`, which enacted §4.1.2
before this revision of the plan existed), so Phase 1c items 2, 4, 7 and 8 are
complete:

- `_NAMED` maps each name to its **format** type; the 504 aliases are format
  types (`Binary8p4se <: Binary`).
- `(::Type{F})(x::Real)` constructs a datum, so `Binary8p4se(1.5)` still works.
- Named-format use sites migrated by classification; precompile workload names
  `F` and `T` separately.
- Additionally, and not in the plan: the datum type prints as
  `BinaryValue(Binary8p4se)` so both kinds round-trip, and
  `BinaryFormatOf(::Type{F}) = F` makes normalization total (§4.3.3).

**Inventory of forms this plan deletes or rewrites** (occurrences across
`src/`, `test/`, `benchmark/`):

| Form | Count | Plan disposition |
|---|---:|---|
| `::Binary` (instance-accepting) | 56 | remove (§4.1.3) |
| `rawvalue` | 56 | rename `_rawvalue`, drop from `public` (§4.2.5) |
| `get_table` | 40 | make internal (§5 Phase 5.1) |
| `DefaultProjection!` | 21 | delete (§4.3) |
| `BinarySpecifier` | 10 | remove (§4.1.3) |
| `_formattype` | 8 | remove (§4.1.3) |
| `.data` / `.scales` / `.elems` direct access | 16 | behind accessors (§6 Phase 6) |
| `table_keys` | 7 | delete, subsumed by snapshots (§5.6) |
| `PackedVector{T}(words,n)` | 7 | replace with `packedfromwords` (§6.2) |
| `DefaultRoundingMode!` / `DefaultSaturationMode!` | 8 | delete (§4.3) |

**The silent-hazard search** the plan calls for specifically (§6 Phase 0.4):
`T(codepoint(x))` and equivalents, which keep compiling while changing meaning
once `Unsigned` becomes a value. **Zero found** in `src/` or `test/`. The one
`codepoint` occurrence inside a call, `kernels.jl:122`, is
`Int(codepoint(C[i])) + 1` — a table index, not a reconstruction.

Note `BinarySpecifier`, `_formattype` and most of the 56 `::Binary` methods
were added by `bcf5852`, which this plan removes again. That commit and this
plan pull in opposite directions; the plan wins here by the author's
instruction to implement it.



## Type hierarchy: a format is no longer a number (2026-09-01)

Gate: full `Pkg.test()` green, docs build and doctests clean, benchmarks
unmoved.

```julia
struct Binary{K,P,S,D} end                                  # was <: BinaryFloat
struct BinaryValue{F<:Binary,U<:Unsigned} <: AbstractFloat  # unchanged
```

`abstract type BinaryFloat <: AbstractFloat end` is deleted, and with it the
export.

### Why, since the original decision was to keep it

`docs/structuralplan.md` §9.2 had considered and deferred this, on the grounds
that it "breaks documented API for zero computational gain". The gain is not
computational, which is why that framing missed it:

- While a format was an `AbstractFloat`, Base's numeric fallbacks applied to
  format instances and **`isnan(Binary{8,4,SIGNED,EXTENDED}())` returned
  `false`** — the generic method is `x != x`, so a meaningless question got a
  confident answer instead of an error.
- The hierarchy contradicted its own names. `Binary`, the format *specifier*,
  was a subtype of something called `BinaryFloat`; `BinaryValue`, the actual
  number, was not.

### The predicted cost did not appear

`BinaryFloat` had **zero uses as a bound** anywhere in `src/` or `test/` — it
was declared, exported, documented and otherwise inert. So "propagate the
change throughout the source and tests" required no propagation: five line
edits in two files, no test changed, no doc page changed, and the benchmark
suite unmoved (`decode` 1.4 ns, `Add` 8.7, `T(1.3)` 1.4, `Exp` 22.2, `vmap!`
14.9 µs — all at baseline). `BinaryValue` stays concrete, so dispatch is
untouched.

The API break is the removal of the exported name `BinaryFloat`. It named the
wrong thing and nothing used it.

### Pinned, not left implicit

`test/test-binary-format.jl` gains "a format is not a number": `supertype(F)
=== Any`, `!(F <: AbstractFloat/Real/Number)`, the datum of the same format
still `<: AbstractFloat` and `isbits`, `isnan`/`zero` on a format instance
throwing `MethodError`, and `!isdefined(AIFloats, :BinaryFloat)`. Without this
the category error can silently return — re-adding a numeric supertype would
otherwise fail no test anywhere.

`docs/structuralplan.md` §4 and §9.2 record the reversal rather than hiding it;
§9.2 keeps the original reasoning above the revision.

## implmentplan.md Step 10 done — documentation close-out (2026-08-28)

Gate: full `Pkg.test()` green, docs build clean.

- `docs/src/50-status.md`: NEW "[Performance characteristics](@id performance)"
  section — the facts a caller needs to predict cost, all measured, none
  asserted: the K ≤ 8 decode table; the table band and why it is a build-time
  bound that ignores call length; the threading threshold, its crossover, and
  the fixed ~1.6 KB scheduler cost; which broadcasts route through the kernels
  and which deliberately do not; sequential seed-reproducible stochastic order;
  what packed storage actually trades; when block reductions are exact in
  `Dyadic` and when they fall back; the session-default speculation; and
  first-call latency.
- `docs/src/50-status.md` deliberate limits: the packed entry said computation
  "unpacks tile by tile", which stopped being true in Step 6 — it now says a
  packed operand is read straight out of the bit stream and is supported for
  unary operations only.
- `README.md`: NEW short "Performance" section with the headline numbers and a
  pointer to the harness and the status page.
- `docs/planreview.md` had already been removed from the tree; `reviewplan.md`
  and `implmentplan.md` no longer link to it, and `reviewplan.md` records what
  it was and which of its claims were checked and found stale.
- `implmentplan.md` status header and summary table updated to reflect that all
  ten steps are enacted, and to point at this file for what actually happened
  rather than what was planned.

---

## implmentplan.md — all ten steps complete (2026-08-28)

| # | Step | Outcome |
|---|---|---|
| 0 | hygiene | no overwrite warnings; 5 stale docstrings corrected; 2 unused deps dropped |
| 1 | benchmark harness | `benchmark/`, 3 suites, isolated from package deps |
| 2 | constructor guard | `T(1.3)` 98.6 → 1.4 ns, 0 allocs |
| 3 | Integer conversion | `T(3)` 583 → 1.8 ns, 0 allocs |
| 4 | FMA Float64-first | 452 → 12.7 ns |
| 5 | `@inline _mpfr*` | `Log` 236 → 27.5 ns, 0 allocs |
| 6 | packed direct gather | 52.3 → 27.0 µs |
| 7 | broadcast through kernels | `A .+ B` 632 → 15 µs; `exp.(A)` 1578 → 8.6 µs |
| 8 | blocks via Dyadic | `BlockReduceAdd` 2899 → 267 ns, `BlockDotProduct` 5312 → 297 ns, both 0 allocs |
| 9 | thresholds and latency | `THREAD_MIN_ELEMS` 32768 → 1024 (3.6x at N=4096); cold `Log` 103 → 6.5 ms |
| 10 | documentation | performance characteristics documented from measurement |

### Rejected on measurement — recorded so they are not retried

1. **Packed running-offset walk** (Step 6). Carrying the word index and bit
   offset across iterations removes a multiply per element but adds a
   loop-carried dependency: 65.1 µs against 26.9 µs recomputed, 2.4x worse.
   Reverted, with both numbers in a comment at the loop.
2. **Int128 fixed-point block accumulator** (Step 8). `Dyadic` already is one,
   with the preconditions derived and tested. The plan was rewritten before
   any code was written.
3. **Raising `TABLE_EAGER_BITS` to 18** (Step 9). A 95x win at N = 65,536 and
   an 864x regression on a one-shot N = 100 call, because the gate cannot see
   call length. Declined; the reasoning is in the docstring, and the adaptive
   band that would capture the win safely is named as the follow-up.

### Bugs the tests caught in work written during this plan

1. **FMA underflow hole** (Step 4). `fma(x, y, -p) == 0` does not prove the
   product exact when the residual itself underflows. Fixed with a derived
   magnitude floor, `|p| ≥ 2^-915`.
2. **Signed zero in the block fast lane** (Step 8). The draft has a single
   zero; raw multiplication yields `−0.0` on mixed signs. Caught immediately by
   the existing "blockdecode ≡ lane semantics" testset.
3. **Threaded kernels allocate** (Step 9). Lowering `THREAD_MIN_ELEMS` made an
   existing allocation assertion fail, correctly: `Threads.@threads` costs a
   fixed 1,568 bytes. The test now asserts the true property — sequential
   allocates nothing, and the threaded cost does not scale with N.

### Follow-ups deliberately not taken

- An adaptive band for **binary** table signatures, mirroring
  `_ternary_table_for`. This is the one change that would claim a large
  measured win (up to 95x on expensive binary ops over long arrays) and is
  blocked only by `table_for` not receiving the call's element count.
- `FAA` still runs `_exact_sum3` with no Float64/Float128 specialization
  (166 ns against `Add`'s 9). The same peel as Step 4 probably applies.
- `BlockReduceMultiply` stays on BigFloat by design.
- Packed storage supports one unary operand; binary packed operands and packed
  output were left unbuilt pending a workload that needs them.

## implmentplan.md Step 9 done — thresholds and latency (2026-08-28)

Gate: full `Pkg.test()` green. Measure-then-decide; one threshold moved, one
deliberately not.

### THREAD_MIN_ELEMS: 32768 → 1024

The old value was far too high. Measured at K = 12 compute, speedup of 4
threads over 1:

| N | Add | Log |
|---|---|---|
| 64 | 0.47x | 0.77x |
| 128 | 0.88x | 1.30x |
| 256 | 1.41x | 2.23x |
| 1024 | 2.66x | 3.19x |
| 4096 | 3.58x | 2.10x |
| 65536 | 3.83x | 3.98x |

The crossover is N ≈ 128–256 for both a cheap and an expensive op — within a
factor of two, so the plan's condition for keeping ONE threshold is met and no
per-op cost class is needed. 1024 sits past the crossover with margin for
machines with fewer cores. Effect: `vmap!` Add K=12 at N=4096 went
57,530 → 16,116 ns (3.57x), and `A .+ B` K=12 at N=4096 58,598 → 16,337 ns.

Also measured and recorded in the docstring: the Shape-A **gather** is never
threaded (it is a flat indexed loop) and is at memory bandwidth already —
1 vs 4 threads is 1.00x at every N from 1 Ki to 64 Ki. So this threshold only
ever governed the compute kernels.

**A pre-existing test caught the consequence.** `test-fastpaths.jl` asserted the
compute kernel allocates nothing at N = 4096 — true only because 4096 was below
the old threshold, so that call ran sequentially. Lowering the threshold makes
it threaded, and `Threads.@threads` allocates scheduler state. Verified that
cost is **1,568 bytes regardless of N** (2 Ki through 256 Ki) while sequential
is exactly 0, and rewrote the test to assert what is actually true: sequential
allocates nothing, and the threaded path's allocation does not scale with N.

### TABLE_EAGER_BITS: left at 16, deliberately

Raising to 18 admits the K = 9 binary band (2^18 entries, 512 KiB, well inside
`TABLE_MAX_BITS`), and at scale it is a large win — warm gather is ~22 µs
whatever the operation, against 238 µs (Add) to 2,082 µs (ArcTan2) of compute at
N = 65,536, with the build repaid in 3–5 calls. Every op measured cleared the
plan's "build ≤ 20x the compute call" bar (worst: ArcTan2 at 4.1x).

Declined anyway, because this gate sees **no element count** — it decides from
the format alone, so one small call pays the whole build:

| ArcTan2, K = 9 | band 16 | band 18 |
|---|---:|---:|
| N = 100 | 9.8 µs | 8,506 µs (**864x slower**) |
| N = 1,000 | 118 µs | 8,874 µs (75x slower) |
| N = 10,000 | 1,215 µs | 8,589 µs (7.1x slower) |

Trading an 864x one-shot regression for a 95x large-array win is not a threshold
decision, it is a missing mechanism — and the mechanism already exists for
ternary signatures (`_ternary_table_for` takes `nelems` and gates an adaptive
band on cumulative elements). Extending the binary gate the same way is the
right follow-up; the numbers and the reasoning are now in the
`TABLE_EAGER_BITS` docstring so the next person does not re-derive them.

### Precompile workload and first-call latency

Added to `@compile_workload`: the value constructors (`T(::Float64)`,
`::Float32`, `::Integer`, `convert`), one Group B ladder row (`Log` — the
enclosure machinery is shared), the three broadcast `copyto!` methods from
Step 7, and `BlockReduceAdd` at B ∈ {4, 16, 32}. `Block{B}` specializes on B,
so precompiling B = 4 does nothing for a B = 16 caller; 16 and 32 are the
MX-standard sizes, and any other B compiles on first use as it must.

| Fresh process | Before | After |
|---|---:|---:|
| `using AIFloats` | 55.6 ms | 57.2 ms |
| first `Log(x)` | 103.0 ms | **6.5 ms** |
| first `A .+ B` | 40.5 ms | **0.01 ms** |
| first `exp.(A)` | 45.0 ms | **0.03 ms** |
| first `BlockReduceAdd` | 136.4 ms | **0.03 ms** |
| first `vmap!` Add | 19.3 ms | **0.62 ms** |

Load cost +1.6 ms for ~340 ms of first-call latency removed; the precompile
cache image stayed at ~0.30 MiB.

A reported 15 ms first `T(1.3)` turned out to be an artifact of the probe
(a closure over a non-const global); measured directly it is 0.21 ms.

`benchmark/latency.jl` NEW: a third suite that shells out to fresh processes —
load and first-call timings cannot be Chairmarks samples, since the quantity of
interest happens exactly once per process.

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
- `src/rules/constraints.jl`: `formatname`, `_NAMED` registry, 504 capitalized
  aliases = datum types (`Binary8p4se === BinaryValue{Binary(8,4,SIGNED,EXTENDED),UInt8}`),
  `Formats` opt-in submodule.
- `src/content/gentables.jl`: real `codetable`/`printcodetable` (by=:code|:value).
- `src/AIFloats.jl`: rewritten module root — include order per plan §7, new
  exports, K ≤ 8 alias export loop, module docstring updated.
- Tests NEW: `test-binaryvalue.jl` (132,857) — construction discipline,
  predicates, total-order walk (NextGreaterThan visits all 2^K exactly once,
  NextLessThan inverts), classification, show styles, aliases;
  `test-codec.jl` (66,700) — **exhaustive 7,602,160-code-point sweep of all 504
  formats**: `_canonical`∘`encode` round-trip + decode ≡ sign·S·2^Q in
  Rational{BigInt}; layout spot checks (0x45→1.625 on Binary8p4se); monotone
  decode.
- `docs/src/50-status.md` rewritten to the new truth.
- Suite totals: Binary Format 122 · Binaryvalue 132,857 · Codec 66,700 ·
  Singletons 334 · Traits 8,610. Doctests pass.

### Corrections made mid-phase (worth knowing)

- `codepoint` must EXTEND `Base.codepoint`, else export clash with Base.
- Binary3p1uf value table is [0,⅛,¼,½,1,2,4,NaN] (B=4) — an early docstring/
  test had it shifted one octave up. Binary8p4sf MaxFinite = 240 (not 248);
  Binary8p4uf MinPositive = 2^-18.

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
  known-value checks (e→2.75, ln2→11/16, sin1→13/16 on Binary8p4se; peels;
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
