# Implementation Plan — realizing [reviewplan.md](reviewplan.md)

Ready-to-apply steps. Each step: files, exact change, test, benchmark line,
gate. Steps are independent commits in this order; a later step never depends
on an earlier one except where stated. All numbers are from the recon on this
tree (i9-14900K, Julia 1.12.6, `-t 4`); the two hypotheses in Steps 4 and 5
were prototyped before writing this and the "after" numbers are measured, not
predicted.

## Status

**Steps 0–5 are enacted** (2026-08-28), each gated on a green full `Pkg.test()`
and recorded in [checkpoint.md](checkpoint.md). Achieved, against the Step 1
baseline: `T8(1.3)` 98.6 → 1.4 ns · `T8(3)` 583 → 1.8 ns · `FMA` 452 → 12.7 ns ·
`Log` 236 → 27.5 ns · all now allocation-free. Two things the plan got wrong
and the work corrected: the Step 4 peel needed a magnitude floor (a nonzero
residual can underflow, so `fma(x, y, -p) == 0` is only a proof of exactness
above `|p| ≥ 2^-915`), and the Step 5 culprit was the missing `@inline`, not
the `try`/`catch` in `_f64guard`, which is load-bearing and was kept.

**Steps 6–10 are also enacted.** Section text below is as *planned*, not as
built — read [checkpoint.md](checkpoint.md) for what actually happened. Steps
6, 7, 8 were reordered after Steps 0–5 landed (see *What actually makes a step
expensive* at the end), and Step 8 was rewritten before enactment once a
prototype showed `Dyadic` already provided the accumulator it proposed to
build. Three further plan claims were corrected by measurement: the packed
running-offset walk is slower, not faster; `arrays/broadcast.jl` cannot load
where the plan placed it; and raising `TABLE_EAGER_BITS` was declined.

Conventions used below:

- `T` = `binary8p4se`, `F` = `BinaryFormatOf(T)`, `x = T(1.5)`, `y = T(0.25)`,
  `z = T(0.75)`.
- "reference" = the path that stays authoritative for the change; every fast
  path must agree with it bit-for-bit on the stated sweep.
- Gate for every step, in addition to what the step lists:
  `julia --project=. -e 'import Pkg; Pkg.test()'` green and
  `julia --project=benchmark benchmark/runbenchmarks.jl` runs.

---

## Step 0 — hygiene (no behavior change)

### 0.1 Shared test helpers

- Create `test/support/helpers.jl` containing `allcodes(F)` and `subcodes(F, n)`
  (currently duplicated at `test/test-compat.jl:20` and
  `test/test-fastpaths.jl:14–15`).
- In each test file that uses them: replace the definitions with
  `include(joinpath(@__DIR__, "support", "helpers.jl"))` guarded by
  `isdefined(Main, :allcodes) ||`.
- Gate: `Pkg.test()` output has no `WARNING: Method definition … overwritten`.

### 0.2 Stale prose in `src/`

| File:line | Now says | Change to |
|---|---|---|
| `src/AIFloats.jl:16` | "Blocks and packed storage are staged next" | "Blocks (`Block`, `BlockVector`, the `Block*`/`Scaled*` operations) and packed storage (`PackedVector`) are implemented; the P = 1 exponent-add block decode is the one remaining performance port (Step 8)." — and delete that clause again after Step 8. |
| `src/types/singletons.jl:416, 426, 436` | "The projection rules themselves are not implemented yet; today …" | Delete the sentence; the rules live in `src/projection/saturate.jl`. Add a `See also [`project`](@ref)`. |
| `src/types/singletons.jl:469` | "applying one to a number is not implemented yet" | "applied to a number by [`project`](@ref)". |
| `src/arrays/blocks.jl:15` | "are performance ports, deferred with the rest" | "the Float128 cascade is not ported; the P == 1 exponent-add decode is Step 8 of docs/implmentplan.md" — then rewrite after Step 8. |
| `src/ops/registry.jl:56` | `op in (:CopySign,) ? :A :` | delete the arm (unreachable: `:CopySign ∈ _EXACT_SELECTION` is matched on line 54). Assert in `test-ops.jl` that `opinfo(:CopySign).group` is unchanged before/after. |

### 0.3 Regression test for the mixed-width ternary LRU

The fix is already in `src/tables/cache.jl:84–118`; only the test is missing.
Add to `test/test-tables.jl`:

```julia
@testset "ternary LRU spans both code widths" begin
    AIFloats.empty_tables!()
    old = AIFloats.TERNARY_CACHE_BYTES[]
    try
        # operands ΣK = 4+4+3 = 11 → 2^11 entries: a UInt16-result table is
        # 4096 B, a UInt8-result one 2048 B. Under a 4096 B budget the second
        # insert must evict the first (the older, other-width) table.
        AIFloats.TERNARY_CACHE_BYTES[] = 4096
        F16 = Binary(9, 4, SIGNED, EXTENDED); F8 = Binary(8, 4, SIGNED, EXTENDED)
        F3 = Binary(4, 2, SIGNED, EXTENDED); F4 = Binary(3, 2, SIGNED, EXTENDED)
        AIFloats.get_table(:FMA, F16, F3, F3, F4, RTE_SN)   # ΣK = 11 ≤ TERNARY_EAGER_BITS (18): built eagerly
        @test AIFloats.table_bytes() == 4096
        AIFloats.get_table(:FMA, F8,  F3, F3, F4, RTE_SN)
        @test AIFloats.table_bytes() == 2048
        @test isempty(AIFloats.TERNARY_CACHE16)
    finally
        AIFloats.TERNARY_CACHE_BYTES[] = old
        AIFloats.empty_tables!()
    end
end
```

(`get_table(op, fr, f1, f2, f3, ρ)` is the ternary signature; entry count is
`2^_sumK(f1, f2, f3)`, bytes = entries × `sizeof(CodeType(fr))`.)

### 0.4 Package dependencies

`Aqua`, `JET`, `SHA`, `Statistics`, `SmallCollections` are in the package
`[deps]` of `Project.toml` but nothing under `src/` uses them (verified by
grep). Move `Aqua` to `[extras]`/`[targets]` next to `JET`; delete
`SmallCollections` and `Statistics` from `[deps]` unless a test needs them
(then `[extras]`). Keep `test/Project.toml` consistent. Gate: `test-quality.jl`
(Aqua `stale_deps`) passes.

---

## Step 1 — benchmark harness

Replace `benchmark/bench_floats{1,2,3}.jl` (three identical copies) with:

```
benchmark/Project.toml
benchmark/runbenchmarks.jl
benchmark/scalar.jl
benchmark/arrays.jl
```

`benchmark/Project.toml`:

```toml
[deps]
AIFloats   = "021c5541-574e-4699-a644-4e7fe83e8672"
Chairmarks = "0ca39b1e-fe0b-4e98-acfc-b1656634c4de"

[sources]
AIFloats = {path = ".."}
```

`benchmark/runbenchmarks.jl`:

```julia
using Chairmarks, AIFloats
const REPORT = Ref(stdout)
row(label, s::Chairmarks.Sample) = println(REPORT[], rpad(label, 44), " ",
    lpad(round(s.time * 1e9; digits = 1), 10), " ns  allocs=", s.allocs, " bytes=", s.bytes)
function withflags(f; fast_arith = true, fast_enclosure = true, threaded = true, eager_bits = 16)
    saved = (AIFloats.FAST_ARITH[], AIFloats.FAST_ENCLOSURE[],
             AIFloats.THREADED_KERNELS[], AIFloats.TABLE_EAGER_BITS[])
    try
        AIFloats.FAST_ARITH[] = fast_arith; AIFloats.FAST_ENCLOSURE[] = fast_enclosure
        AIFloats.THREADED_KERNELS[] = threaded; AIFloats.TABLE_EAGER_BITS[] = eager_bits
        f()
    finally
        AIFloats.FAST_ARITH[], AIFloats.FAST_ENCLOSURE[],
        AIFloats.THREADED_KERNELS[], AIFloats.TABLE_EAGER_BITS[] = saved
        AIFloats.empty_tables!()
    end
end
println("julia $(VERSION)  threads=$(Threads.nthreads())  cpu=$(Sys.cpu_info()[1].model)")
println("commit ", readchomp(`git -C $(pkgdir(AIFloats)) rev-parse --short HEAD`),
        isempty(readchomp(`git -C $(pkgdir(AIFloats)) status --porcelain`)) ? "" : " (dirty)")
suites = isempty(ARGS) ? ["scalar", "arrays"] : ARGS
for s in suites; include("$s.jl"); end
```

`benchmark/scalar.jl` — one `row` per line of reviewplan.md §2's scalar table,
plus one op from each registry group at K = 8 and K = 12
(`Add, Multiply, FMA, Divide, Sqrt, Exp, Log, Sin, ArcTan2Pi, Convert`),
constructors (`T(1.3)`, `T(3)`, `convert(T, 1.3)`), and the veneers
(`x + y`, `fma(x,y,z)`, `x < y`, `Float64(x)`). All with `$`-interpolated
operands.

`benchmark/arrays.jl` — `vmap!` Add/Exp at K = 8 (warm table) and K = 12
(compute, threaded and `withflags(threaded = false)`), `A .+ B`, `exp.(A)`,
`sort`, `PackedVector`/`collect`/packed `vmap`, `blockdecode`,
`BlockReduceAdd`, `BlockDotProduct` at B = 16 and B = 32, and the two cold
cases with `evals = 1` inside `withflags`. N ∈ {4096, 65536}. For arrays also
print `N / s.time / 1e9` as Gelem/s.

Gate: `julia --project=benchmark -t 4 benchmark/runbenchmarks.jl` from a clean
clone after `Pkg.instantiate()`; two consecutive runs agree within 10 % on
every row over 20 ns.

---

## Step 2 — constructor and `convert` default-projection guard

**Measured:** `T(1.3)` 82 ns / 2 allocs; `Convert(T, RTE_SN, 1.3)` 0.7 ns.
**Cause:** `src/ops/scalar.jl:169` keyword `projection::Projection =
DefaultProjection()` reads an abstract `Ref{Projection}` and calls through it
dynamically. `src/compat/base.jl:368` does the same for `convert(T, ::Unsigned)`.
The same-format op methods already solve this with the speculation guard at
`scalar.jl:100–104`; apply the identical pattern.

`src/ops/scalar.jl:169–172` → 

```julia
@inline function (::Type{BinaryValue{F,U}})(x::Real;
        projection::Union{Nothing, Projection} = nothing,
        rng::MaybeRNG = nothing, R::MaybeR = nothing) where {F<:Binary, U<:Unsigned}
    projection === nothing || return Convert(F, projection, x; rng, R)::BinaryValue{F,U}
    # SPECULATION GUARD (see the same-format op methods above): the untouched
    # default RTE_SN is tested by identity and called with the literal
    # constant so the common case is a static, allocation-free call
    ρ = DefaultProjection()
    ρ === RTE_SN && return Convert(F, RTE_SN, x; rng, R)::BinaryValue{F,U}
    Convert(F, ρ, x; rng, R)::BinaryValue{F,U}
end
```

`src/compat/base.jl:367–368` → (an `Unsigned` handed to the struct
constructor is a *code point*, so this must stay on `Convert`; only the
guard is added)

```julia
function Base.convert(::Type{T}, x::Unsigned) where {T<:BinaryValue}
    ρ = DefaultProjection()
    ρ === RTE_SN && return Convert(T, RTE_SN, x)::T
    Convert(T, ρ, x)::T
end
```

Docstring: the keyword is still documented as "defaults to the session
projection"; `nothing` is an implementation detail — say so in one line.

Tests (`test/test-fastpaths.jl`, next to line 95):

```julia
@test (@allocated T(1.3)) == 0
@test (@allocated convert(T, 1.3)) == 0
@test (@allocated T(1.3f0)) == 0
DefaultProjection!(RTZ_SF); try
    @test T(1.3) == Convert(T, RTZ_SF, 1.3)          # the non-default branch is live
finally DefaultProjection!(RTE_SN) end
@test T(1.3; projection = RTP_SN) == Convert(T, RTP_SN, 1.3)
```

Benchmark rows: `T(1.3)`, `convert(T, 1.3)`. Target ≤ 3 ns, 0 allocs.

---

## Step 3 — Integer conversion without BigFloat

**Measured:** `T(3)` 586 ns / 28 allocs.
**Cause:** `src/ops/scalar.jl:150–155` builds a `BigFloat` for every Integer.

Replace with an exact-width dispatch. Any Integer with `|x| ≤ 2^53` is exact
in `Float64`; the existing `Convert(fr, ρ, ::Float64)` then does the rest
(one rounding, as before, because the widening is exact).

```julia
function Convert(fr::Type{<:Binary}, ρ::Projection, x::Integer;
                 rng::MaybeRNG = nothing, R::MaybeR = nothing)
    if -(Int64(1) << 53) <= x <= (Int64(1) << 53)     # exact in Float64
        return Convert(fr, ρ, Float64(x); rng, R)
    end
    b = setprecision(BigFloat, max(64, ndigits(x, base = 2) + 8)) do
        BigFloat(x)                                   # exact at this width
    end
    project(fr, ρ, b; R = _drawR(ρ, rng, R))
end
```

`Bool` is an `Integer` and takes the same path. The comparisons are exact for
every Integer type including `BigInt` and `UInt64` (Julia compares mixed
integer types by value).

Tests (`test/test-compat.jl`): for each `F` in the K ≤ 8 grid and each `n` in
`-300:300 ∪ {2^53 - 1, 2^53, 2^53 + 1, typemax(Int64), typemin(Int64), big(2)^80}`
assert `Convert(F, ρ, n) == Convert(F, ρ, BigFloat(n))` for `ρ ∈ (RTE_SN, RTZ_SF, RTP_SN)`,
and `(@allocated T(3)) == 0`.

Benchmark row: `T(3)`. Target ≤ 3 ns.

---

## Step 4 — FMA: Float64-first

**Measured:** `FMA(T, RTE_SN, x, y, z)` 451 ns; prototype (product exactness
checked in Float64, then the existing `Add` cascade) 11 ns.
**Cause:** `src/ops/oracle.jl:305–322` widens to `Float128` unconditionally.

Insert after the `FAST_ARITH[] || return _exact_fma(x, y, z)` line
(so `FAST_ARITH[] = false` remains the pure reference):

```julia
    if F === Float64
        p = x * y
        if isfinite(p) && fma(x, y, -p) == 0.0        # product exact in Float64
            return ωeval(Val(:Add), p, z)             # Add's own cascade decides
        end
    end
```

Why correct: `fma(x, y, -p) == 0` with finite `p` proves `p == x·y` exactly
(no rounding, no overflow; underflow to a subnormal `p` is still exact when
the residual is zero). `x·y + z` is then the two-operand exact sum, which
`ωeval(Val(:Add), ::Float64, ::Float64)` already resolves to Float64 /
Float128 / `Sticky` / BigFloat with the same escalation proofs as `Add`. The
NaN/∞/zero rows above the insertion point already returned, so `z` is finite
here and `p ≠ 0`.

Tests: `test/test-fastpaths.jl` already sweeps ternary ops against
`FAST_ARITH[] = false`; add `FMA` to that sweep over the full K = 5 code cube
(32³ = 32,768 triples) and a K = 8 subsampled cube, plus the directed cases
`(x, y, z)` with `x·y` exact and `|x·y| ≫ |z|` (sticky), `x·y ≈ -z`
(cancellation), and `x·y` subnormal.

Benchmark rows: `FMA(T, RTE_SN, x, y, z)`, `fma(x, y, z)`. Target ≤ 15 ns.

---

## Step 5 — Group B enclosure builders inline

**Measured:** `Log`, `Log2`, `Sin`, `Cos`, `ScaledAdd` 250–320 ns / 7 allocs;
`Exp` 22 ns / 0 allocs. Prototype: `@inline _mpfr1` alone → `Log` 28 ns / 0
allocs; also removing the `try` in `_f64guard` → 25 ns. Cause confirmed:
`_mpfr1`/`_mpfr2` are not inlined when `f` may throw, so the three closures
are boxed and the `Enclosure` is heap-allocated even though stage 1 decides.

`src/ops/oracle.jl:89, 96` → prefix both definitions with `@inline`:

```julia
@inline _mpfr1(f, x) = Enclosure(_ladder1(f, x), _fq1(f, x), _yd1(f, x))
@inline _mpfr2(f, x, y) = Enclosure(_ladder2(f, x, y), _fq2(f, x, y), _yd2(f, x, y))
```

Also `@inline` on `_mpfr_pitrig` (line 108) and `_mpfr_divpi` (line 120), then
measure `SinPi`, `ArcTan2Pi`; keep only if they drop the same way. Keep the
`try/catch` in `_f64guard`: it costs 3 ns and it is what makes an
out-of-domain libm call yield `NaN` (stage 1 skipped) instead of throwing.

Tests: existing `FAST_ENCLOSURE[] = false` equivalence in `test-fastpaths.jl`;
add `(@allocated Log(T, RTE_SN, x)) == 0` for one op per libm family
(`Log`, `Sin`, `ArcTan`, `Sinh`, `SinPi`).

Benchmark rows: `Log`, `Sin`, `ArcTan2Pi` at K = 8 and K = 12.
Target ≤ 35 ns, 0 allocs.

`ScaledAdd` (188 ns / 7 allocs) is a block-layer op (`blocks.jl`, generated
`Scaled*` family) and was **not** covered by the prototype. Re-measure after
this step; if it still allocates, attribute it separately — the candidates are
`_samecarrier`/`_nosticky` returning a carrier union and the `_bp_element`
quotient — and fold the fix into Step 8.

---

## Step 6 — packed unary gather without the tile adapter

**Measured:** packed `vmap(:Negate, F, RTE_SN, P)` 46 µs vs 8.6 µs unpacked.
**Cause:** `src/arrays/packed.jl:102–117` unpacks 256-element tiles into a
scratch and calls `vmap!` on views.

In `_vmap_packed`, before the tile loop:

```julia
    if !isstochastic(ρ)
        tbl = table_for(op, BinaryFormatOf(OUT), BinaryFormatOf(T), ρ)   # already @noinline
        if tbl !== nothing
            K = Int(BitwidthOf(T)); mask = _packmask(K); data = pv.data
            @inbounds for i in 1:pv.n
                w, off = _wordpos(K, i)
                c = data[w] >> off
                _crosses_word(off, K) && (c |= data[w + 1] << (64 - off))
                out[i] = rawvalue(BinaryFormatOf(OUT), tbl[Int(c & mask) + 1])
            end
            return out
        end
    end
```

`_vmap_packed` takes `v::Val{op}`; bind `op` in the signature. The tiled path
remains for stochastic ρ and untabled signatures. If the K-bit extraction
dominates, a second pass can walk words with a running `off` (no
multiply/shift per element); measure first.

Tests (`test/test-blocks.jl` or a new `test-packed.jl`): for K ∈ {3, 5, 7, 9, 12}
and N ∈ {0, 1, 63, 64, 65, 1000}, `vmap(op, F, ρ, PackedVector(A)) == vmap(op, F, ρ, A)`
for `op ∈ (:Negate, :Exp)` and `ρ ∈ (RTE_SN, RTZ_SF)`; unchanged stochastic
test with a seeded rng.

Benchmark rows: packed vs unpacked unary `vmap`, K = 5 and K = 8. Target ≤ 1.5×
the unpacked row.

---

## Step 7 — broadcasting through the kernels

**Measured:** `A .+ B` 631 µs vs `vmap!(d, Val(:Add), RTE_SN, A, B)` 15 µs
(N = 65,536, K = 8). Broadcasting calls the scalar veneer per element.

New file `src/arrays/broadcast.jl`, included immediately after
`arrays/kernels.jl` (and add the line to the include-order note in
`docs/structuralplan.md` §7). It hooks `copyto!` on a fully-materialized
`Broadcasted` whose function is a registered veneer and whose arguments are
same-format datum arrays. Nested/fused expressions and scalar operands do not
match the signature and fall back to Base unchanged, so semantics are
untouched (the scalar veneer and `vmap!` are already asserted equal in
`test-kernels.jl`).

```julia
# arrays/broadcast.jl — route `f.(A, B)` through vmap! when f is a registered
# veneer and every operand is a same-format datum array. Anything else
# (fused chains, scalars, mixed formats) falls back to Base's elementwise loop.
using Base.Broadcast: Broadcasted, DefaultArrayStyle

const _BC_OPS = (
    (:Negate => :-, 1), (:Add => :+, 2), (:Subtract => :-, 2),
    (:Multiply => :*, 2), (:Divide => :/, 2), (:FMA => :fma, 3),
    ((op => bf, 1) for (op, bf) in _BASE_UNARY)...,
    ((op => bf, 2) for (op, bf) in _BASE_BINARY)...,
)
for ((op, bf), arity) in _BC_OPS
    args = [Symbol(:A, i) for i in 1:arity]
    argtypes = [:(AbstractArray{T}) for _ in 1:arity]
    @eval function Base.copyto!(dest::AbstractArray{T},
            bc::Broadcasted{<:DefaultArrayStyle, <:Any, typeof(Base.$bf), <:Tuple{$(argtypes...)}}
            ) where {T<:BinaryValue}
        $(args...), = bc.args
        if all(a -> axes(a) == axes(dest), bc.args)
            ρ = DefaultProjection()                      # same guard as the veneers
            ρ === RTE_SN && return vmap!(dest, Val($(QuoteNode(op))), RTE_SN, $(args...))
            return vmap!(dest, Val($(QuoteNode(op))), ρ, $(args...))
        end
        invoke(Base.copyto!, Tuple{AbstractArray, Broadcasted}, dest, bc)   # broadcasting shapes
    end
end
```

Notes for the implementer:

- `Base.:-` appears with arity 1 and 2; two methods, distinct `Tuple` lengths
  — no clash.
- `Broadcasted` in Julia 1.12 has four type parameters
  `(Style, Axes, F, Args)`; the signature above relies on that order.
- The `invoke` fallback targets Base's `copyto!(::AbstractArray, ::Broadcasted)`
  (verified present in 1.12; it converts to `Broadcasted{Nothing}` and runs
  the generic loop). `Broadcasted`'s parameters are `(Style, Axes, F, Args)`
  in 1.12 (verified).
- Result eltype for `A .+ B` is chosen by Broadcast via inference of `+(T,T)`
  and is `T`, so `copy(bc)` allocates a `Vector{T}` and lands in this
  `copyto!`. `A .+ x` (scalar) does not match and stays on the slow path — a
  follow-up, not this step.

Tests (`test/test-kernels.jl`):

```julia
for (bf, op, n) in ((+, :Add, 2), (-, :Subtract, 2), (*, :Multiply, 2), (exp, :Exp, 1), (fma, :FMA, 3), (-, :Negate, 1))
    args = ntuple(_ -> rand(T, 1000), n)
    @test bf.(args...) == vmap(op, F, RTE_SN, args...)
    d = similar(args[1]); d .= bf.(args...); @test d == vmap(op, F, RTE_SN, args...)
end
@test (A .+ B) .* C == vmap(:Multiply, F, RTE_SN, vmap(:Add, F, RTE_SN, A, B), C)   # fused chain still correct
@test A .+ A[1] == [a + A[1] for a in A]                                              # scalar operand falls back
@test exp.(A[1:0]) == T[]
M = reshape(A[1:64], 8, 8); @test M .+ M == vmap(:Add, F, RTE_SN, M, M)
```

`test-quality.jl` (Aqua ambiguities) is the gate that the `copyto!` methods
do not collide with Base's.

Benchmark rows: `A .+ B`, `exp.(A)`, `fma.(A, B, C)` at N = 65,536, K = 8 and
K = 12. Target: within 1.2× of the corresponding `vmap!` row.

---

## Step 8 — blocks: concrete Float64 lanes and Dyadic accumulation

**Revised 2026-08-28 after measuring.** The first draft of this step proposed
`_mexp` / `_sum_fixed` / `_fixed_to_carrier` — an Int128 fixed-point
accumulator with a hand-derived 126-bit overflow budget. That is a
reimplementation of `Dyadic` (`src/carriers/dyadic.jl`), which already *is*
`S::Int128 · 2^Q::Int64`, already has `add_dy` / `add_dy_checked` /
`mul_dy` with the alignment and width preconditions worked out
(`DYADIC_ALIGN_MAX = 94`, `nbits + d ≤ 126`), is already covered by
`test-dyadic.jl` with golden digests, and is already accepted by
`project` and `_finish`. Writing a second one would be the single riskiest
thing in this plan for no gain. **Use Dyadic.**

### What was measured (B = 16, one prototype run)

| | time | allocs |
|---|---:|---:|
| `BlockReduceAdd` | 2,899 ns | 189 |
| ├ `blockdecode` | 242 ns | 17 |
| └ `_reduce_add_value` (BigFloat) | 2,173 ns | 151 |
| **Dyadic accumulation of the same lanes** | **156 ns** | **0** |
| `project(F, ρ, ::Dyadic)` | 6.9 ns | 0 |

Same sum, bit-identical, 14x faster, no allocation. Projected
`BlockReduceAdd` ≈ 200 ns against the earlier target of < 300 ns.

Also measured, and it corrects the diagnosis above: `blockdecode` on a rung-1
block **already returns a concrete `NTuple{16, Float64}`**. The 17 allocations
are not heterogeneous lanes — they are `ωeval`'s *inferred* return being a
carrier union, so `ntuple` boxes each lane on the way even though every value
lands as a `Float64`. The fix in 8.1 is still the right one; the reason is
inference, not representation.

### 8.1 `blockdecode`: a concrete-typed fast lane

```julia
@inline function blockdecode(b::Block{B,S,E}) where {B,S,E}
    Sv = decode(b.s)
    # rung-1 scale and elements: try the all-lanes-exact-in-Float64 case, which
    # is the MX-shaped common case. P_S == 1 scales are powers of two, so S·x is
    # a pure exponent shift; a general S is certified lane by lane by fma. The
    # point is not that the values differ from the generic path (they do not) —
    # it is that this ntuple is inferred NTuple{B,Float64}, so no lane is boxed.
    if datumcarrier(BinaryFormatOf(S)) === Float64 && datumcarrier(BinaryFormatOf(E)) === Float64
        xs = ntuple(i -> decode(b.x[i])::Float64, Val(B))
        fast = ntuple(i -> Sv * xs[i], Val(B))
        all(i -> isfinite(fast[i]) && fma(Sv, xs[i], -fast[i]) == 0.0, 1:B) && return fast
    end
    ntuple(i -> ωeval(Val(:Multiply), Sv, decode(b.x[i])), Val(B))
end
```

A NaN or ±∞ lane fails `isfinite` and takes the generic path, so the draft's
fold algebra is untouched. Return type is
`Union{NTuple{B,Float64}, NTuple{B,Any}}` — two concrete types, so callers
union-split. Delete the `blocks.jl:15` sentence after this step.

### 8.2 Guarded Dyadic accumulation

`add_dy` throws when the operands align past `DYADIC_ALIGN_MAX`; a wide
exponent spread is reachable (a K=16, P=1 element format has B = 32768). So
the accumulator needs a *predicate*, not a throw:

```julia
# exact Σ of finite Float64 lanes, or nothing when a partial sum would leave
# Dyadic's exact band. Mirrors add_dy_checked's preconditions, returning
# rather than throwing, so the caller can fall back to the BigFloat oracle.
function _dyadic_sum(X::NTuple{B,Float64}) where {B}
    acc = DYADIC_ZERO
    for i in 1:B
        v = X[i]
        iszero(v) && continue
        d = Dyadic(v)
        acc.S == 0 && (acc = d; continue)
        hi, lo = acc.Q >= d.Q ? (acc, d) : (d, acc)
        Δ = Int(hi.Q - lo.Q)
        (Δ > DYADIC_ALIGN_MAX || nbits_dy(hi.S) + Δ > 126) && return nothing
        acc = add_dy(acc, d)
    end
    acc
end
```

`BlockReduceAdd`: when `blockdecode` returned the `Float64` tuple and every
lane is finite, try `_dyadic_sum`; on `nothing`, fall through to the existing
`_reduce_add_value`. The special-value fold (`any(isnan)`, ±∞) stays in front,
unchanged and shared.

### 8.3 `BlockDotProduct`

The existing `cls` fold for NaN/±∞ lanes stays in front. When both blocks
decoded to `Float64` tuples and all lanes are finite, form each lane product in
Float64 and certify it with `fma` exactly as 8.1 does — if every product is
exact, `_dyadic_sum` them; otherwise fall back. Nothing new is invented.

`BlockReduceMultiply` is deliberately **not** changed: accumulating products
grows the significand by `P_S + P_E` per lane, so `mul_dy`'s `nbits ≤ 96`
precondition fails almost immediately at B = 16. BigFloat is the right carrier
there and the row stays as it is.

### Tests

`test/test-blocks.jl`, differential against the BigFloat path, which remains
live as both fallback and oracle:

- 2,000 pseudo-random blocks at B ∈ {1, 4, 16, 32}, over a P=1 power-of-two
  scale and a general non-power-of-two scale, elements `binary8p4se` and
  `binary5p2se`: `BlockReduceAdd` and `BlockDotProduct` must equal the result
  with the fast path disabled.
- Blocks containing NaN, +∞, −∞, all-zero, and max-magnitude lanes.
- A wide-spread block that must *reject* the Dyadic path (assert it still
  agrees with BigFloat).
- `@allocated BlockReduceAdd(...) == 0` for a finite B = 16 block.

### Cost

~30 lines of new code, no new arithmetic. Closer to Step 6 in risk than to the
"high" label this step carried before the prototype: `add_dy` is not being
written here, only called, and `test-dyadic.jl` already guards it.

---

## Step 9 — thresholds and latency (measure, then decide)

Do these only with the harness from Step 1; each is a one-line constant
change or nothing.

1. `TABLE_EAGER_BITS` (`src/tables/policy.jl:33`, currently 16). Measure the
   K = 9 binary `Add` build (2^18 entries) once, and the warm gather at
   N = 65,536, against the compute path (237 µs on 4 threads, 927 µs on 1).
   Raise to 18 for **binary** signatures only if build ≤ 20 × the compute call
   and the resident 256 KB–512 KB per table stays under `TABLE_CACHE_BYTES`'s
   documented budget; otherwise leave it and record the numbers in the policy
   docstring.
2. `THREAD_MIN_ELEMS` (`src/arrays/kernels.jl:24`, 32,768). Sweep N ∈
   {4k, 8k, 16k, 32k, 64k} for `Add` K = 12 and `Log` K = 12 compute, 1 vs 4
   threads. Keep one threshold if the crossovers are within 2× of each other;
   otherwise lower it for Group B via one `Val`-dispatched
   `_thread_min(::Val{op})` returning either of two constants — not one per op.
3. Load and first call: in a fresh process, `@time using AIFloats`, then
   `@time` each of `Add(x,y)`, `Exp(x)`, `vmap!(…)`, `A .+ B`, `T(1.3)`.
   Add `A .+ B` and `T(1.3)` to the `@compile_workload` in `src/AIFloats.jl`.
   Record before/after in the benchmark output header.

---

## Step 10 — documentation close-out

- `README.md`, `docs/src/20-concepts.md`, `docs/src/50-status.md`: state that
  datums, operations, blocks, and packed storage are implemented; list the
  performance facts a caller needs: K ≤ 8 decode is a table; warm binary
  tables exist for ΣK ≤ `TABLE_EAGER_BITS`; `vmap!` threads above
  `THREAD_MIN_ELEMS`; broadcasting of veneers over same-format arrays uses the
  kernels, fused chains do not; stochastic array results are sequential and
  seed-reproducible; packed storage trades compute for memory only when
  `packing_saves(T)`.
- `docs/checkpoint.md`: append an entry listing the ten steps, the accepted
  benchmark ratios, and anything rejected (with its number).
- `docs/planreview.md` is gone; `reviewplan.md` notes what it was and which
  of its claims were checked and found stale.

---

## Order of execution and expected result

| Step | Risk | Gain |
|---|---|---|
| 0 hygiene | none | ✅ trustworthy comments, no test warnings |
| 1 harness | none | ✅ `benchmark/`, reproducibility for 2–9 |
| 2 ctor guard | none | ✅ `T(1.3)` 98.6 → **1.4 ns**, 0 allocs |
| 3 Integer | low | ✅ `T(3)` 583 → **1.8 ns**, 0 allocs |
| 4 FMA | low (exact proof) | ✅ 452 → **12.7 ns** |
| 5 `@inline _mpfr*` | none | ✅ `Log` 236 → **27.5 ns**, `Sin` 246 → **24.8**, 0 allocs |
| 6 packed | low | 46 µs → < 13 µs |
| 7 broadcast | medium (dispatch surface) | `A .+ B` 631 µs → ~15 µs |
| 8 blocks | medium (reuses Dyadic; revised after prototype) | 2.9–5.3 µs → ~0.2 µs, 0 allocs |
| 9 thresholds | low | ✅ `THREAD_MIN_ELEMS` 32768 → 1024 (3.6x at N=4096); `Log` cold 103 → **6.5 ms** |
| 10 docs | none | ✅ performance characteristics documented |

**All ten steps enacted.** See [checkpoint.md](checkpoint.md) for what each one
changed, what it measured, and the two proposals that measurement rejected.

Nothing here changes public names, parameter order, projection semantics, or
the rigorous reference paths.

### What actually makes a step expensive

Not lines of code. The cost is the **number of independent correctness
decisions that have no existing reference to check against**. Steps 2–5 each
had exactly one decision and a reference sitting right there
(`FAST_ARITH[] = false`, the explicit-projection `Convert`), which is why they
were small. That is also why 6–8 are ordered as they are:

- **6 packed** — ~15 lines inside one function. The reference is the unpacked
  `vmap!`, already exact; the equivalence test is a mechanical K × N grid.
  Nothing is invented. Nearest neighbour: Step 3.
- **7 broadcast** — ~40 lines, but a wide surface, and every shape is an
  intercept-or-fall-back decision. Measured on this tree, all of these produce
  a datum eltype and so are candidates: `A .+ B`, `exp.(A)`, `(A .+ B) .* B`
  (fused), `M .+ M` (matrix), `view .+ view`, and `A .+ B[1]` — that last one
  is the trap, because the signature in this step takes two *arrays* and will
  quietly leave the scalar-operand form on the slow path (correct, not fast).
  `A .+ 1.0` yields `Float64` and `A .< B` yields `Bool`; both must fall back.
  Aqua's ambiguity check against Base's `copyto!` methods is an
  iterate-until-clean loop. Failure mode if wrong: silently intercepting
  something it should not — wrong numbers, not a crash.
- **8 blocks** — was the only step inventing arithmetic, and a prototype
  showed it did not need to: `Dyadic` already is the Int128 fixed-point
  accumulator, with the overflow preconditions derived and tested. Rewritten
  to call it. What remains is the guard predicate (Dyadic throws where this
  needs to fall back) and the special-value folds, which stay shared with the
  BigFloat path that is kept live as the oracle. Step 4's underflow hole —
  where `fma(x, y, -p) == 0` certified an *inexact* product and only a
  written-down test assertion caught it — is still the precedent for how the
  fma certification in 8.1/8.3 has to be tested.

Risk of getting it *silently* wrong runs 8 > 7 > 6, which is why the order is
6, 7, 8: most throughput per unit of risk first, and the step whose bugs are
hardest to see last, when the harness and the differential habits are
established.
