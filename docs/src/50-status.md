# [Implementation status](@id status)

```@meta
CurrentModule = AIFloats
```

AIFloats.jl models P3109 formats completely, and now also their **values** and
**arithmetic**: every datum of every format can be named, decoded, enumerated,
ordered, classified, and operated on — through the draft's register or through
Julia's own operators — as scalars, arrays, shared-scale blocks, and packed storage.
This page says plainly what exists and what the deliberate limits are.

## Implemented

| Area | What works |
|:--|:--|
| Format specifiers | [`Binary`](@ref) construction, canonicalization, validation (`3 <= K <= 16`) |
| Format fields | [`BitwidthOf`](@ref), [`PrecisionOf`](@ref), [`SignednessOf`](@ref), [`DomainOf`](@ref), [`TrailingSignificantBitsOf`](@ref), [`ExponentBiasOf`](@ref), [`ExponentBitwidthOf`](@ref) |
| Format predicates | [`is_signed`](@ref), [`is_unsigned`](@ref), [`is_finite`](@ref), [`is_extended`](@ref) |
| Axis singletons | [`SIGNED`](@ref), [`UNSIGNED`](@ref), [`FINITE`](@ref), [`EXTENDED`](@ref), with `Bool` interop |
| Storage selection | [`CodeType`](@ref), [`ValueType`](@ref) |
| **Datums** | [`BinaryValue`](@ref) — a format's member as its code point; `codepoint`, [`BinaryFormatOf`](@ref) |
| **The codec** | [`decode`](@ref) (exact, on the format's carrier: `Float64` for B ≤ 512, `Float128` for B ≤ 8192, the exact dyadic carrier `AIFloats.Dyadic` above); the canonical field split and its encode inverse, verified over every code point of all 504 formats |
| **Special values** | [`MaxFiniteOf`](@ref), [`MinFiniteOf`](@ref), [`MinPositiveOf`](@ref), [`MaxSubnormalOf`](@ref), [`MinNormalOf`](@ref); NaN/Inf/zero placement |
| **Enumeration** | [`codetable`](@ref), [`printcodetable`](@ref); the 504 capitalized aliases (`Binary8p4se`), K ≤ 8 exported, the rest via `AIFloats.Formats` |
| **Total order** | NaN-first order keys, [`Class`](@ref)/[`FPClass`](@ref), [`NextGreaterThan`](@ref)/[`NextLessThan`](@ref) |
| **Datum display** | four styles — `:value` (default), `:codepoint`, `:datum`, `:typed` — via [`set_show_style!`](@ref) |
| Projection vocabulary | 9 rounding modes (stochastic ones carry their random-bit budget `N`; [`isstochastic`](@ref), [`nrandbits`](@ref)), 3 saturation modes, [`Projection`](@ref) and its 27 constants |
| **Projection behavior** | [`project`](@ref) — the single write path: round to precision → saturate → encode, for every rounding mode (sticky protocol, stochastic at fixed `R`) and all three saturation modes, from `Float64`/`Float128`/`BigFloat`; the interval oracle `AIFloats.project_interval` |
| **Operations** | the draft register — `Add`, `Subtract`, `Multiply`, `Divide`, `FMA`, `FAA`, `Sqrt`, `Exp`, `Log`, the trig/hyperbolic families and their π-scaled forms, `Hypot`, `Clamp`, the extremum family — correctly rounded via exact evaluation or interval enclosure; [`Convert`](@ref) from datums, floats, and integers |
| **Value construction** | `Binary8p4se(1.5)` (via `Convert` under the task's default projection or an explicit `projection` keyword) |
| **Default projection** | [`DefaultProjection`](@ref), bound for a dynamic extent by [`with_projection`](@ref); `DefaultRoundingMode`/`DefaultSaturationMode` derive from it |
| **Random datums** | `rand` (default `RTZ_SN`, provably `< 1`) and `randn` (default `RTE_SF`, tails clamp; signed formats only) |
| **Array kernels** | every register op elementwise over arrays — `Add(F, ρ, A, B)`, `Exp(A)` — via `vmap`/`vmap!`; pure projections gather from a memoized table when policy grants one, otherwise compute per element (same answer either way); stochastic projections run a sequential, seeded-reproducible loop |
| **Tables** | memoized result tables per `(op, formats, projection)`, fetched internally by the kernels. Public surface: [`table_policy`](@ref) (prospective, never mutates a counter), `AIFloats.table_stats` and `AIFloats.table_entries` (one locked snapshot each, details summing to totals), `AIFloats.empty_tables!`. Byte and build-time budgets refuse loudly; ternary eager/adaptive bands evict LRU |
| **Base surface** | same-format `+ - * /`, `abs`, `sqrt`, `exp`, `log`, the trig/hyperbolic families, `hypot`, `copysign`, `max`/`min` (NaN-propagating), `fma`/`muladd`, `clamp` — each one register call under the task's default projection; `Op(ρ, x)` projection-first convenience; comparison (`==`/`<` unordered on NaN), `isless`/`sort` in the draft's **NaN-first** total order (a counting sort, `AIFloats.CodeCountingSort`); `hash`/`Dict`/`Set` via `Base.decompose` |
| **AbstractFloat contract** | `zero`/`one`/`eps`/`typemin`/`typemax`/`floatmin`/`floatmax`/`precision`; `exponent`/`significand`/`frexp`/`ldexp`; `round`/`floor`/`ceil`/`trunc` and `round(x, RoundUp)` etc. as one projection each; `nextfloat`/`prevfloat` (off-lattice into NaN) |
| **Conversion & promotion** | `Float64`/`Float32`/`Float16`/`BFloat16`/`Float128`/`BigFloat`/`Int(x)`; `convert` (value semantics, `Unsigned` included); `x + 1.0` promotes to the format's public carrier `AIFloats.promotecarrier` — `Float64`, `Float128`, or `BigFloat` by exponent bias; `similar` keeps element types concrete; `reinterpret` checks the representation invariant |
| **Stated refusals** | `rem`/`mod`, `round(x, RoundNearestTiesUp)`/`RoundFromZero`, `Rational` inputs — each throws an `ArgumentError` that says why, never a bare `MethodError` |
| **Blocks** (draft §5) | [`Block`](@ref) `(scale, elements)`; `BlockOp`/`ScaledOp` for every register op (`BlockAdd(FR, ρ, b1, b2, sr)`, `ScaledAdd(FR, ρ, s1, x1, s2, x2)`), the reductions [`BlockReduceAdd`](@ref)/[`BlockReduceMultiply`](@ref)/[`BlockDotProduct`](@ref) with exact accumulators at derived precision, the conversions [`ConvertFromBlock`](@ref)/[`ConvertToBlock`](@ref)/[`ConvertToBlockMaxAbsFinite`](@ref); [`BlockVector`](@ref) structure-of-arrays storage |
| **Packed storage** | [`PackedVector`](@ref) — code points at `K` bits per element in 64-bit words; kernels run unpack → compute → emit (`AIFloats.vmap(op, F, ρ, pv)`); [`packing_saves`](@ref) |
| **Performance layers** | the Float64 bit path and the Dyadic fixed-point path of `round_to_precision`, pinned bit-identical to the generic core (35M comparisons); Float128 exactness proofs and the `Sticky` wide-spread escape for Group A; eager Float64/Float128 envelope stages before the MPFR ladder for every enclosure — each switchable (`AIFloats.FAST_ARITH`, `AIFloats.FAST_ENCLOSURE`) and pinned equal to the rigorous path; the `Dyadic` carrier is verified against golden digests captured from SmallFloats' original; pure-Julia `fma128`/`faa128` for `Float128` |
| **Governance** | [`conformance`](@ref) — the draft-§4.6 declaration derived live from the registry, the table cache, and the κ registry ([`conformance_report`](@ref), [`conformance_dict`](@ref)); [`register_approx!`](@ref)/[`measure_kappa`](@ref) — κ measured by enumeration, understatement rejected; [`ftz_variant`](@ref), the Annex's worked example; [`draft_identity`](@ref) with the retained transliteration's digest |
| IEEE 754 aliases | [`binary16`](@ref), [`binary32`](@ref), [`binary64`](@ref), [`binary128`](@ref), [`bfloat16`](@ref) |

Every accessor and predicate works on the `Binary` format type, the `BinaryValue`
datum type, and a datum. A format has no instance form: `F()` raises, because `F`
already *is* the format. Calling a format constructs a **datum**, so `F(x) isa F`
is `false` and the datum type is spelled `BinaryValue(F)`.

Construction has one semantic axis. `F(x)`, `BinaryValue(F, x)`, `BinaryValue{F}(x)`,
and `convert(BinaryValue(F), x)` all mean *the number `x`, projected into `F`* —
`Unsigned` included, so `F(0x03)` is three. A **code point** is a different
question with a different spelling, [`fromcode`](@ref).

## [Performance characteristics](@id performance)

Facts a caller needs in order to predict cost. All are measured; the benchmark
suite that produces them is `benchmark/runbenchmarks.jl` (an isolated
environment — Chairmarks is not a dependency of the package). That suite is run
during every documentation build and its output is reproduced verbatim under
[Benchmark results](@ref benchmarks), so the numbers on this page can be checked
against the machine that built it.

**Decoding.** `K ≤ 8` decodes through a `@generated` constant table (~1.4 ns);
wider formats compute the value (~3 ns). Both are allocation-free.

**Tables.** A unary or binary signature whose operand bits sum to
`AIFloats.TABLE_EAGER_BITS[]` (16) or fewer is memoized on first array use, and
subsequent calls are a flat indexed gather — for `K = 8` binary `Add` at
65,536 elements that is ~15 µs against ~240 µs of computation. The band is a
bound on *build time*: the gate sees only the formats, not the call's length,
so it is deliberately set where a first call can afford the build. Signatures
above it always compute. Ternary signatures additionally have an adaptive band
(`TERNARY_ADAPTIVE_BITS`) that builds only after a signature has processed
`TERNARY_BUILD_ELEMS` cumulative elements.

**Threading.** Compute kernels thread above `AIFloats.THREAD_MIN_ELEMS[]`
(1024), giving roughly 2.7–4x on four threads. The measured crossover is near
256 elements for both cheap and expensive operations. The table gather is never
threaded: it runs at memory bandwidth already. Threading costs a fixed ~1.6 KB
of scheduler state per call, independent of length; the sequential kernels
allocate nothing.

**Broadcasting.** `f.(A, B)` routes through the array kernels when `f` is a
registered veneer and every operand is a same-format datum array sharing the
destination's axes — so `A .+ B` costs what `vmap!` costs. Fused chains
(`(A .+ B) .* C`), scalar operands (`A .+ B[1]`), mixed element types
(`A .+ 1.0`), predicates (`A .< B`), and shape broadcasts keep Base's
element-at-a-time loop and are correspondingly slower.

**Stochastic projection.** Array results are produced sequentially in index
order from a single RNG stream, so a seeded call is reproducible and never
depends on the scheduler. Stochastic signatures are never tabled.

**Packed storage.** [`PackedVector`](@ref) saves memory only when
[`packing_saves`](@ref) is `true` (that is, when `K` is not the storage unit's
width). It trades compute for that memory: a tabled unary `vmap` over packed
input runs about 3x an unpacked one, because the codes must be extracted from
the bit stream before they can index the table.

**Blocks.** When a block's scale and elements both decode to `Float64` and
every lane product is exact, [`BlockReduceAdd`](@ref) and
[`BlockDotProduct`](@ref) accumulate exactly in the `Dyadic` carrier and
allocate nothing (~270 ns and ~300 ns at `B = 16`). Wider carriers, non-finite
lanes, or a lane spread beyond `Dyadic`'s exact alignment band fall back to
`BigFloat` at a derived precision — always correct, roughly 10x slower.
`BlockReduceMultiply` always takes the `BigFloat` path: accumulating products
leaves the exact fixed-point band almost immediately.

**Default projection.** `DefaultProjection()` reads a
`ScopedValue{Projection}`: 4.1 ns unbound, 31 ns inside a `with_projection`
block. The convenience methods and value constructors speculate on the
untouched default (`RTE_SN`), so the overwhelmingly common path is a static,
allocation-free call — 4.1 ns for `Add(x, y)`, 3.1 ns for `F(1.35)`. Under a
bound non-`RTE_SN` projection those seams cost ~61 ns and one small allocation,
because the projection's type is not known until run time: the call crosses a
dynamic dispatch, and Julia's generic calling convention boxes its return.
A projection-typed function barrier recovers everything after that boundary
(without it the same call is 272 ns).

Three details of that barrier were each worth more than they look, and are
commented at the seam in `ops/scalar.jl`: it must not be `@inline`d; it must
match `Projection{RM,SM}` rather than `ρ::P where P<:Projection`, because an
abstract `Projection` argument *satisfies* the latter and Julia then binds
`P = Projection` and compiles the barrier away; and it must take the format
from a datum rather than from a leading `::Type{F}` argument, which alone
cost 120 ns in a dynamically dispatched call.

Where that matters, pass the projection explicitly. `Add(F, ρ, x, y)` is
1.3 ns and never reads the default at all.

Array operations resolve the default **once per call**, never per element:
a four-element `Add(A, B)` is 140 ns unbound and 178 ns bound, and the
difference does not grow with the array.

**First call.** `using AIFloats` is ~57 ms. The precompile workload covers the
standard profile's hot entries, so first calls to constructors, arithmetic,
broadcasting, and `B ∈ {4, 16, 32}` block reductions are sub-millisecond.
A block size outside that set, or an operation outside the workload, compiles
on first use.

## Deliberate limits

- **Cross-format arithmetic.** `Binary8p4se(1) + Binary8p3se(1)` does not promote
  — mixing formats is an explicit [`Convert`](@ref).
- **In-place packed arithmetic.** Packed vectors are storage; computation
  reads codes out of the bit stream, and the result is an ordinary vector.
  A packed operand is supported for unary operations only.
- **K > 16.** The grid stops at `UInt16` code units.

## Consequences

- Everything a datum can do runs through the register under an explicit or
  session-default [`Projection`](@ref) — `Add(F, ρ, x, y)`, `Add(x, y)`, or `x + y`.
- `sort` places NaN **first** (the draft's total order), not last as for `Float64`.
- The engine is verified against an independent `BigInt` reference — millions of
  compared decisions per test run, every rounding and saturation mode, plus a
  totality sweep of every operation at every carrier rung.
- Stochastic projection is reproducible: pass `R` explicitly, or a seeded `rng`.
