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
| **Enumeration** | [`codetable`](@ref), [`printcodetable`](@ref); the 504 lowercase aliases (`binary8p4se`), K ≤ 8 exported, the rest via `AIFloats.Formats` |
| **Total order** | NaN-first order keys, [`Class`](@ref)/[`FPClass`](@ref), [`NextGreaterThan`](@ref)/[`NextLessThan`](@ref) |
| **Datum display** | four styles — `:value` (default), `:codepoint`, `:datum`, `:typed` — via [`set_show_style!`](@ref) |
| Projection vocabulary | 9 rounding modes (stochastic ones carry their random-bit budget `N`; [`isstochastic`](@ref), [`nrandbits`](@ref)), 3 saturation modes, [`Projection`](@ref) and its 27 constants |
| **Projection behavior** | [`project`](@ref) — the single write path: round to precision → saturate → encode, for every rounding mode (sticky protocol, stochastic at fixed `R`) and all three saturation modes, from `Float64`/`Float128`/`BigFloat`; the interval oracle `AIFloats.project_interval` |
| **Operations** | the draft register — `Add`, `Subtract`, `Multiply`, `Divide`, `FMA`, `FAA`, `Sqrt`, `Exp`, `Log`, the trig/hyperbolic families and their π-scaled forms, `Hypot`, `Clamp`, the extremum family — correctly rounded via exact evaluation or interval enclosure; [`Convert`](@ref) from datums, floats, and integers |
| **Value construction** | `binary8p4se(1.5)` (via `Convert` under the session default or an explicit `projection` keyword) |
| **Session defaults** | [`DefaultProjection`](@ref) and its coupled component setters |
| **Random datums** | `rand` (default `RTZ_SN`, provably `< 1`) and `randn` (default `RTE_SF`, tails clamp; signed formats only) |
| **Array kernels** | every register op elementwise over arrays — `Add(F, ρ, A, B)`, `Exp(A)` — via `vmap`/`vmap!`; pure projections gather from a memoized table when policy grants one, otherwise compute per element (same answer either way); stochastic projections run a sequential, seeded-reproducible loop |
| **Tables** | memoized result tables per `(op, formats, projection)`: `AIFloats.get_table`, `AIFloats.table_for`, `AIFloats.table_policy` introspection, byte and build-time budgets that refuse loudly, ternary eager/adaptive bands with LRU eviction |
| **Base surface** | same-format `+ - * /`, `abs`, `sqrt`, `exp`, `log`, the trig/hyperbolic families, `hypot`, `copysign`, `max`/`min` (NaN-propagating), `fma`/`muladd`, `clamp` — each one register call under the session default; `Op(ρ, x)` projection-first convenience; comparison (`==`/`<` unordered on NaN), `isless`/`sort` in the draft's **NaN-first** total order (a counting sort, `AIFloats.CodeCountingSort`); `hash`/`Dict`/`Set` via `Base.decompose` |
| **AbstractFloat contract** | `zero`/`one`/`eps`/`typemin`/`typemax`/`floatmin`/`floatmax`/`precision`; `exponent`/`significand`/`frexp`/`ldexp`; `round`/`floor`/`ceil`/`trunc` and `round(x, RoundUp)` etc. as one projection each; `nextfloat`/`prevfloat` (off-lattice into NaN) |
| **Conversion & promotion** | `Float64`/`Float32`/`Float16`/`BFloat16`/`Float128`/`BigFloat`/`Int(x)`; `convert` (value semantics, `Unsigned` included); `x + 1.0` promotes to the format's public carrier `AIFloats.promotecarrier` — `Float64`, `Float128`, or `BigFloat` by exponent bias; `similar` keeps element types concrete; `reinterpret` checks the representation invariant |
| **Stated refusals** | `rem`/`mod`, `round(x, RoundNearestTiesUp)`/`RoundFromZero`, `Rational` inputs — each throws an `ArgumentError` that says why, never a bare `MethodError` |
| **Blocks** (draft §5) | [`Block`](@ref) `(scale, elements)`; `BlockOp`/`ScaledOp` for every register op (`BlockAdd(FR, ρ, b1, b2, sr)`, `ScaledAdd(FR, ρ, s1, x1, s2, x2)`), the reductions [`BlockReduceAdd`](@ref)/[`BlockReduceMultiply`](@ref)/[`BlockDotProduct`](@ref) with exact accumulators at derived precision, the conversions [`ConvertFromBlock`](@ref)/[`ConvertToBlock`](@ref)/[`ConvertToBlockMaxAbsFinite`](@ref); [`BlockVector`](@ref) structure-of-arrays storage |
| **Packed storage** | [`PackedVector`](@ref) — code points at `K` bits per element in 64-bit words; kernels run unpack → compute → emit (`AIFloats.vmap(op, F, ρ, pv)`); [`packing_saves`](@ref) |
| **Performance layers** | the Float64 bit path and the Dyadic fixed-point path of `round_to_precision`, pinned bit-identical to the generic core (35M comparisons); Float128 exactness proofs and the `Sticky` wide-spread escape for Group A; eager Float64/Float128 envelope stages before the MPFR ladder for every enclosure — each switchable (`AIFloats.FAST_ARITH`, `AIFloats.FAST_ENCLOSURE`) and pinned equal to the rigorous path; the `Dyadic` carrier is verified against golden digests captured from SmallFloats' original; pure-Julia `fma128`/`faa128` for `Float128` |
| **Governance** | [`conformance`](@ref) — the draft-§4.6 declaration derived live from the registry, the table cache, and the κ registry ([`conformance_report`](@ref), [`conformance_dict`](@ref)); [`register_approx!`](@ref)/[`measure_kappa`](@ref) — κ measured by enumeration, understatement rejected; [`ftz_variant`](@ref), the Annex's worked example; [`draft_identity`](@ref) with the retained transliteration's digest |
| IEEE 754 aliases | [`binary16`](@ref), [`binary32`](@ref), [`binary64`](@ref), [`binary128`](@ref), [`bfloat16`](@ref) |

Every accessor and predicate works on the `Binary` type, a `Binary` instance, the
`BinaryValue` datum type, and a datum.

## Deliberate limits

- **Cross-format arithmetic.** `binary8p4se(1) + binary8p3se(1)` does not promote
  — mixing formats is an explicit [`Convert`](@ref).
- **In-place packed arithmetic.** Packed vectors are storage; computation
  unpacks tile by tile.
- **K > 16.** The grid stops at `UInt16` code units.

## Consequences

- Everything a datum can do runs through the register under an explicit or
  session-default [`Projection`](@ref) — `Add(F, ρ, x, y)`, `Add(x, y)`, or `x + y`.
- `sort` places NaN **first** (the draft's total order), not last as for `Float64`.
- The engine is verified against an independent `BigInt` reference — millions of
  compared decisions per test run, every rounding and saturation mode, plus a
  totality sweep of every operation at every carrier rung.
- Stochastic projection is reproducible: pass `R` explicitly, or a seeded `rng`.
