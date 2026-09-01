# Structural Plan — Giving AIFloats.jl Computational Power

*Source of algorithms: `~/github/SmallFloats.jl` (a complete, verified IEEE P3109
implementation, 8,600 lines of source, ~35M compared units in its suite).
Target structure: AIFloats.jl as it stands — `Binary{K,P,S,D}` format specifiers,
axis singletons, `Projection`, the `*Of` accessor convention, and the
directory-per-concern `src/` layout.*

*This is the reconsidered result of a drafted plan, a weakness review, and an
omissions/inconsistency review. §9 records the decisions those passes forced.
§14's four open questions have since been answered by the author; the answers are
folded in throughout and recorded in §14.*

---

## 1. Purpose

AIFloats.jl today is a complete, documented **specification layer**: it can name any
P3109 format and answer questions about it, but it cannot produce a value, encode a
code point, round a number, or add two datums. SmallFloats.jl has proven algorithms
for all of that. The goal is to bring those algorithms into AIFloats.jl **on
AIFloats' own terms**: its names, its type discipline, its directory organization —
extended where the new capability genuinely needs new structure, never overwritten
by SmallFloats' flat-file organization.

## 2. Governing principles

1. **AIFloats' structure is the frame; SmallFloats supplies algorithms.** Where the
   two disagree on organization or naming, AIFloats wins. Where SmallFloats records
   a hard-won *correctness* lesson (§8), the lesson wins regardless of spelling.
2. **`Binary{K,P,S,D}` stays exactly what it is** — a concrete singleton format
   specifier, constructed by `Binary(K,P,S,D)`, canonicalized to `Int8`/`Bool`
   parameters. It never grows a payload. SmallFloats' abstract-`Binary` +
   `Code8`/`Code16` representation split is **not** imported; the storage-width
   seam lives in the datum type's code-unit parameter instead (§4).
3. **One new core type, not a parallel hierarchy.** The datum type `BinaryValue`
   (§4) is the single structural addition at the type level. Everything else is
   functions and traits over `Binary` and `BinaryValue`.
4. **Every accessor and predicate works on both the type and an instance** — the
   promise the docs already make for `Binary` extends to every new trait, and the
   value-flavored subset extends to `BinaryValue` datums.
5. **The projection engine is the only writer of code points** (SmallFloats
   invariant 1). Every constructor-from-value, every operation, every table entry
   goes through `project`.
6. **Directory-per-concern.** New capability lands in new `src/` subdirectories or
   fills the stub files AIFloats already reserved (`content/codepoints.jl`,
   `content/datums.jl`, `content/floatvalues.jl`, `content/gentables.jl`,
   `rules/constraints.jl`).

## 3. Vocabulary translation

Fixed correspondences, applied everywhere during the port. AIFloats' column is the
one that appears in code.

| SmallFloats | AIFloats | note |
|---|---|---|
| `Binary{K,P,SGN,EXT}` (abstract) | `Binary{K,P,S,D}` (concrete) | D = "domain", same Bool sense |
| `Code8`/`Code16` reps | code-unit parameter `U` of `BinaryValue{F,U}` | §4 |
| `NearestTiesToEven` / `RNE` | `ρRTE` / `RTE` | AIFloats' existing spelling |
| `NearestTiesToAway` / `RNA` | `ρRTA` / `RTA` | |
| `TowardPositive/Negative/Zero`, `ToOdd` | `ρRTP/ρRTN/ρRTZ/ρRTO` | already aligned |
| `StochasticA{N}` … | `ρRSA{N}` … | N is **new** to AIFloats — §9.3 |
| `NearestRoundingMode` | `ToNearestRoundingMode` | AIFloats' existing abstract |
| `DirectedRoundingMode` | `UnidirectionalRoundingMode` | |
| `FaithfulRoundingMode` | `ParityRoundingMode` | |
| `ProjSpec{R,S}` | `Projection{R,S}` | already zero-size; see §9.3 |
| `roundingmode`/`saturationmode` | `RoundOf`/`SatOf` | already aligned |
| `RNE_SF` … | `RTE_SF` … | AIFloats' 27 constants keep their names |
| `issigned`/`isextended` | `is_signed`/`is_extended` | |
| `bitwidth`/`precision` | `BitwidthOf`/`PrecisionOf` | `*Of` is the public convention |
| `expbias`, `expbitwidth`, `trailingsigbits` | `ExponentBiasOf`, `ExponentBitwidthOf`, `TrailingSignificantBitsOf` | new public traits, `*Of` style |
| `MaxFiniteOf`, `MinPositiveOf`, … | same names | SmallFloats already uses the `*Of` style here |
| `codeunit_type` | `CodeType` | exists; K ≤ 8 → `UInt8`, else `UInt16` |
| `Binary8p4se` alias | `Binary8p4se` | capitalized, following Julia's convention for type names |
| `format(K,P,Σ,Δ)` | `Binary(K,P,S,D)` | already exists — the runtime route to a format; `BinaryValue(Binary(K,P,S,D))` is the runtime route to the datum type |
| `set_show_style!` styles | same | fits AIFloats' existing string/String duality |

One spelling rule throughout the port: a `Binary` type is always written via its
constructor — `Binary(8,4,SIGNED,EXTENDED)` — never as a brace literal.
`Binary(…)` canonicalizes `K`,`P` to `Int8`, so `Binary{8,4,true,true}` spelled
with `Int64` literals names a *different* (never-constructed) type. The alias
generator and every doc example use the constructor spelling.

Draft operation names (`Add`, `Multiply`, `Exp`, `Convert`, …) are P3109 vocabulary,
not SmallFloats house style — they port unchanged. The ω-prefix internals
(`ωeval`, `ωSaturate`) also port unchanged: AIFloats already uses Greek-letter
prefixes (`Σ`, `Δ`, `ρ`) as house style.

## 4. The one structural addition: the `BinaryValue` datum type

SmallFloats merges format and datum: an instance of a format type *is* a number.
AIFloats deliberately separates them — `Binary(8,4,SIGNED,FINITE)()` is a format
token. That separation is preserved and completed by introducing the datum type
`BinaryValue`, named to pair explicitly with `Binary`: the format is `Binary`, a
member of its value set is a `BinaryValue`.

```julia
struct BinaryValue{F<:Binary, U<:Unsigned} <: AbstractFloat
    code::U
    # inner constructor enforces: U === CodeType(F), high bits zero
end
```

- `F` is the `Binary` format; `U` is `CodeType(F)` (`UInt8`/`UInt16`), so the
  storage-width seam is dispatchable (`BinaryValue{F,UInt8}` vs
  `BinaryValue{F,UInt16}`) without a parallel format hierarchy. A convenience
  form fixes `U`: `BinaryValue(F)` and `BinaryValue{F}` normalize to the full
  type.
- **Representation invariant** (SmallFloats inv. 3): the code point occupies the
  low K bits; high bits are zero. Constructors check; `rawvalue` (unchecked
  internal route) assumes.
- **Code point vs value** (SmallFloats inv. 2): an `Unsigned` constructor argument
  means *code point* (range-checked against `2^K`); every other `Real` means
  *value* and goes through `project` under a `Projection`.
  `convert(::Type{BinaryValue{F}}, x)` is the value-preserving exception.
  Phasing note: the code-point constructor exists from Phase 1; the
  value constructor requires the projection engine and `Convert`, so
  `Binary8p4se(1.5)` becomes available in Phase 3 (explicit-`Projection` form and
  session-default form together — see Phase 3).
- `BinaryValue{F,U}` is concrete and `isbits` — a valid array element type. The
  invariant-8 hazard from SmallFloats (rebuilding an abstract format in a method
  body) largely disappears because AIFloats' `Binary` is already concrete; the
  residual rule is: **never spell `BinaryValue{Binary{…` in a method body** —
  propagate the received type.
- Subtyping: `BinaryValue <: AbstractFloat` directly. No new abstract root is
  needed — the `BinaryValue` UnionAll itself serves dispatch (`::BinaryValue`).
  `Binary` has no supertype at all: a format describes a value set rather than
  belonging to one (§9.2, revised).

## 5. Directory plan

```
src/
  AIFloats.jl               module root; include order (§7); exports
  types/                    (existing) format specification layer
    constants.jl            (existing) + table/budget Refs, KMAX
    external.jl             (existing)
    singletons.jl           (existing) + ρRSA{N} parameterization, isstochastic, nrandbits
    binaryformats.jl        (existing) + K ≤ 16 ceiling in validformat
    traits.jl               NEW: ExponentBiasOf, ExponentBitwidthOf, signmask,
                            codemask (_unitmask by complement), orderkeytype
    binaryvalue.jl          NEW: the BinaryValue datum type, rawvalue, codepoint
  content/                  (existing stubs → filled) the encoding's contents
    codepoints.jl           special code points: nan_code, posinf_code, neginf_code,
                            _maxfinite_code, _minfinite_code, MinPositiveOf,
                            MaxSubnormalOf, MinNormalOf, MaxFiniteOf, …
                            (code primary; values built FROM codes)
    floatvalues.jl          decode: _decode_compute, _finite_datum (bit path for
                            UInt8-width, ldexp path for UInt16-width), decodepolicy,
                            @generated constant-tuple decode tables for K ≤ 8
    datums.jl               datum-level API: decode(x), Class/FPClass, order_key
                            (NaN-first), NextGreaterThan/NextLessThan, predicates
    gentables.jl            (existing intent, completed) codetable/printcodetable —
                            human-readable enumeration of any format
  carriers/                 NEW: what holds a value in flight (function of B, not K)
    dyadic.jl               DyadicNumbers submodule, adapted to house style —
                            loads first, zero AIFloats dependencies (checkable
                            on its own terms); see §9.9 on adaptation discipline
    fma128.jl, faa128.jl    Float128 fma/faa support, adapted likewise
    heads.jl                HeadF64/HeadF128/HeadExact, rungindex, joinhead,
                            rung(F), rung(op, Fs...) = join of operand & monomial
                            bounds; carriertype; datumcarrier vs promotecarrier
    lift.jl                 lift (upward only — no narrowing method, by design)
    bigprec.jl              derived MPFR precision (never a flat constant)
  projection/               NEW: the single write path
    rounded.jl              Rounded canonical form (kind, sign, S, Q), HUGEQ,
                            the sticky ∈ {−1,0,+1} protocol
    round.jl                round_to_precision: _rtp_core (generic), _rtp_f64
                            (bit path), _rtp_dyadic (fixed-point family), the two
                            predicate families (_roundaway / _rab), _codeiseven
                            (P==1 → parity of biased exponent)
    saturate.jl             ωSaturate — outcome currency is a CODE POINT;
                            SF/SP/SN rows; (Q,S)-lexicographic range test
    project.jl              project pipeline; project_interval (Ziv loop with
                            derived cap max(4096, bigprec(F)+64))
  ops/                      NEW: operations
    registry.jl             OP_REGISTRY (name, arity, group, factors);
                            opfactors as Val-dispatched trait
    protocol.jl             result protocol: BigExactF, StickyF, EncloseF,
                            Enclose128F; _finish resolution ladder
    oracle.jl               the ωeval catalog: Group A error-free transforms with
                            derived _de_* thresholds, exact selections (parametric
                            in carrier), enclosure ladder for Group B, quotient
                            fma-exactness proofs, π-scaled trig with Niven peeling
    scalar.jl               apply_op, generated spec-register methods, _drawR,
                            Convert methods
  tables/                   NEW: memoized evaluation
    cache.jl                TableKey; two caches by code unit (dispatch, no branch);
                            lock protocol; ternary LRU
    policy.jl               the two budgets (bytes-as-bits vs entries), table_for
                            vs get_table, table_policy introspection
    build.jl                builders with Val(op) function barrier; threaded fill
  arrays/                   NEW: array surface
    kernels.jl              vmap/vmap!; Shape A (gather) vs Shape B (compute);
                            hoisted table getter; sequential stochastic kernel
    blocks.jl               Block/BlockVector, blockdecode (P==1 ldexp fast path),
                            blockproject cascade, reductions with derived
                            accumulator precision, ConvertToBlockMaxAbsFinite
    packed.jl               PackedVector sub-byte packing
    broadcast.jl            copyto! hook routing veneer broadcasts to vmap!
                            (loaded after compat/base.jl — reads its tables)
  compat/                   NEW: Julia surface
    base.jl                 Base veneers from the registry; AbstractFloat contract
                            (decompose, eps, ldexp, round-family); refusals that
                            say why; NaN-first isless + CodeCountingSort;
                            promote_rule → promotecarrier; similar/reinterpret
    show.jl                 four show styles (:value default, :codepoint, :datum,
                            :typed) — extends AIFloats' existing display layer
    rand.jl                 rand (RTZ_SN default) / randn (RTE_SF, signed only)
  rules/                    (existing empty dir → filled) policy & governance
    constraints.jl          (promised by the commented include) the format grid:
                            KMIN/KMAX walk, alias generation (Binary⟨K⟩p⟨P⟩…),
                            opt-in Formats submodule. Validity itself stays in
                            validformat (types/binaryformats.jl) — one validator,
                            one place
    defaults.jl             session defaults (plain Refs; coupled projection
                            setters; speculation-guard consumption pattern)
    conformance.jl          conformance declaration derived live from the registry
    approx.jl               κ registry (register_approx!, measured-not-promised)
```

Existing `types/` files change minimally; existing docs/tests keep passing at every
phase boundary.

## 6. Layer notes — what is harvested and what is adapted

**types/**: `validformat` gains `K <= 16` (§9.4). `singletons.jl` parameterizes the
three stochastic structs as `ρRSA{N}` etc. with `1 ≤ N ≤ 60` checked in an inner
constructor; existing constants stay valid via `const RSA = ρRSA{8}()` (§9.3).
`traits.jl` adds the exponent formulas — `B = 2^(K−P−1)` signed, `2^(K−P)`
unsigned; `w = (K − S) − (P − 1)` — and the mask primitive built **by complement**
(`typemax(U) >> (8sizeof(U) − K)`), never by `1 << K`.

**content/**: fills the stubs with SmallFloats' encoding layout: zero at code 0
(single zero — decode drops the sign when the significand is 0); the single NaN at
the would-be −0 slot (`signmask`) for signed formats, at the top code for unsigned
(**NaN tested first in decode** — it aliases the −Inf slot for unsigned); +Inf
immediately below NaN when EXTENDED. Decode's core: strip sign, split
`tsig`/`Eb`, `e = (max(Eb,1)) − B + 1 − P`, subnormal and lowest-normal binade
sharing one grid exponent. Encode from canonical `(sign, S, Q)` with the
`S == 2^P` carry. `gentables.jl` is completed with these as its substance — the
file's original promise.

**carriers/**: the rung criterion is a function of **exponent bias, not bitwidth**:
`_rungindex_span(2B)` with boundaries 1024/16384 → Float64/Float128/Dyadic.
Per-operation rung is the **join** of the operand bound and the monomial bound
(`opfactors(op) · maxB`); omitting the operand bound is the recorded subtle error.
`Dyadic` remains an isolated submodule (its zero-dependency load constraint is
part of the design), adapted to house style under the §9.9 discipline. Two
carrier traits stay distinct:
`datumcarrier` (internal; may be `Dyadic`, which is `Real` but not
`AbstractFloat`, `float(::Dyadic)` deliberately undefined) and `promotecarrier`
(public; always a real Julia float).

**projection/**: ports the engine whole. Key algorithmic anchors: grid exponent
`Q = max(e, 1−B) − P + 1`; the sticky step-down block (identical in all three
carrier paths, and they must agree); RTE ties to the even **code point** — for
P == 1 that is parity of the biased exponent; RTO reuses the same predicate
inverted; the three stochastic predicates on an N-bit sub-grid; saturation as a
code-point-valued function with the (Q, then S) lexicographic range test; and the
Ziv interval loop whose soundness is "projection is monotone in the value at fixed
R", with a **derived** precision cap.

**ops/**: `OP_REGISTRY` is the single source (SmallFloats inv. 7) from which the
scalar methods, Base veneers, array surface, Block/Scaled variants, table
enumeration, and conformance are generated — no hand-written per-op variants. The
`factors` column drives carrier width (too low ⇒ silent overflow, not an error).
The result protocol (`Float64/Float128/Dyadic` exact; `BigExactF` deferred-exact;
`StickyF` head+direction; `EncloseF`/`Enclose128F` staged enclosures) and the
`_finish` ladder port as designed — the sticky-directed two-endpoint projection is
the universal correct-rounding decision procedure for every mode including
stochastic. All `_de_*` exactness thresholds and `bigprec` are **derived from
operands**, never literals (§8.6). Two measured performance lessons carry over
verbatim: the wide `apply_op` method takes a **typed** `Vararg{Any,N}` (the
untyped splat lowers to a dynamic apply and boxes 304–592 B per call), and the
Float64 fast path keeps an **explicit `res isa Float64` union split** before the
`@noinline` slow finisher (measured 399 → 269 ns/element) — the speculation guard
in the convenience methods is spelled inline rather than passed as a closure for
the same reason.

**tables/**: two budgets with different failure modes — memory (log2 bytes,
compared in bits so `1 << ΣK` never overflows) and build time (entry count).
Stochastic ρ is never tabulable (a distribution, not a value) and builders reject
it loudly. A table entry IS the defined result: built by one trip through the same
scalar path Shape B runs per element. `Val(op)` passes as an *argument* into the
fill functions (the 13× function-barrier lesson).

**arrays/**: `vmap!` hoists the `@noinline` table getter out of the loop; the
stochastic kernel is a separate *function* (sequential by construction — seeded
reproducibility must not depend on the scheduler). Blocks: shared-scale MX shape,
`blockdecode` on the **joint** rung of scale and element formats, P == 1 scale as
an exponent add, reduction accumulator precision derived from the formats.

**compat/**: NaN-first total order (`order_key` with NaN at key 0; key type must
widen — `UInt32` for 16-bit formats), `sort` places NaN in front — a deliberate,
documented divergence from Base convention. Same-format-only Base operators
(cross-format arithmetic is an explicit `Convert`). Refusals name their reason
(`rem`/`mod`/`Rational` inputs refuse rather than round outside `project`).

**rules/**: session defaults use the coupled-setter/speculation-guard pattern; the
alias grid defines all 504 capitalized names, exports only the K ≤ 8 subset (120)
with the rest reachable qualified or via an opt-in `AIFloats.Formats` submodule —
exporting more later is non-breaking, un-exporting is not.

## 7. Load order (load-bearing; stated only here and in the module root)

```
carriers/dyadic.jl            first, zero package dependencies
carriers/fma128.jl, faa128.jl
types/constants.jl → types/external.jl → types/singletons.jl
  → types/binaryformats.jl → types/traits.jl
carriers/heads.jl             (before binaryvalue.jl: decode needs datumcarrier;
                               lift, CarrierValue, promotecarrier live here)
types/binaryvalue.jl
content/codepoints.jl → compat/show.jl (early: error paths may print)
  → content/floatvalues.jl → content/datums.jl
carriers/bigprec.jl
projection/rounded.jl → projection/round.jl → projection/saturate.jl
  → projection/project.jl
rules/constraints.jl → rules/defaults.jl   (before ops: the generated
  same-format methods read the defaults' guard constants)
ops/registry.jl (also rung(op, Fs...)) → ops/oracle.jl → ops/scalar.jl
tables/cache.jl → tables/policy.jl → tables/build.jl
arrays/kernels.jl → arrays/blocks.jl → arrays/packed.jl
compat/base.jl → arrays/broadcast.jl → compat/rand.jl
  (broadcast.jl builds its veneer table from compat/base.jl's _BASE_UNARY /
   _BASE_BINARY, so it CANNOT sit with the other arrays/ files)
content/gentables.jl
rules/conformance.jl → rules/approx.jl
precompile workload (module root)
```

`carriers/lift.jl` and `ops/protocol.jl` from the draft plan did not become
files: `lift` lives in `heads.jl` (it is four one-line methods on the head
tags) and the result protocol is `Sticky`/`Enclosure` in `ops/oracle.jl`.
Changing the order means changing this section in the same commit.

## 8. Correctness invariants carried over (the ledger)

Each of these is a recorded SmallFloats failure and its rule. They are review
criteria for every phase, spelled here once.

1. **One write path.** `project` is the only producer of a code point.
2. **Unsigned argument = code point; other Real = value.** `convert` is the
   value-preserving exception.
3. **Representation invariant** checked in constructors, assumed by `rawvalue`.
4. **Stochastic ρ is never tabulable.**
5. **A table entry IS the defined result** — one trip through the scalar path.
6. **No flat "wide-enough" constants.** Every threshold (`_de_*`, `bigprec`,
   interval caps, exactness screens) is derived from operands or formats. Every
   flat constant in SmallFloats' history was ample at K ≤ 8 and silently wrong
   later, always in the direction no test could see.
7. **Policy is dispatch, never a branch** — traits behind `Val`, one concrete
   return type per method; no trait returns a Type from a ternary.
8. **Masks by complement**; the K == storage-width case is structural.
9. **The code point is primary**; extremal values are built from extremal codes.
10. **`lift` upward only** — the absent narrowing method is the safety property.
11. **Checked/unchecked are two named functions**, never `@boundscheck`.
12. **Refuse rather than silently round** outside the write path, and refusals
    say why, as methods that throw (not missing methods — JET-cleanliness).
13. **No construct materializes `2^ΣK` elements without a byte budget**, compared
    in bits.
14. **Julia ≥ 1.12 is a correctness floor** (ScopedValue-backed
    `setprecision`/`setrounding` make threaded table builds sound). AIFloats'
    compat already says 1.12.

## 9. Decisions forced by the review passes

**9.1 Datum type, not merged format-datum.** First draft imported SmallFloats'
abstract-format/concrete-representation split; review rejected it as forcing
SmallFloats' structure. `BinaryValue{F,U}` keeps AIFloats' format/datum separation
and is simpler (no abstract-rebuild hazard).

**9.2 `Binary <: BinaryFloat <: AbstractFloat` — REVISED, 2026-09-01.** The
original decision was to keep it: re-parenting the format token out of
`AbstractFloat` "breaks documented API for zero computational gain", to be
revisited "only if method ambiguities actually materialize".

The gain turned out not to be computational, which is why that framing missed
it. While a format was an `AbstractFloat`, Base's numeric fallbacks applied to
format instances, and `isnan(Binary{8,4,SIGNED,EXTENDED}())` returned **`false`**
— a confident answer to a meaningless question — because the generic method is
`x != x`. The hierarchy also contradicted its own names: the format specifier
was a subtype of something called `BinaryFloat`, while `BinaryValue`, the actual
number, was not.

`Binary` now has no supertype and `BinaryValue <: AbstractFloat` as before. The
predicted cost did not appear either: `BinaryFloat` had no uses as a bound
anywhere in `src/` or `test/`, so nothing propagated, no test changed, and the
benchmark suite was unmoved. The API break is the removal of the exported name
`BinaryFloat`, which named the wrong thing and was otherwise inert.

**9.2a Type-canonical vs value-canonical, and the bridge rule (2026-09-01).**
Two opposite conventions live in the package, and both are right:

- A **format is a TYPE**. `Binary(K,P,S,D)` returns `Binary{K,P,S,D}`, not an
  instance, because the format has to be `BinaryValue{F,U}`'s first parameter.
- A **projection component is a VALUE**. `SIGNED`, `RTE`, `SN`, `RTE_SN` are
  constants passed as runtime arguments; their types surface only where
  dispatch or tabulability needs them. `isstochastic` answering for both a
  value and a type is deliberate — table policy asks the question of
  `Type{Projection{R,S}}` — and is not a licence to double every other
  signature.

Formats are nonetheless instantiable, and every format accessor accepts an
instance. That must stay total. A PARTIAL instance surface is worse than either
extreme, because the missing method is discovered as a `MethodError` and
"fixed" by writing the bridge, and the obvious bridge is an infinite recursion:

```julia
BinaryValue(fmt::Binary, code) = BinaryValue(fmt, code)              # StackOverflowError
BinaryValue(fmt::Binary, code) = BinaryValue(some_identity(fmt), c)  # StackOverflowError
```

Julia cannot warn about either: the signature legitimately matches itself, so
it is a `StackOverflowError` rather than an ambiguity.

> **Rule.** An instance-form method must change its argument's KIND, not merely
> its value: `f(x::T) = f(typeof(x))`. Never delegate through anything that
> hands back the same kind you were given.

`test-binary-format.jl` asserts the surface is total in both directions — which
is how the missing `validformat(::Type{Binary{...}})` was found, the mirror of
the missing `BinaryValue(::Binary, code)`.

**9.3 Stochastic N without breaking the 27 constants.** `ρRSA{N}` etc. carry N in
the type (tabulability and randomness budget must be static). The existing
`RSA`, `RSA_SF`, … remain **instances** at the default N = 8, so all current
exports and docs stay valid; other budgets via `ρRSA(N)`/`Projection(ρRSA(n), SF)`.
AIFloats' existing `Projection{R,S}` (zero-size, singleton fields) already gives
full specialization — no `ProjSpec` import needed.

**9.4 K ≤ 16 ceiling.** `validformat` currently has no upper bound, but
`CodeType` stops at `UInt16` and every ported algorithm is verified on 3..16.
The ceiling is honest scope, enforced in **one place** — `validformat`
(types/binaryformats.jl), which every constructor already routes through;
`rules/constraints.jl` only *walks* the KMIN..KMAX grid it implies. Lifted only
with new storage and new verification.

**9.5 `ValueType` disposition.** `ValueType(K)` stays as the *exact-representation*
storage trait and its documented ladder is correct for K ≤ 10; for K ≤ 16 it
answers `Float128`, which represents every datum **except** those of the eight
formats with B > 16384 — for those the honest answer is that no fixed-width float
suffices, and `datumcarrier` (new, B-derived) answers `Dyadic`. `ValueType`'s
docstring gains that caveat; internal code uses `datumcarrier`, never `ValueType`,
for evaluation decisions.

**9.6 Aliases capitalized, narrow export.** `Binary8p4se` follows Julia's type-name
convention; all 504 are defined and the 120 with K ≤ 8 are exported. The
distinct IEEE aliases `binary16`/`binary32`/`binary64`/`binary128` remain lowercase.

**9.7 Naming translations are total** (§3) — no SmallFloats spelling survives in
AIFloats' public surface; ω-internals and draft op names pass through.

**9.8 The independent oracle ports early, not late.** SmallFloats'
`refimpl.jl`-style `Rational{BigInt}` reference (a P3109 datum *is* a dyadic
rational; comparisons are decisions, not estimates) is the acceptance gate for the
projection engine, so it lands with Phase 2, before any operation exists.

**9.9 Adapted vendoring, protected by differential tests.** The three support
files (`dyadic.jl`, `fma128.jl`, `faa128.jl`) are copied and **restyled to
AIFloats conventions during the port** (author's choice, §14.4) rather than kept
verbatim. That trades diffability against the verified originals for house-style
consistency, so the trade is paid for explicitly: each adapted file carries a
provenance header (source repo, commit, date), and Phase 2's gate includes a
differential testset asserting the adapted `Dyadic` produces results identical to
SmallFloats' original over the exhaustive kernel-band sweeps (the same G7-style
"the retired implementation is the oracle for its replacement" discipline
SmallFloats used when Dyadic replaced BigFloat). Because SmallFloats is
unregistered, it cannot be a test dependency: the comparison runs against
**checked-in golden digests** captured once from SmallFloats' `Dyadic` by a
`test/support/` capture script (kept in-repo so the capture is reproducible on a
machine that has SmallFloats). Restyle means renames, comment style, and AIFloats
naming — never algorithmic "improvements" in the same commit as the port.

## 10. Phases and gates

Each phase ends with: full test suite green, docs build green,
`docs/src/50-status.md` updated to tell the truth.

**Phase 0 — groundwork** (types/, rules/constraints.jl)
K ≤ 16 ceiling; `ρRSA{N}`; `traits.jl` (bias, exponent width, masks, order-key
type); `isstochastic`/`nrandbits`. *Gate:* existing 456 tests still pass; new
trait tests exhaustive over all 504 formats.

**Phase 1 — datum and codec** (types/binaryvalue.jl, content/)
`BinaryValue`; special code points; decode (compute + K ≤ 8 tables); encode from
canonical form; `gentables.jl` completed; show styles for datums. *Gate:*
encode∘decode round-trip exhaustive over every code point of all 504 formats
(7.6M); value tables for small formats checked against independently hand-derived
P3109 tables.

**Phase 2 — projection engine** (carriers/, projection/)
Dyadic + heads + lift + bigprec; Rounded/sticky; the two rounding-predicate
families; saturate; project; project_interval. *Gate:* the ported
`Rational{BigInt}` oracle — rounding sweep exhaustive over (P,B) cells for all
deterministic and stochastic modes; saturation sweep over (P,B,S,D); the
fixed-point family bit-identical to the generic family.

**Phase 3 — operations** (ops/, rules/defaults.jl)
Registry; result protocol; oracle catalog in three cuts: (a) `Convert` + exact
selections + Group A arithmetic, (b) quotient family, (c) Group B enclosures with
the π-scaled specials. `rules/defaults.jl` lands **here**, not Phase 5: the
generated same-format convenience methods and the value constructor's
default-projection form both consume it. `Convert` unlocks value construction —
`BinaryValue{F}(x::Real)` with explicit and defaulted `Projection` — hence
`compat/rand.jl` can land at the end of this phase. *Gate:* exhaustive comparison
against the rational oracle for unary/binary ops at K ≤ 8; a G10-style totality
sweep (every registry op returns, at every rung, with the declared type) over
rung representatives.

**Phase 4 — tables and kernels** (tables/, arrays/kernels.jl)
*Gate:* Shape A ≡ Shape B measured, not assumed; budget refusals tested; zero
warm-path allocation pinned as a deterministic regression.

**Phase 5 — Julia surface** (compat/base.jl)
Base veneers, ordering, promotion, counting sort. *Gate:* Aqua + JET clean;
NaN-first ordering pinned; specialization/inference pins at the public entry
points.

**Phase 6 — blocks and packed** (arrays/blocks.jl, arrays/packed.jl)
*Gate:* block surface enumerated by (FS, FE) shape; packed round-trip exhaustive.

**Phase 7 — governance** (rules/conformance.jl, rules/approx.jl, precompile
workload) *Gate:* conformance report derives from the registry live; κ
registration rejects understatement.

Phases 0–2 are the critical path and deliver the capability the docs' status page
lists as missing first: values, code points, projection. Phases 3+ are separable.

## 11. Testing plan

AIFloats' runner auto-includes `test-*.jl` into titled testsets — keep it. New
files per phase: `test-traits.jl`, `test-binaryvalue.jl`, `test-codec.jl`,
`test-projection.jl`, `test-ops.jl`, `test-tables.jl`, `test-kernels.jl`,
`test-compat.jl`, `test-blocks.jl`. Support code that is not itself a testset
(the rational oracle, format-representative selection) lives in `test/support/`,
included explicitly. Two doctrines carried from SmallFloats: **enumerate rather
than sample wherever affordable, and say "sampled" out loud where not**; and
tests that compare two answers are complemented by one broad totality sweep,
because deep gates are silent about paths that throw.

## 12. Documentation plan

Each phase updates `50-status.md` (the honesty page) and extends the docstring
surface (the `@autodocs` reference page picks it up). New user pages when the
capability exists: values/codec page after Phase 1, projection-behavior page after
Phase 2 (the current `40-projections.md` documents names only and says so),
operations page after Phase 3. The README's scope caveat shrinks as phases land.

## 13. Initially out of scope

- K > 16, and any storage unit beyond `UInt16`.
- In-place packed arithmetic; cross-format implicit promotion; iteration/range
  protocol for datums (all deliberate SmallFloats limitations, adopted).
- The full 14-gate/roll-call test governance apparatus — its *doctrines* are
  adopted (§11); its machinery is scaled to this package's size and can grow.
- Benchmark harness (adopt SmallFloats' benchmark doctrine when performance work
  starts, not before).

## 14. Formerly open questions — answered by the author

1. **Datum type name: `BinaryValue`.** Pairs explicitly with `Binary`: the format
   is `Binary`, a member of its value set is a `BinaryValue`. (`AIFloat` and
   `Datum` were considered and declined.)
2. **The 504 capitalized aliases name the datum type**:
   `Binary8p4se === BinaryValue{Binary(8,4,SIGNED,EXTENDED), UInt8}` (constructor
   spelling — see §3's canonical-parameters rule). So `Binary8p4se(1.5)`
   constructs a value and `Vector{Binary8p4se}` is a concrete array — mirroring
   how `binary16 === Float16` already works. The format is reached via
   `Binary(8,4,SIGNED,EXTENDED)` or from the alias by its `F` parameter.
3. **Show-style default is `:value`** — a datum prints as the number it denotes;
   `:typed` is the documentation-rendering convention, established by the docs
   harness rather than by the default.
4. **Vendored files are adapted during the port**, not copied verbatim — restyled
   to AIFloats conventions with provenance headers, protected by the differential
   testing discipline of §9.9.
