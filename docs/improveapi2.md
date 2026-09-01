# Review of `improveapi.md`

Review of the API simplification plan in [improveapi.md](improveapi.md), against
the tree at `e5cc4c8`. It is a strong plan — the seam design (§5) and the
self-review (§10) are genuinely good. What follows is what I would change,
heaviest first. Two items change what the plan should *say*, not merely how it
says it, and should be settled before enacting anything else: §1 and §2 below.

## 1. §9.2 sets a gate that §4.3's design cannot meet

Measured, one thread, i9-14900K, Julia 1.12.6:

| | ns | allocs |
|---|---:|---:|
| `Ref{Projection}[]` (today) | 2.50 | 0 |
| `ScopedValue{Projection}[]`, no scope active | 4.07 | 0 |
| **`ScopedValue[]` inside a `with` scope** | **34.72** | 0 |
| `Add` via Ref + speculation guard (today) | 4.07 | 0 |
| `Add` explicit ρ (floor) | 1.25 | 0 |
| **`Add` via ScopedValue + guard, inside a scope** | **272.61** | **1** |

§9.2 requires that "Repeated work inside one `with_projection` scope should not
allocate per operation." That is **not achievable as designed**. Inside a scope
the speculation guard `rho === RTE_SN` fails, `rho` is abstractly typed, and
every convenience call goes dynamic and boxes — 67x today's cost.

The cause is not `ScopedValue`. Calling `DefaultProjection!(RTZ_SF)` today has
the same effect, because the guard recognizes exactly one projection. But
`with_projection`'s entire purpose is to run many operations under a
**non-default** projection, so the plan promotes the bad case to the common
case.

Resolve one of two ways:

- extend the guard to the handful of common projections behind a function
  barrier, so a scoped `RTZ_SF` also reaches a statically typed call; or
- relax the gate to "one dynamic dispatch per public call, never per array
  element", which is achievable and still meaningful.

Do not ship both claims. Separately, the 35 ns in-scope read deserves its own
row in §9.1: it is 14x the `Ref` read the plan is replacing, and §4.3 asserts
the design without measuring it.

## 2. The alias rename that just landed moves away from the plan

Commit `7fe0dfd` ("Capitalize generated Binary format aliases") landed during
this review. The aliases are now capitalized but still denote **datum** types:

```julia
Binary8p4se <: BinaryValue   # true
Binary8p4se <: Binary        # false
```

§4.1.2 wants them to be format types, and §4.1's own rationale says leaving them
as datum types "would retain two meanings for 'format'". The capitalization made
that worse rather than better: lowercase `binary8p4se` was visually distinct
from `Binary(...)`, which signalled "a different kind of thing"; `Binary8p4se`
now asserts a kinship that the types deny.

Finish §4.1.2 or revert the capitalization. The current state is the worst of
the three options.

## 3. `F(x) isa F` would be false

§2 makes `F(1.625)` return a `BinaryValue`, so a type's constructor returns a
*different* type. Commit `88dcb04` has just removed the format-is-a-number
confusion (a format was `<: AbstractFloat`, so `isnan` of a *format* answered
`false`); making `F(x)` a datum constructor re-blurs format and datum from the
other direction.

It is legal Julia and the convenience is real, but it is surprising enough to
deserve a conscious decision rather than a table row. The alternative —
`BinaryValue(F, x)` as the only value constructor — already exists, already has
the speculation guard, and costs one word more per call site.

## 4. Internal inconsistencies

**The process-global argument is applied once.** §4.3 removes the projection
setters because a process-wide mutable default is incompatible with reliable
task-local behavior. Sixteen other process-global mutable `Ref`s survive
untouched and are absent from the §7 ownership map:

```
src/compat/show.jl      DEFAULT_SHOW_STYLE
src/ops/oracle.jl       FAST_ARITH, FAST_ENCLOSURE
src/arrays/kernels.jl   THREAD_MIN_ELEMS, THREADED_KERNELS
src/tables/policy.jl    TABLE_MAX_BITS, TABLE_EAGER_BITS, TABLE_ADAPTIVE_BITS,
                        TABLE_BUILD_ELEMS, TERNARY_EAGER_BITS,
                        TERNARY_ADAPTIVE_BITS, TERNARY_BUILD_ELEMS,
                        TERNARY_CACHE_BYTES
src/tables/cache.jl     TERNARY_TICK
src/tables/build.jl     TABLE_BUILD_MIN_ENTRIES, THREADED_TABLE_BUILDS
```

Either scope them too, or state why semantics gets scoped while display and
policy do not. `DEFAULT_SHOW_STYLE` is the weakest exclusion: it is
user-visible, mutable, and process-global, exactly the properties the plan
objects to.

**The full suite is forbidden but completion is declared.** §6 Phase 8.7 and
§8.5 both say not to run `Pkg.test()`, while §11 declares the redesign complete
for a breaking change that touches every file. Give the rationale (runtime?) and
require one full green run in §11.

**§4.1.4 breaks live doctests and a design record.** Suppressing `F()`
invalidates the `Binary` docstring's own jldoctest, which shows `B()` and
`is_signed(Binary(8, 4, UNSIGNED, FINITE)())`. It also contradicts
`structuralplan.md` §9.2a, which documents format instances as supported with a
deliberately total accessor surface. The plan updates `docs/src/*.md` but not
the design records; add `docs/structuralplan.md` and `docs/checkpoint.md` to §7.

## 5. Missing from "complete"

**Version and release notes.** The plan justifies the breakage with "while it is
at version 0.1.0" but never says to record it. Removing exported names
(`BinaryFloat` has already gone; `DefaultProjection!` and friends are next) needs
a `Project.toml` version decision and a CHANGELOG entry in §11.

**Split Phase 1.** §10 calls unsigned construction "the most dangerous change"
precisely because an unclassified old call "would continue to compile but change
meaning" — and then Phase 1 performs it in one step. Bisect it:

1. **1a** — add `fromcode` and `_rawvalue` *alongside* the existing `Unsigned`
   constructor, and migrate every internal call site. Nothing breaks; everything
   still works; the classification from Phase 0 is exercised rather than
   trusted.
2. **1b** — delete the `Unsigned` constructor. Now every missed site is a loud
   `MethodError` instead of a silent reinterpretation.

That is the whole mitigation for the plan's own top-ranked risk: it converts a
silent meaning-change into a loud failure.

## 6. Smaller points

- Add `T(codepoint(y))` explicitly to the Phase 0 inventory list (§6 Phase 0.4).
  `codepoint` returns an `Unsigned`, so that round-trip silently flips meaning
  under the new rule. No such call exists in `src/` today, but it is the pattern
  most likely to appear in user code, examples, and downstream packages.
- §4.3's comment that `ScopedValue{Projection}` needs its explicit abstract
  parameter is correct — confirmed — and worth keeping in the final source.
- `fromcode` / `codepoint` are a slightly asymmetric pair. Not worth churn, but
  worth a sentence in the docs so the asymmetry reads as deliberate.

## Method

Claims above were checked against the tree rather than read off the plan:
the `ScopedValue` table is a Chairmarks run in the `benchmark/` environment;
the alias subtyping, the surviving `Ref` inventory, and the absence of
`T(codepoint(...))` in `src/` are all greps and live evaluation at `e5cc4c8`.
