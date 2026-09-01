# API simplification and consistency plan

*Revision 3 applies the findings in `docs/improveapi2.md` to
`docs/improveapi.md`, incorporates the four decisions recorded below, and
corrects the unsigned-migration failure-mode assumption discovered during the
application review.*

## 1. Decision

AIFloats should make one clean, breaking API change from `0.1.0` to `0.2.0`:

> **Formats are types, datum constructors always consume values, raw code
> points use a named constructor, and projection defaults are task-local.**

This plan deliberately does **not** preserve compatibility scaffolding. There
will be no format-instance forwarding methods, legacy unsigned-constructor
branch, deprecation wrappers, dual global/task default system, or transitional
alias registry. The repository, tests, benchmarks, precompile workload, and
documentation will be migrated together, after which the superseded methods
will be deleted.

The implementation may temporarily add `fromcode`, migrate callers, and
install an unsigned-construction diagnostic trap before enabling the new value
meaning. That is a local sequencing technique, not maintained compatibility:
no commit, release, or final interface retains the old meaning or the trap.

The result should be a deeper API: a small interface with one meaning per
operation, while representation checks, projection policy, table machinery,
and storage invariants remain behind narrow module seams.

Four decisions from the review of this plan are settled here:

1. `F(x)` remains a datum constructor, and its deliberately nonstandard return
   relationship is documented and tested.
2. Scoped convenience calls use a projection-type function barrier, accept one
   dynamic dispatch, and must not allocate per scalar call.
3. Performance-policy controls remain process-wide because that is faster;
   only the numerically semantic projection default is task-local.
4. The breaking interface is released as `0.2.0` with release notes.

## 2. Target surface

The following example is the intended end state.

```julia
using AIFloats

# A named format is a Binary type.
F = Binary8p4sf
@assert F === Binary(8, 4, SIGNED, FINITE)

# Its concrete AbstractFloat datum type is explicit when a type is needed.
T = BinaryValue(F)

# All ordinary constructors consume numeric values, including Unsigned values.
x = F(1.625)
y = T(UInt8(3))                    # numeric value 3, not code point 3
z = BinaryValue(F, 1.625)

# A code point is intentionally named and checked.
c = fromcode(F, 0x45)
@assert c === fromcode(T, 0x45)
@assert codepoint(c) == 0x45

# A dynamic projection default is confined to this task scope.
with_projection(RTZ_SN) do
    @assert F(1.7) === project(F, RTZ_SN, 1.7)
end

# Explicit projection remains the performance-oriented, context-free form.
w = Convert(F, RTE_SN, 1.7)
```

The central distinctions are:

| Concept | Canonical spelling | Meaning |
|---|---|---|
| format | `F = Binary(K, P, S, D)` or `Binary8p4sf` | a `Type{<:Binary}`; never an instance |
| datum type | `T = BinaryValue(F)` | the concrete `AbstractFloat` type `BinaryValue{F,CodeType(F)}` |
| value construction | `F(x)`, `T(x)`, or `BinaryValue(F, x)` | project numeric value `x` once |
| checked code construction | `fromcode(F, code)` or `fromcode(T, code)` | validate and preserve the code point |
| unchecked internal construction | `_rawvalue(F, code)` | trust a canonical code unit and invariant |
| explicit operation | `Add(F, rho, x, y)` | no ambient-policy lookup |
| scoped operation | `with_projection(rho) do ... end` | task-local default for convenience calls |

`reinterpret(T, code)` may remain a Base-compatible bit-level operation, but
it is not the ordinary AIFloats constructor and must enforce the same bit-width
invariant as `fromcode`.

`fromcode` and `codepoint` are intentionally not grammatical inverses:
`codepoint(x)` follows Base's established noun-style query, while `fromcode`
names the potentially invariant-bearing construction action. The guaranteed
round trip is `fromcode(typeof(x), codepoint(x)) === x`.

## 3. Requested recommendations and their realization

| Requested item | Realization |
|---|---|
| most valuable simplification | the target surface and four invariants above |
| 1. canonical format spelling | format types only; named `Binary...` constants also name format types |
| 2. value-based numeric construction | every `Real`, including every `Unsigned`, is a value in ordinary constructors |
| 3. format constructs a datum | `F(x; projection, rng, R)` returns `BinaryValue(F)` |
| 4. task-local projection | `Base.ScopedValues.ScopedValue` plus `with_projection` |
| 6. scalar/array `Convert` parity | one accepted-source policy and one scalar conversion kernel used by arrays |
| 7. coherent cache introspection | `table_stats`, `table_entries`, `table_policy`, and `empty_tables!`; cache objects stay internal |
| 8. packed serialization | checked `packedfromwords`/`packedfrombytes` and copying `packedwords`/`packedbytes` |
| 9. normalized errors | a documented exception matrix enforced at public seams |
| 10. idiomatic queries | lowercase query bindings plus `formatinfo` |
| lower: container consistency | `copy`, `similar`, `copyto!`, construction, and conversion contracts for packed/block vectors |
| lower: deterministic introspection | sorted registry, cache-entry, conformance, and format listings |
| lower: registry validation | validate operation existence and arity before converting a runtime symbol to `Val` |
| lower: checked/raw separation | checked public constructors and `_raw...` implementation routes for every invariant-bearing representation |
| lower: compact format summary | stable `formatinfo(F)` named tuple |

Recommendation 5, a broader redesign of stochastic argument spelling, is not
part of this work. Existing `rng` and `R` behavior remains intact except where
the constructor and scalar/array consistency work necessarily shares its
implementation. Correct rounding and the explicit refusal of unsupported
inputs remain correctness constraints.

## 4. Governing invariants

### 4.1 Formats are type-level information

1. `Binary(K, P, S, D)` returns a concrete `Binary{K,P,S,D}` type.
2. `_NAMED[:Binary8p4sf]` and the public constant `Binary8p4sf` contain that
   format type, not its `BinaryValue` type.
3. No public method accepts `f::Binary`, and `BinarySpecifier` and
   `_formattype` are removed.
4. `F()` does not create a zero-field token. Give it a direct, helpful error
   explaining that `F` is already the format and that `F(x)` constructs a
   datum. The `Binary` definition must explicitly suppress its generated
   zero-argument constructor.
5. Internal dispatch specializes on `::Type{F} where F<:Binary`; no runtime
   normalization branch is needed on hot paths.

Changing the named aliases is important. Leaving `Binary8p4sf` as a datum type
would retain two meanings for “format”: constructed `Binary` values would name
format types while the standard names would name `AbstractFloat` types. Making
the aliases actual format types removes that mismatch, and `F(x)` preserves
their convenient constructor role.

The capitalization change already in the tree makes completing this step more
important: a capitalized `Binary8p4sf` visually claims to be the same kind of
thing as `Binary(...)`. The final type relationship must make that claim true:
`Binary8p4sf <: Binary`, while `BinaryValue(Binary8p4sf) <: AbstractFloat`.

### 4.2 Constructors have one semantic axis

1. `F(x::Real)`, `T(x::Real)`, and `BinaryValue(F, x::Real)` all mean numeric
   conversion under a projection.
2. `Unsigned` is not special. `T(UInt8(3))` represents numeric three if that is
   representable; it does not select code point three.
3. `fromcode(F, code::Integer)` and `fromcode(T, code::Integer)` are the checked
   code paths. They reject negative values and values above `codemask(F)` with
   `ArgumentError`, then return the canonical datum type.
4. `fromcode` accepts integer widths independently of `CodeType(F)` and narrows
   only after the range check. This makes `fromcode(F, UInt16(3))` safe for an
   eight-bit format without silently truncating.
5. `_rawvalue(F, code::CodeType(F))` is the internal fast path. It performs no
   range check and is never exported or declared `public`.
6. All table builders, decoding loops, packed extraction, special-value
   accessors, and internal codecs use `_rawvalue`; tests and user examples use
   `fromcode`.

The `BinaryValue` inner constructor should expose only a private raw token or an
equivalent private `new` path. It must not retain a public one-argument
`Unsigned` method, because that method would take precedence over the new
value-based `Real` constructor and silently preserve the old ambiguity.

Calling a format type is a conscious convenience decision, not an ordinary
Julia constructor relationship: `F(x) isa BinaryValue(F)` and `F(x) isa F` is
false. This exception earns its place because named formats remain concise
numeric constructors while their constants correctly denote formats. State it
in the `Binary` and `BinaryValue` docstrings and test it directly so callers do
not have to infer the relationship from implementation details.

### 4.3 Projection has one source of dynamic truth

On Julia 1.12, use `Base.ScopedValues.ScopedValue` directly:

```julia
# The explicit abstract parameter is required: ScopedValue(RTE_SN) alone
# would infer only Projection{typeof(RTE),typeof(SN)} and reject other modes.
const _DEFAULT_PROJECTION = ScopedValue{Projection}(RTE_SN)

DefaultProjection() = _DEFAULT_PROJECTION[]

function with_projection(f::Function, rho::Projection)
    Base.ScopedValues.with(f, _DEFAULT_PROJECTION => rho)
end

DefaultRoundingMode() = RoundOf(DefaultProjection())
DefaultSaturationMode() = SatOf(DefaultProjection())
```

The final API has no mutation setters: remove `DefaultProjection!`,
`DefaultRoundingMode!`, and `DefaultSaturationMode!`. A persistent process-wide
setter is incompatible with a reliable task-local default and would require
the dual fallback scaffolding explicitly excluded from this plan.

`with_projection(rho) do ... end` binds the value for its dynamic extent,
restores it on normal return or exception, nests correctly, and follows Julia's
scoped-value inheritance rules for child tasks. Component queries derive from
the single projection; there are no independently mutable rounding and
saturation values that can become torn or inconsistent.

Every public array operation resolves the default once before entering an
element loop. Every operation that already accepts an explicit `Projection`
continues directly to its typed implementation and must not read the scoped
value. This is the crucial performance boundary.

The review measured why a second seam is required for scalar convenience
calls on Julia 1.12.6 (one thread, i9-14900K):

| Path | Time | Allocations |
|---|---:|---:|
| current `Ref{Projection}[]` | 2.50 ns | 0 |
| unbound `ScopedValue{Projection}[]` | 4.07 ns | 0 |
| scoped-value read inside `with` | 34.72 ns | 0 |
| current default `Add` through the RTE guard | 4.07 ns | 0 |
| explicit-projection `Add` | 1.25 ns | 0 |
| naive non-RTE scoped `Add` | 272.61 ns | 1 |

The naive result is unacceptable. A wrapper that receives an abstractly typed
projection and immediately calls the operation leaves the non-RTE result
dynamically typed and boxed. Route it through a projection-type function
barrier and assert the known datum return type:

```julia
@inline function _default_add(
        ::Type{T}, rho::P, x::T, y::T) where {T<:BinaryValue,P<:Projection}
    Add(BinaryFormatOf(T), rho, x, y)::T
end

function Add(x::T, y::T) where {T<:BinaryValue}
    rho = DefaultProjection()
    rho === RTE_SN && return Add(BinaryFormatOf(T), RTE_SN, x, y)::T
    _default_add(T, rho, x, y)::T
end
```

Generate the equivalent barrier for each operation arity and for value
construction. This permits one dynamic dispatch at a non-RTE scalar
convenience seam, then restores concrete projection and result types inside the
implementation. It must eliminate the allocation; it is not expected to equal
the explicit-projection floor. The RTE fast guard remains because it preserves
the overwhelmingly common unscoped path.

### 4.3.1 Why other mutable state remains process-wide

Task-locality follows semantics, not a blanket objection to `Ref`. Projection
changes numeric results, so concurrent tasks need independent values.
Performance-policy controls (`FAST_ARITH`, `FAST_ENCLOSURE`, threading and
table thresholds/budgets) change implementation strategy and are read on hot
paths; retaining process-wide `Ref`s is measurably cheaper and avoids scoped
lookups in kernels. Treat them as configuration that must not be mutated
concurrently with work.

Display already has the appropriate two-level interface: an `IOContext`
property is the local override and `DEFAULT_SHOW_STYLE` is only the
process-wide fallback. Keep that arrangement because display context naturally
travels with `IO`, not task scope. `TERNARY_TICK` is internal cache state under
the table lock, not a user default. Document these distinctions and include
the affected files in the ownership map; do not scope them as part of this
change.

### 4.4 Checked public seams, raw local seams

Apply the same pattern consistently:

| Representation | Checked public seam | Unchecked/private seam |
|---|---|---|
| datum code | `fromcode` | `_rawvalue` |
| packed words/bytes | `packedfromwords`, `packedfrombytes` | `_rawpacked` |
| dyadic carrier | ordinary validated constructor | `_rawdyadic` |
| block SoA storage | `BlockVector` constructor | `_rawblockvector` only if a measured kernel needs it |
| table entries | no direct public construction | cache-internal insertion |

Do not add a raw function merely for symmetry. Add it only when a caller has
already established the invariant outside a loop and Chairmarks shows that
rechecking in the loop matters.

## 5. Module and seam design

The target consists of six deep modules/interfaces rather than many pairwise
adapters:

1. **Format module** — owns canonical type creation, named-format registry,
   traits, query names, and `formatinfo`.
2. **Datum module** — owns the representation invariant, value construction,
   `fromcode`, `_rawvalue`, `codepoint`, and format recovery.
3. **Projection context module** — owns the one scoped default and convenience
   resolution. The projection engine remains context-free.
4. **Conversion module** — owns accepted source families and the exact
   one-rounding conversion kernel used by scalar and array interfaces.
5. **Table service** — owns caching, policy, deterministic statistics, and
   reset. Dictionaries, locks, keys, and table memories are implementation
   details.
6. **Storage module** — owns packed wire format and packed/block collection
   invariants while implementing Julia collection contracts.

The important seams are one-way:

```text
format type -> datum type -> projection/conversion -> operation kernels
                                  |
                                  +-> table service
datum code  <-> packed storage    +-> block storage
```

The adapters are only at public boundaries (`F(x)`, `fromcode(T, c)`, and
datum-type operation targets). Implementations normalize immediately to a
format type and then stay on type-specialized methods. This keeps policy local
and avoids a combinatorial format-type/datum-type/format-instance method grid.

## 6. Detailed implementation plan

### Phase 0 — freeze the contract and establish evidence

1. Record the current commit and dirty state. The existing uncommitted source
   and test changes belong to the working tree and must be incorporated, not
   overwritten.
2. Add focused API contract tests that express the target behavior. Initially
   keep them in a separate test file so each implementation phase has a small
   executable gate.
3. Capture Chairmarks baselines for constructor, conversion, default lookup,
   table introspection, packed serialization, and container operations. Record
   Julia version, CPU, thread count, projection, cache state, time,
   allocations, bytes, and throughput. Reproduce or explain material deviation
   from the scoped-value measurements in Section 4.3 before changing the gate.
4. Inventory every use of:
   `BinarySpecifier`, `_formattype`, `::Binary`, `F()`, `_NAMED`, named
   `Binary...` aliases, unsigned datum construction, `rawvalue`, default
   setters, direct table getters/keys, `PackedVector{T}(words,n)`, and direct
   `.data`/`.scales`/`.elems` access. Search separately for
   `T(codepoint(x))`, `BinaryValue(F, codepoint(x))`, and equivalent aliases:
   `codepoint` returns an `Unsigned`, so these round trips otherwise continue
   to compile while silently changing meaning.
5. Classify each call site as format identity, datum type, value construction,
   checked code import, or proven internal raw construction before changing it.
   This semantic classification prevents mechanical replacements from turning
   codes into values.

### Phase 1a — add the named code seam and migrate callers

This is a temporary implementation sequence, not compatibility support. Do not
commit or release the repository with both public interpretations in place.

1. Add checked `fromcode` methods for a format type and datum type. Add the
   exact-contract `_rawvalue` internal route while the existing unsigned
   constructor still exists.
2. Classify and migrate every source, test, benchmark, precompile, and example
   call site: checked code imports use `fromcode`, proved implementation loops
   use `_rawvalue`, and numeric inputs retain ordinary construction.
3. Run the focused constructor, codec, packed, table, and operation tests. At
   this point behavior has not broken, so a failure identifies a mistaken
   classification rather than being confounded with the semantic switch.
4. Repeat the `T(codepoint(x))` search and require zero residual call sites
   outside any intentionally failing migration test.

### Phase 1b — make missed unsigned construction fail diagnostically

Simply deleting the unsigned-specific method would not produce a `MethodError`:
the general `Real` constructor would immediately accept the same argument as a
numeric value. Use a temporary diagnostic method instead.

1. Replace the code-point unsigned constructor with a method that throws a
   distinctive migration `ArgumentError` directing code users to `fromcode`
   and value users to the eventual ordinary constructor.
2. Run the focused source, test, benchmark, precompile, and doctest groups.
   Classify every diagnostic failure rather than mechanically changing it.
3. Search downstream examples available in the repository, especially nested
   `codepoint` expressions and generated alias calls.
4. Do not commit or release this diagnostic interface. Its only purpose is to
   expose calls that a source grep or incomplete test inventory missed.

### Phase 1c — make the format and datum model canonical

1. In `types/binaryformats.jl`, suppress construction of zero-field `Binary`
   instances and remove `BinarySpecifier`, `_formattype`, all `::Binary`
   overloads, instance printing, and instance trait methods.
2. Change `rules/constraints.jl` so `_NAMED` maps each standard name to its
   format type. Update its declared value type and the `Formats` namespace.
3. Introduce one internal datum-type query, for example `_datumtype(F)`, with
   the public spelling remaining `BinaryValue(F)`. Use it wherever a concrete
   array element type is required.
4. Add `(::Type{F})(x::Real; projection=nothing, rng=nothing, R=nothing) where
   F<:Binary`, delegating directly to `BinaryValue(F)(x; ...)` and asserting the
   concrete return type.
5. Refactor `BinaryValue` so its public numeric constructors all call the value
   conversion seam. Delete both the old code-point constructor and the Phase
   1b diagnostic method, so `Unsigned` now reaches the ordinary value path.
6. Remove `rawvalue` from `public` and delete it after every internal caller has
   moved to `_rawvalue`.
7. Update named-format use sites. Code such as `T = Binary8p4se` that needs an
   element type becomes `F = Binary8p4se; T = BinaryValue(F)`. Code that only
   constructs values can continue to call `Binary8p4se(x)`.
8. Update the precompile workload so it explicitly names `F` and `T`, and
   precompiles `F(x)`, `T(x)`, `fromcode(F,c)`, and `Convert(F,rho,x)`.
9. Run method-ambiguity and inference checks immediately. Overloading calls on
   `Type{<:Binary}` is the highest dispatch-risk change and should not be mixed
   with later cache or collection work before it is clean.

### Phase 2 — replace process-global defaults with scoped projection

1. Replace all three mutable projection `Ref`s in `rules/defaults.jl` with one
   `ScopedValue{Projection}(RTE_SN)`. Do not rely on inferred construction,
   which would bind the scoped value to the concrete `RTE_SN` parameterization.
2. Add and export `with_projection`; retain the three query functions, with
   component queries derived from `DefaultProjection()`.
3. Delete all three setters and all benchmark/test helpers that save and
   restore them. Helpers needing a non-default projection must execute their
   measured body under `with_projection`.
4. Audit generated scalar methods, Base veneers, broadcasting, constructor
   calls, and array kernels. Resolve the scoped default once per public call;
   never once per array element.
5. Test nested scopes, exception restoration, sibling-task isolation, and
   child-task inheritance. Include both `@async` and `Threads.@spawn` cases
   supported by Julia's scoped-value model.
6. Preserve the `rho === RTE_SN` specialization guard where it measurably helps,
   then route every other projection through an arity-specific,
   projection-typed function barrier with a concrete result assertion. Read the
   scoped value only in convenience wrappers. Explicit projection methods must
   remain identical to their current implementation.
7. Chairmark the scoped read, RTE convenience call, non-RTE scoped convenience
   call, and explicit call independently. Require zero allocations for all
   steady-state scalar cases; accept the one dynamic dispatch and measured
   latency of the non-RTE convenience seam.
8. Leave performance-policy `Ref`s and the display fallback unchanged. Add
   documentation stating their process-wide configuration contract and use
   `IOContext` for local display changes.

### Phase 3 — unify scalar and array conversion

1. Define a closed accepted-source union shared by both surfaces:
   `BinaryValue`, `Float16`, `Float32`, `Float64`, `BFloat16`, `Float128`,
   `BigFloat`, and `Integer`.
2. Keep `Rational` and `Irrational` explicit refusals. Do not add a generic
   `Real` fallback that could introduce an unproved double rounding.
3. Extract one `_convert_value(F, rho, x, R)` function family. It selects the
   exact carrier ladder and projects once; scalar `Convert` and array loops both
   call it.
4. Keep the existing exact-integer gates: exact `Float64`, then exact
   `Float128`, then adequate-precision `BigFloat`. Quadmath elementary
   functions are not assumed correctly rounded; this phase uses `Float128`
   only where its exact representation or a proved enclosure/refusal makes it
   safe.
5. For arrays, allocate with `similar(A, BinaryValue(F))`, preserve axes and
   shape, resolve stochastic RNG once, and draw exactly once per element in
   deterministic `eachindex` order.
6. Refuse heterogeneous abstract arrays whose element type is merely `Real`
   rather than hiding dynamic dispatch in the loop. Users can convert the
   source array to one supported concrete family.
7. Add default-projection array convenience methods only if they resolve
   `DefaultProjection()` before the loop. Explicit-`rho` methods remain the
   primitive interface.

### Phase 4 — consolidate queries and format introspection

1. Establish one generic function object for each query and bind both the
   P3109 spelling and Julia-style spelling to it, rather than writing forwarding
   wrappers. Permanent names include:

   | P3109/current | Julia-style | Accepted inputs |
   |---|---|---|
   | `BinaryFormatOf` | `formatof` | format type, datum type, datum value |
   | `BitwidthOf` | `bitwidth` | format type, datum type, datum value |
   | `SignednessOf` | `signedness` | format type, datum type, datum value |
   | `DomainOf` | `domain` | format type, datum type, datum value |
   | `CodeType` | `codetype` | valid bitwidth, format type, datum type/value |
   | `ValueType` | `valuetype` | valid bitwidth, format type, datum type/value |

   These are permanent vocabulary bindings, not transitional compatibility
   adapters. They must share the same method table and have zero run-time cost.
2. Do not export a new `precision` function that shadows Base. Extend
   `Base.precision` consistently for format and datum types if the existing
   `AbstractFloat` contract does not already cover both.
3. Make `formatof(F) === F` for a format type. This gives internal code one
   total normalization query without accepting format instances.
4. Add `formatinfo(F)` returning a stable named tuple. At minimum include:

   ```julia
   (name, format, datumtype, bitwidth, precision, signed, extended,
    exponentbias, exponentbits, trailingbits, codetype, valuetype,
    datumcarrier, promotecarrier)
   ```

5. Ensure `formatinfo` is pure, type-stable, and constant-foldable for a
   concrete `F`. Do not include decoded extrema or allocated tables in the
   compact result; those already have focused APIs.

### Phase 5 — turn table caching into a service

1. Remove `get_table`, `table_for`, `TableKey`, `TernaryKey`, cache dictionaries,
   counters, and table memories from the public surface. Operation kernels may
   continue to use them internally.
2. Keep `table_policy` as the prospective policy query. Validate the operation
   and arity before computing a key, and preserve the documented rule that
   `nelems` does not increment use counters.
3. Add `table_stats()` as one locked snapshot with stable keys, for example:

   ```julia
   (entries = 7,
    bytes = 14336,
    by_arity = (unary = 2, binary = 4, ternary = 1),
    by_codeunit = (uint8 = 6, uint16 = 1),
    adaptive_signatures = 3,
    ternary_budget = 64 * 1024 * 1024)
   ```

4. Add `table_entries()` for detail. Return public named tuples rather than
   internal key structs, and sort by operation, arity, result format, operand
   formats, rounding, and saturation.
5. Retain `empty_tables!()` as the intentional mutation operation. It must clear
   every cache, adaptive counter, and LRU tick under the same lock.
6. Delete `table_bytes`, `table_count`, `ternary_count`, and `table_keys`; their
   information is subsumed by the two coherent snapshot functions.
7. Take a single lock per snapshot. Do not compute user-visible totals by
   calling several separately locked query functions, which can describe
   different moments under concurrent cache activity.

### Phase 6 — define packed serialization and collection behavior

1. Keep `PackedVector`'s fixed-size `Memory{UInt64}` backing store and validate
   `n >= 0`, checked `n*K`, exact word count, and canonical zero padding in the
   unused high bits of the final word.
2. Remove the ambiguous public `PackedVector{T}(words,n)` representation
   constructor. Add:

   ```julia
   packedfromwords(T, words, n)  # validates and copies
   packedwords(pv)               # returns an independent Vector{UInt64}
   packedfrombytes(T, bytes, n)  # canonical little-endian wire form
   packedbytes(pv)               # canonical little-endian bytes
   ```

3. Define “words” as `cld(n*K,64)` logical `UInt64` values, independent of host
   byte order. Define bytes as the minimal `cld(n*K,8)` bytes in little-endian
   bit order. Both forms require zero unused high bits in their final unit.
   This is necessary for an actual portable serialization interface; exposing
   the in-memory byte representation would not be enough.
4. `_rawpacked` may take ownership of a validated `Memory{UInt64}` only inside
   packing/deserialization kernels. Public constructors always copy, so later
   source mutation cannot invalidate bounds or padding assumptions.
5. Implement `copy(pv)` as an independent packed copy; `collect`/`Vector` as an
   unpacked copy; and conversions in each direction with unsurprising element
   types.
6. Implement the most specific non-ambiguous `copyto!` methods for packed to
   unpacked, unpacked to packed, and packed to packed. Run Aqua ambiguity checks
   after each signature. If a broad signature conflicts with Base, narrow it
   rather than introducing a catch-all.
7. Define `similar(pv)` as an independent, valid zero-filled packed vector of
   the same length and datum type. Define `similar(pv, S, dims)` to preserve
   packed storage only for a one-dimensional `S<:BinaryValue` result; otherwise
   use the ordinary Array fallback.
8. For `BlockVector`, implement independent `copy`, shape-preserving `similar`,
   exact-type `copyto!`, and `Vector`/`collect` round trips. Preserve the SoA
   representation when the requested element type is `Block{B,S,E}` and use
   normal arrays otherwise. Zero-initialize new scale/element storage so an
   accessible `BinaryValue` never contains arbitrary high code bits.
9. Test aliasing explicitly: mutating a copy, a source word vector, or a source
   block vector must not mutate its independently constructed peer.

### Phase 7 — validate registry calls and normalize errors

1. Freeze operation metadata after module construction. Replace the mutable
   registry scan used by `opinfo` with a read-only name lookup and a stable
   public `operationinfo(op)` named tuple if introspection is desired.
2. At each runtime-symbol boundary (`vmap`, `table_policy`, approximate
   registration/use, and any dynamic table request), validate:
   - the operation exists;
   - supplied operand count matches its arity;
   - the operation is supported by that subsystem; and
   - result and operand formats are concrete valid format types.
3. Only after validation, cross a function barrier to `Val(op)` so inner loops
   retain static dispatch. Do not perform registry lookup per element.
4. Use the following error taxonomy:

   | Condition | Exception |
   |---|---|
   | invalid format fields, code range, padding, mode, policy value, or unknown operation | `ArgumentError` |
   | known operation with wrong operand count | `ArgumentError` with expected/actual arity |
   | incompatible array/block shapes or packed storage length | `DimensionMismatch` |
   | invalid collection index | `BoundsError` via Base bounds checking |
   | checked size arithmetic overflow | `OverflowError` from `Base.checked_*` |
   | unsupported Julia input type with no promised API | `MethodError` |
   | deliberately refused `Rational`/`Irrational` conversion | `ArgumentError` explaining the correctness risk |
   | IEEE invalid arithmetic represented by the format | return the prescribed NaN/code; do not throw |

5. Errors at public seams must name the function, offending value/type, and
   accepted alternative. Internal raw functions may rely on documented
   preconditions and assertions, not user-facing validation.
6. Make all registry- and cache-derived listings deterministic by sorting on
   semantic fields, never dictionary insertion order or type object identity.

### Phase 8 — remove residue and align all consumers

1. Search again for all deleted forms. The target count is zero for
   `BinarySpecifier`, `_formattype`, `::Binary`, `F()` format tokens, public
   `rawvalue`, projection setters, direct public table getters, and the old
   packed representation constructor.
2. Update docstrings and all files under `docs/src/` to use named format types,
   `BinaryValue(F)` where a datum type is required, `fromcode` for codes, and
   `with_projection` for contextual defaults.
3. Revise `docs/structuralplan.md` and `docs/checkpoint.md`. They currently
   record format instances and total instance accessors as deliberate design;
   leaving those records unchanged would make the new interface internally
   contradictory.
4. Update examples so every code literal is visibly introduced by `fromcode`;
   otherwise integers and unsigned integers are visibly numeric values.
5. Update benchmark helpers to use scoped projection and the new table
   snapshots. Do not reach into scoped values, caches, or container fields.
6. Update conformance reports and `formatname`/`codetable` to accept format
   types, datum types, and datums through their documented query seam, without
   reintroducing format instances.
7. Update exports/public declarations. An exported name must have a docstring;
   a private raw path and internal cache implementation must not be `public`.
8. Set `Project.toml` to version `0.2.0` and add a `CHANGELOG.md` entry that
   names every removed export and semantic break, with direct replacements.
9. Run the focused tests and benchmarks below. Per the explicit execution
   constraint, this work does not run `Pkg.test()`. Its completion report must
   say “targeted verification complete,” not “the full suite is green.” A
   later release/CI owner may apply a separate full-suite gate.

## 7. Source ownership map

| Files | Primary work |
|---|---|
| `src/types/binaryformats.jl` | type-only format contract, no instances, lowercase format queries |
| `src/types/binaryvalue.jl` | datum type factory, `fromcode`, `_rawvalue`, format recovery |
| `src/rules/constraints.jl` | named aliases map to format types; deterministic registry |
| `src/rules/defaults.jl` | scoped projection and removal of setters |
| `src/compat/show.jl` | retain fast global fallback and document `IOContext` as the local display seam |
| `src/compat/base.jl` | `reinterpret`, Base precision/conversion behavior |
| `src/projection/project.jl` | accept only format/datum types at the public seam; remain context-free |
| `src/ops/scalar.jl` | shared value conversion and constructor delegation |
| `src/ops/registry.jl` | frozen metadata and checked runtime-symbol lookup |
| `src/ops/oracle.jl` | retain process-wide performance-policy configuration |
| `src/arrays/kernels.jl` | scalar/array conversion parity and one-time policy/RNG resolution |
| `src/arrays/packed.jl` | serialization, invariant checks, Base collection contract |
| `src/arrays/blocks.jl` | Base collection contract for SoA blocks |
| `src/tables/cache.jl` | atomic statistics snapshots and deterministic entries |
| `src/tables/policy.jl`, `src/tables/build.jl` | internal-only table access and validated policy boundary |
| `src/content/*.jl`, `src/carriers/*.jl` | migrate raw datum creation without changing numeric algorithms |
| `src/rules/approx.jl`, `src/rules/conformance.jl` | registry validation and deterministic results |
| `src/AIFloats.jl` | exports, public/private boundary, includes, precompile workload |
| `test/test-*.jl` | focused behavior, concurrency, error, ambiguity, and invariant tests |
| `benchmark/*.jl` | Chairmarks regression rows and scoped benchmark controls |
| `docs/src/*.md` | public API/reference/example migration |
| `docs/structuralplan.md`, `docs/checkpoint.md` | replace superseded format-instance design records |
| `Project.toml`, `CHANGELOG.md` | `0.2.0` release identity and breaking-change migration notes |

## 8. Correctness verification

### 8.1 Construction and dispatch

Test every source family with both `F(x)` and `BinaryValue(F)(x)`, including an
`Unsigned` value whose numeric projection differs from its old code-point
interpretation. For every valid code of representative 3-, 8-, 9-, and 16-bit
formats:

```julia
x = fromcode(F, c)
@test codepoint(x) == c
@test typeof(x) === BinaryValue(F)
@test fromcode(BinaryValue(F), c) === x
```

Test negative codes, `codemask(F)+1`, very wide integers, wrong code units,
zero-argument format calls, partial/abstract format types, and constructor
method ambiguities. Verify `F(x)`, `T(x)`, and `Convert(F,rho,x)` produce equal
code points for each deterministic projection. Pin the conscious constructor
relationship with `F(x) isa BinaryValue(F)` and `!(F(x) isa F)`. Add an
explicit migration test showing that `T(codepoint(x))` is value construction
and `fromcode(T, codepoint(x))` is the code-preserving round trip.

### 8.2 Scoped behavior

Test the default outside, inside, and after nested scopes; restoration after a
thrown exception; two concurrent sibling tasks with different projections;
and child-task inheritance. Test that explicit projections override ambient
context and that component queries always match `RoundOf`/`SatOf` of the one
current projection.

### 8.3 Conversion parity

For each accepted scalar type, compare scalar conversion to every element of
array conversion over edge populations: zero, signed zero, subnormal
boundaries, ties, finite extrema, infinities, NaNs, large integers, and values
requiring `Float128` or `BigFloat`. Compare code points, not decoded approximate
values. Verify Rational/Irrational refusals are identical at scalar and array
boundaries. For stochastic projections, use a seeded RNG and verify one draw
per element in index order.

### 8.4 Cache, serialization, and collections

Verify cache snapshots are internally coherent during concurrent reads and
builds, details sum to totals, entries are sorted, a prospective policy query
does not mutate counters, and reset clears tables/counters/ticks.

For packed storage, exhaustively round-trip all codes for small formats and
sample boundary-crossing positions for every `K=3:16`. Test word and byte
round trips, little-endian fixtures, empty vectors, exact 64-bit boundaries,
nonzero padding refusal, length overflow, source mutation, `copy`, `similar`,
and each `copyto!` direction. Test analogous ownership and shape contracts for
`BlockVector`.

### 8.5 Focused test commands only

Run individual files or small related groups, not `Pkg.test()`. This limitation
is an explicit execution constraint, not evidence that a package-wide breaking
change has been exhaustively verified:

```bash
julia --project=. -e 'include("test/test-binary-format.jl"); include("test/test-binaryvalue.jl")'
julia --project=. -e 'include("test/test-projection.jl"); include("test/test-ops.jl")'
julia --project=. -e 'include("test/test-kernels.jl"); include("test/test-tables.jl")'
julia --project=. -e 'include("test/test-blocks.jl")'
julia --project=. -e 'include("test/test-governance.jl")'
julia --project=. -e 'using Aqua, AIFloats; Aqua.test_ambiguities(AIFloats)'
```

Before enactment, confirm the exact existing test filenames and adjust the
groups; do not create a command that accidentally invokes `test/runtests.jl`.
Use `@inferred` and targeted JET calls on the new constructor, `Convert`, and
runtime-symbol function barriers.

## 9. Performance and throughput plan

Chairmarks remains confined to `benchmark/Project.toml`; it is not a runtime
dependency. Add a focused `api` benchmark suite or narrowly extend the current
scalar/array suites.

### 9.1 Measurements

Measure, with interpolated operands and compilation warmed separately:

1. `F(1.3)`, `T(1.3)`, `F(UInt8(3))`, and explicit-projection equivalents;
2. `fromcode(F,c)` checked and `_rawvalue(F,c)` inside an internal benchmark;
3. explicit, unscoped-RTE convenience, and scoped non-RTE `Add`, `Exp`, and
   `Convert`, reporting the three paths separately;
4. an unbound scoped-value read, an in-scope read, `with_projection` scope
   setup, and repeated operations inside one scope; reproduce the review's
   4.07 ns/34.72 ns read contrast or record why the machine differs;
5. scalar/array conversion for every accepted carrier at `N=64,1024,65536`;
6. cold/earned/warm table operation controls plus `table_stats` and
   `table_entries` separately;
7. `packedwords`, `packedbytes`, both deserializers, `copy`, `collect`, and
   `copyto!` for every meaningful bit-width boundary;
8. `BlockVector` construction, indexing, `copy`, `similar`, and bulk copying;
9. dynamic-symbol `vmap` validation cost versus steady-state kernel time.

Run at least five fresh processes for small differences. Report median time,
allocations, bytes, and elements/second along with commit/dirty state, Julia,
CPU, threads, format, projection, cache state, and population.

### 9.2 Performance acceptance gates

- Explicit-projection scalar hot paths: zero allocations and no meaningful
  regression; investigate a repeatable median regression above 3%.
- `F(x)`, `T(x)`, and deterministic `fromcode`: zero allocations after
  compilation.
- Scoped default lookup: at most once per public call and never per array
  element. A non-RTE scalar convenience call may dynamically dispatch once at
  the projection-type function barrier, but must return the known datum type
  without allocating. Judge its latency separately from the explicit path; do
  not claim parity with the 1.25 ns explicit-projection floor.
- Process-wide performance-policy reads must not become scoped-value reads.
  Their throughput baselines remain controls for the task-local projection
  work.
- Array conversion and packed kernels: no repeatable throughput regression
  above 5% at `N=65536`; smaller sizes are separately latency-sensitive.
- Cache stats/details may allocate their returned snapshots, but table lookup
  and operation kernels must not allocate because introspection exists.
- Checked deserialization may allocate exactly its owned result storage and
  returned collection; `_rawpacked` must not add copying to established
  internal pack kernels.
- Runtime operation validation occurs once before the function barrier, never
  in an element loop.

Do not weaken validation or correctness to meet a percentage. If a public
checked constructor is measurably slower, retain the check and ensure internal
proved loops use the private raw seam.

## 10. Review of the plan

### Correctness review

The most dangerous change is unsigned construction: an unclassified old call
would continue to compile but change meaning. The improved plan therefore
requires semantic inventory, adds and tests the named code seam first, migrates
the repository, temporarily makes unsigned construction throw diagnostically,
and only then enables its new value meaning. This three-step local sequence
exposes repository mistakes without retaining compatibility or a diagnostic
trap in the final interface. It also corrects the review's suggestion that
deleting the old method alone would yield `MethodError`; the general `Real`
method would otherwise accept the call silently.

The second danger is named aliases. Changing them from datum types to format
types affects array element declarations, subtype tests, promotion, and method
signatures even though calls such as `Binary8p4sf(1.5)` still work. The plan now
explicitly separates `F` and `T` in all internal, test, benchmark, and
documentation contexts.

The third danger is task context. A mutable fallback would reintroduce races
and two sources of truth, so the improved end state removes setters entirely.
Explicit-projection functions remain pure with respect to task context. The
review's measured allocation in a naive non-RTE scoped call is addressed by a
projection-type function barrier and concrete result assertion.

Portable packed serialization requires defined byte order and canonical
padding. The plan includes both; merely exposing `Vector{UInt64}` would have
been incomplete.

### Completeness review

The plan covers scalar operations, arrays, blocks, packed storage, tables,
conformance, approximate implementations, precompilation, tests, benchmarks,
exports, and documentation. It also covers Base contracts, error categories,
deterministic ordering, runtime registry validation, alias ownership, and the
public/private boundary. These were the principal omissions from a plan that
only changed constructors and default projection.

It now also covers the superseded structural design records, the `0.2.0`
version and CHANGELOG, the `T(codepoint(x))` migration trap, the intentional
`F(x) isa BinaryValue(F)` relationship, and the reason other performance and
display state is not moved into scoped values.

No compatibility phase remains in the delivered design. Phases 1a and 1b are
local migration/diagnostic checkpoints removed by Phase 1c. The only dual
names retained are permanent P3109/Julia query bindings that share one function
object; they are part of the target interface rather than migration adapters.

### Performance review

The design preserves type parameters as the specialization currency. `F(x)` is
one inline delegation, format normalization is compile-time, explicit
projection paths do not consult scoped state, a non-RTE convenience call
crosses a projection-type function barrier once, array methods resolve context
once, dynamic operation validation crosses its function barrier once, and raw
constructors remain available only inside proved loops. Cache statistics and
serialization copying are kept off arithmetic hot paths. Performance-policy
`Ref`s remain process-wide specifically to avoid imposing scoped lookup cost on
kernels.

The plan also adds stop gates. No optimization is accepted from inference
alone: constructor dispatch, scoped lookup, conversion throughput, packed
copying, and registry validation are each measured with Chairmarks and checked
for allocations.

## 11. Completion criteria

The locally authorized implementation and targeted verification are complete
only when all of the following are true. This status does not assert that the
full package suite has run; release-wide verification remains a separate CI or
maintainer action.

- named `Binary...` constants are format types;
- no `Binary` instance can be created or is accepted by public methods;
- `F(x)` is documented and tested to return `BinaryValue(F)`, not `F`;
- every ordinary numeric constructor, including `Unsigned`, means value;
- `fromcode` is the checked public code constructor and `_rawvalue` is private;
- projection defaults are a single `ScopedValue`, and all setters are gone;
- non-RTE scoped scalar convenience calls cross one typed function barrier and
  allocate zero bytes after compilation;
- performance policy remains process-wide and local display policy uses
  `IOContext`;
- scalar and array conversion accept/refuse the same source families;
- cache internals are private and coherent snapshots are public;
- packed words and bytes have checked, owned, deterministic serialization;
- packed and block vectors satisfy the documented Base collection contracts;
- operation/arity validation happens before specialized runtime-symbol work;
- errors follow the exception matrix and introspection is deterministic;
- lowercase queries and `formatinfo` are documented and type-stable;
- `Project.toml` is version `0.2.0`, `CHANGELOG.md` records every break, and the
  structural plan/checkpoint no longer promise format instances;
- targeted correctness, ambiguity, inference, concurrency, and invariant tests
  pass; and
- Chairmarks gates show no material hot-path or throughput regression.
