# CHANGELOG

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog],
and this project adheres to [Semantic Versioning].

## [Unreleased]

### Added

Ergonomics for the operation register. The draft writes an operation as
`Op_{fx,fy,fr,ρ}(x, y)` — parameters as subscripts, operands in the
parentheses. Julia reads `fx` and `fy` off the operands' own types, which
leaves `fr` and `ρ` as the only positional parameters; they may now sit at
either end of the call, or bind on their own. Every spelling forwards to the
one implementation, so there is still exactly one projection.

- **Operands-first spellings** for every register operation and `Convert`:
  `Op(xs..., fr, ρ)` mirrors `Op(fr, ρ, xs...)`, and `Op(xs..., ρ)` takes the
  result format from the operands — the every-arity mirror of the unary
  `Op(ρ, x)`. Positional, not keyword: `fr`/`ρ` as defaulted keywords on the
  same-format method were measured to cost the scoped call 27.9 → 33.5 ns
  because the keyword machinery sits on the hot path whether or not a keyword
  is passed. As separate methods over disjoint signatures they cost the tuned
  path nothing, and its 0-allocation scoped call is pinned unchanged.
- **`AIFloats.OpSpecialization`**, the draft's *operation specialization*
  (§4.3.2.4) as a value: `Op(fr, ρ)` with no operands returns a callable
  carrying just the two parameters, and `nameof`, `formatof`, and `Projection`
  read them back. It is zero-size and `isbits`, so a specialization over a
  constant projection forwards at the cost of the explicit call.
- A specialization applied to **arrays** is the array operation, so it takes
  the `vmap` kernel — the memoized gather, the threaded loop — rather than a
  per-element `map`. New rows in `benchmark/scalar.jl` and `benchmark/arrays.jl`
  pin the spellings against each other: 8.7/8.7/8.6/8.6 ns for the four scalar
  forms of `Add` at K = 8, and 0.26 ns/element for every array form against
  9.6 for `map(Add(F, ρ), A, B)` over 4096 `Binary8p4se` datums.

`OpSpecialization` **binds** parameters; it never composes operations, and
there is deliberately no `∘` for it. `Convert(fr, ρ, Op(x, y))` is not
`Op(x, y, fr, ρ)`: the first projects twice. New tests in `test/test-ops.jl`
pin the counterexample in both directions — into a wider result format the
decomposition has already discarded the bits the exact result needed, and into
a narrower one it lands a full ulp away — over the whole `Binary8p4se` grid.

### Documentation

- The Operations page gained *Parameters and operands* (the §4.3.1 signature
  schema, and why `fr` and `ρ` are the only subscripts Julia has to carry),
  *Binding the parameters*, *Arrays take the kernel*, and *An operation does
  not decompose*. The signature table now lists all seven shapes.
- New basic and intermediate examples for the operand-first spellings and for
  a bound operation over arrays.

A documentation-correctness pass (`docs/refinedocs2.md`). Every claim is now
measured against one normative source — the IEEE Working Group P3109 Interim
Report on Arithmetic Formats for Machine Learning, version 4.0.3 (2026-09-01),
whose PDF digest is recorded in `docs/other/p3109-delta.md` and reported by
`draft_identity()`.

- `draft_identity()` now names the designated report (revision, date, URL, PDF
  SHA-256) alongside the retained transliteration, and `draft_revision()` and
  `conformance_report` state plainly that the report is an unapproved draft and
  that the declaration is **not** a certification.
- The exponent-bit budget is stated correctly: `(K - S) - (P - 1)`, not
  `K - P - S`. The concepts page and the `PrecisionOf` docstring both dropped a
  `+1` and printed 3 and 4 exponent bits where the truth is 4 and 5.
- The default projection is documented as `RTE_SN`, task-local, everywhere it
  had been called `RTE_SF`.
- Every public binding is documented: 173 gaps closed, 153 of them by
  registry-generated family docstrings for the scalar and `Block*`/`Scaled*`
  operations. The reference is now generated from `Base.isexported` /
  `Base.ispublic`, so it holds nothing private and the build fails on a gap.
- New Operations page; new `test/test-doc-contracts.jl` pinning the facts the
  documentation asserts about itself.
- Corrected: the `Binary` docstring's contradictory "append `()`" sentence,
  `CodeType`/`ValueType` claiming to accept a format instance, a `BinaryValue`
  doctest that gave `64.0` where the answer is `72.0`, the binary adaptive
  table band (documented as ternary-only), `BlockReduceMultiply` described as
  always using `BigFloat`, and installation instructions naming a registry the
  package is not yet in.


## [0.2.0] - 2026-09-01

An API-consistency release. Every break below is a break on purpose: each one
removes a second way of saying something the package already said, or a
silently-wrong reading of something a caller wrote.

### Breaking — formats are type-level information

A format is a **type**, and there is no longer a second, instance-shaped
spelling of it.

| Removed | Replacement |
|---|---|
| `F()` (a zero-field format instance) | `F` is already the format; the error says so by name |
| every `::Binary` instance method (31 of them) | the `::Type{<:Binary}` method that was already there |
| `AIFloats.BinarySpecifier`, `AIFloats.\_formattype` | not needed; there is one kind of format argument |
| exported `BinaryFloat` | removed in 0.1.x already; `BinaryValue <: AbstractFloat` |

`F(x)` still constructs a **datum**, so `F(x) isa F` is `false` and the datum
type is spelled `BinaryValue(F)`. That is the one deliberate exception to the
ordinary type/instance relationship, and it is now stated in both docstrings.

Keeping an instance surface *total* was a standing obligation on every method
anyone added; one of those bridges had already been written as a self-recursion
Julia cannot diagnose, because the signature legitimately matches itself. It
presented as `StackOverflowError`, not as an ambiguity. Removing the instances
discharges the obligation once.

### Breaking — construction has one semantic axis

**`Unsigned` is no longer a code point.** `F(0x03)`, `BinaryValue(F, 0x03)`,
`BinaryValue{F}(0x03)` and `convert(BinaryValue(F), 0x03)` now all mean *the
number three*, exactly as `F(3.0)` does.

```julia
# before                       # after
BinaryValue(F, 0x45)           fromcode(F, 0x45)      # the datum at code point 0x45
                               F(0x45)                # the number 69, projected into F
```

`fromcode(F, code)` / `fromcode(T, code)` is the checked code-point seam, and
accepts any `Integer` width — the range is checked *before* narrowing, so
`fromcode(F, UInt16(300))` on an eight-bit format raises rather than truncating
to 44.

This is the change most likely to be silently wrong in existing code, because
the old and new spellings are both valid Julia. `T(codepoint(y))` used to be a
reinterpretation and is now a numeric conversion. Search for datum construction
from an `Unsigned` and classify each site; do not rewrite mechanically.

Also removed: public `rawvalue` (no callers remained), and
`Base.convert(::Type{T}, ::Unsigned)`, which existed only to override the old
code-point meaning.

### Breaking — the default projection is task-local

| Removed | Replacement |
|---|---|
| `DefaultProjection!(ρ)` | `with_projection(f, ρ)` |
| `DefaultProjection!(μ, σ)` | `with_projection(f, μ, σ)` |
| `DefaultRoundingMode!`, `DefaultSaturationMode!` | derive from `DefaultProjection()`; bind with `with_projection` |

```julia
# before
old = DefaultProjection()
try
    DefaultProjection!(RTZ_SF)
    T(1.3)
finally
    DefaultProjection!(old)
end

# after
with_projection(RTZ_SF) do
    T(1.3)
end
```

A projection changes numeric **results**, so a process-wide setter makes two
concurrently running tasks silently fight over what arithmetic means. The
scoped binding restores on return *and on exception*, nests, and is inherited
by child tasks. `DefaultRoundingMode()` and `DefaultSaturationMode()` now derive
from the single value and cannot be read torn.

Performance-policy controls (`FAST_ARITH`, `FAST_ENCLOSURE`, threading and
table budgets) stay process-wide `Ref`s on purpose: they select an
implementation *strategy* rather than a result.

### Breaking — the table cache is a service

| Removed | Replacement |
|---|---|
| `table_bytes()`, `table_count()`, `ternary_count()` | `AIFloats.table_stats()` |
| `table_keys()` | `AIFloats.table_entries()` |
| `get_table`, `table_for` in `public` | still there, no longer public API |

Each removed function took the cache lock separately, so a caller assembling a
report from several of them could describe three different moments of a cache
another task was filling — and print totals that do not add up. `table_stats()`
and `table_entries()` each take the lock **once**; details sum to totals by
construction. `table_entries()` reports format types and the mode names a
caller writes, never the internal key struct.

`ConformanceDeclaration.cached_specializations` moved to those public named
tuples and gained a `cached_bytes` field, because `conformance_report` used to
re-read the byte total at print time and print a count and a size from two
different moments.

### Breaking — packed storage

| Removed | Replacement |
|---|---|
| `PackedVector{T}(words, n)` | `packedfromwords(T, words, n)` (validates and copies) |

The old constructor could not say whether it validated, copied, or took
ownership. The new surface is `packedfromwords` / `packedwords` /
`packedfrombytes` / `packedbytes`; both forms are *logical*, defined on the bit
stream rather than on this host's byte order, so what one machine writes
another reads.

### Fixed

- **`similar(pv::PackedVector)` packed uninitialized datums.** A `BinaryValue`
  read out of `undef` memory can carry bits above `K`, and the packing loop
  writes them into the **neighbouring** element's share of the shared word.
  `getindex` masks what it reads, so the corruption was silent. `similar` is
  now zero-filled, as is every new `BlockVector` scale and element array.
- **Packed padding was never validated.** `setindex!` on a cross-word element
  assumes the next word's high bits are canonical, and the byte form copies its
  final unit verbatim. Both deserializers now refuse nonzero padding.
- **`vmap(op::Symbol, …)` did not validate `op`.** An unknown symbol surfaced
  as a `MethodError` from deep inside a kernel, naming nothing a caller could
  act on. Both `vmap` and `vmap!` now validate the operation and its arity once
  at the boundary, then cross into `Val(op)`.
- The array `Convert` carried a private copy of the scalar carrier ladder. They
  agreed; nothing made them keep agreeing. Both now call one
  `_convert_value(F, ρ, x, R)` family, verified element-by-element against the
  scalar surface by code point over edge populations.

### Added

- `with_projection(f, ρ)` / `with_projection(f, μ, σ)`.
- `fromcode(F, code)` / `fromcode(T, code)`.
- `formatinfo(F)` — a 14-field named tuple, pure, type-stable, and
  constant-folding to a literal for a concrete `F`.
- Julia-style query spellings **bound to the same function objects** as their
  P3109 names, not forwarding wrappers: `formatof`, `bitwidth`, `signedness`,
  `domain`, `codetype`, `valuetype`. `formatof === BinaryFormatOf` is `true`.
- `Base.precision` now answers for a format as well as a datum. No `precision`
  of AIFloats' own is exported: shadowing Base's would change the meaning of a
  name every Julia program already has.
- `AIFloats.operationinfo(op)` and `AIFloats.operations()`; registry metadata is
  frozen after module construction and looked up by name.
- `AIFloats.table_stats()`, `AIFloats.table_entries()`.
- `packedfromwords`, `packedwords`, `packedfrombytes`, `packedbytes`.
- `Convert(F, A)` — array conversion under the task default, resolved once
  before the loop.
- `copy`, `similar`, and exact-type `copyto!` for `PackedVector` and
  `BlockVector`.
- `AIFloats.ConvertNumber` / `AIFloats.ConvertSource` name the closed set of
  accepted conversion sources.

### Migration checklist

1. `F()` → `F`; a datum type is `BinaryValue(F)`.
2. Datum construction from an `Unsigned`: decide whether each site meant a code
   point (`fromcode`) or a number (unchanged spelling). **Classify; do not
   rewrite mechanically** — both spellings still compile.
3. `DefaultProjection!(ρ)` + `try`/`finally` → `with_projection(ρ) do … end`.
4. `table_count()`/`table_bytes()` → one `table_stats()` call.
5. `PackedVector{T}(words, n)` → `packedfromwords(T, words, n)`.

<!-- Links -->

[keep a changelog]: https://keepachangelog.com/en/1.1.0/
[semantic versioning]: https://semver.org/spec/v2.0.0.html

<!-- Versions -->

[unreleased]: https://github.com/JeffreySarnoff/AIFloats.jl/compare/v0.2.0...HEAD
[0.2.0]: https://github.com/JeffreySarnoff/AIFloats.jl/compare/v0.1.0...v0.2.0
