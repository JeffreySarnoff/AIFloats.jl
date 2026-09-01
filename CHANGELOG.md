# CHANGELOG

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog],
and this project adheres to [Semantic Versioning].

## [Unreleased]

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
