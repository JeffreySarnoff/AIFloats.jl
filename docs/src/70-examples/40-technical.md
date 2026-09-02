# [Technical examples](@id examples-technical)

```@meta
CurrentModule = AIFloats
DocTestSetup = :(using AIFloats)
```

These examples are useful when integrating AIFloats into a numerical library,
investigating performance, or checking conformance assumptions.

## Inspect carrier selection

The format's exponent span determines its internal carrier rung independently
of its storage width.

```@example technical_carriers
using AIFloats

formats = (
    Binary(8, 4, SIGNED, EXTENDED),
    Binary(16, 4, SIGNED, EXTENDED),
    Binary(16, 1, UNSIGNED, FINITE),
)

[(F, AIFloats.rung(F), AIFloats.datumcarrier(F)) for F in formats]
```

Carrier types are implementation details and are not part of the stable
interface. Use [`decode`](@ref), registered operations, and [`project`](@ref)
rather than depending on a particular rung.

## Inspect table policy without building a table

```@example technical_policy
using AIFloats

F8 = BinaryFormatOf(Binary8p4se)
F9 = Binary(9, 4, SIGNED, EXTENDED)

eager = AIFloats.table_policy(:Add, F8, F8, F8, RTE_SN)
adaptive = AIFloats.table_policy(:Add, F9, F9, F9, RTE_SN; nelems=65_536)
(eager, adaptive)
```

The returned `state` explains the decision. `shape = :A` means the matching
kernel call is eligible to fetch/build a table and gather from it; `shape = :B`
means it will compute each element through the scalar operation.

| `state` | Meaning |
|:--|:--|
| `:eager` | The operand-code bits fit the eager build band. The next call may fetch an existing table or build it immediately, regardless of array length. |
| `:adaptive_pending` | The signature fits the adaptive band but is not cached and has not processed enough cumulative elements to pay for a build. The call computes scalarly. |
| `:adaptive_earned` | The cached use count plus the supplied prospective `nelems` reaches the build threshold. A real call of that size would build and then use the table. Calling `table_policy` itself does not build it or change the count. |
| `:adaptive_cached` | An adaptively earned table has already been built and is available for a gather. |
| `:stochastic` | Stochastic projection depends on a random draw, so it is never represented by one deterministic result table. |
| `:over_byte_budget` | The complete table would exceed the configured per-table memory ceiling. |
| `:over_adaptive_band` | The operand-code space is beyond the largest band for which policy permits a table build. |

`cumulative` is the number of elements previously seen for that adaptive
signature, and `threshold` is the count required to earn its table. Supplying
`nelems` asks what a future call of that size would do without incrementing
`cumulative` or changing the cache.

## Inspect the table cache

`AIFloats.table_stats()` is one locked snapshot: its counts and its byte total
describe the same moment, which is why it exists rather than a pair of separate
queries.

```@example technical_stats
using AIFloats

s = AIFloats.table_stats()
(s.entries, s.bytes, s.by_arity)
```

`AIFloats.table_entries()` is a second locked snapshot, per entry, naming format
types and the mode names you write. Populate the cache through the ordinary
array path — `vmap` — rather than reaching for a private builder:

```@example technical_entries
using AIFloats

AIFloats.empty_tables!()

F = Binary(3, 2, SIGNED, FINITE)          # ΣK = 3: comfortably in the eager band
T = BinaryValue(F)
A = T[0.5, 1.0, 1.5]
vmap(:Negate, F, RTE_SN, A)               # this is what builds and caches the table

entries = AIFloats.table_entries()
[(e.op, e.result, e.operands, e.rounding, e.saturation, e.bytes) for e in entries]
```

!!! warning "Two snapshots are two moments"
    Each of `table_stats()` and `table_entries()` is internally coherent, but
    they are separate calls. The entry bytes sum to a separately obtained
    `table_stats().bytes` **only if the cache is not mutated between them** —
    another task's first array call is enough to break it.

    Where one coherent count-and-byte declaration is required, use
    [`conformance`](@ref): it derives its byte total from the very entry vector
    it captured.

```@example technical_coherent
using AIFloats

c = conformance()
(length(c.cached_specializations), c.cached_bytes)
```

## Compare the fast enclosure with the rigorous ladder

The performance switch is intended for differential testing. Both paths must
produce the same final code point:

```@example technical_oracle
using AIFloats

T = Binary8p4se
x = T(1.5)
fast = Exp(T, RTE_SN, x)

saved = AIFloats.FAST_ENCLOSURE[]
rigorous = try
    AIFloats.FAST_ENCLOSURE[] = false
    Exp(T, RTE_SN, x)
finally
    AIFloats.FAST_ENCLOSURE[] = saved
end

(fast, rigorous, codepoint(fast) == codepoint(rigorous))
```

This switch is diagnostic, not a request for weaker rounding. The fallback is
the correctly rounded MPFR enclosure ladder. In particular, no Quadmath
transcendental result is assumed to be correctly rounded.

## Examine raw codes and the total order

```@example technical_codes
using AIFloats

T = BinaryValue(Binary8p4se)
samples = T[fromcode(T, c) for c in (0x00, 0x01, 0x40, 0x7f, 0x80, 0xff)]
[(codepoint(x), decode(x), Class(x), AIFloats.order_key(x)) for x in samples]
```

Sorting uses the draft's NaN-first total order:

```@example technical_sort
using AIFloats

T = BinaryValue(Binary8p4se)
samples = T[fromcode(T, c) for c in (0x00, 0x01, 0x40, 0x7f, 0x80, 0xff)]
sort(samples)
```

## Query the conformance declaration

```@example technical_conformance
using AIFloats

c = conformance()
(draft_revision(), draft_identity(), typeof(c))
```

Use [`conformance_report`](@ref) for the human-readable declaration and
[`conformance_dict`](@ref) for structured tooling.

`draft_identity()` names the designated Interim Report — revision, date, URL,
and the SHA-256 of the PDF the implementation was compared against — alongside
the retained transliteration it was originally written from. The report is an
**unapproved draft**; its cover states it must not be used for conformance or
compliance purposes. `conformance()` reports what this package implements, in
the shape §4.6 describes. It is not IEEE approval, not a certification, and not
a compliance determination.

## Discover the operation register

The registry is queryable without touching its private storage:

```@example technical_registry
using AIFloats

ops = AIFloats.operations()
by_arity = Dict(a => count(o -> o.arity == a, ops) for a in 1:3)
(total = length(ops), by_arity = by_arity, add = AIFloats.operationinfo(:Add))
```

`AIFloats.operations()` and `AIFloats.operationinfo` are the supported entry
points; `OP_REGISTRY` itself is private and its shape is not part of the
interface. See [Operations](@ref operations).

```@meta
DocTestSetup = nothing
```
