# the table cache: value keys, one cache per code unit, one lock
#
# A pure (non-stochastic) specialization of a registry op is a total function
# on 2^ΣK code points, so its complete result table is buildable and cacheable.
# A table entry is a *result code point*, so its width is `CodeType(fr)`; one
# Dict holding both widths would return a `Union{Memory{UInt8},Memory{UInt16}}`
# and put a type check inside every hot loop. The cache is therefore selected
# by DISPATCH on the result representation, never by a branch on K.

"""
Value key for the unary/binary table cache: op + format parameters + ρ names —
all plain values, so probing the cache is type-stable and allocation-free.
"""
struct TableKey
    op::Symbol
    fr::NTuple{4,Int}          # result format (K, P, signed, extended)
    f1::NTuple{4,Int}          # first operand format
    f2::NTuple{4,Int}          # second operand format; (0,0,0,0) for unary
    rm::Symbol                 # rounding-mode type name
    sm::Symbol                 # saturation-mode type name
end

_fkey(::Type{Binary{K,P,S,D}}) where {K,P,S,D} = (Int(K), Int(P), Int(S), Int(D))
# and back: the snapshot functions report FORMAT TYPES, never the stored tuple
_unfkey(t::NTuple{4,Int}) = Binary(Int8(t[1]), Int8(t[2]), Bool(t[3]), Bool(t[4]))
# the key stores the singleton's TYPE name (`:ρRTE`); a public snapshot reports
# the name a caller actually writes (`:RTE`)
_publicmode(n::Symbol) = (s = String(n); Symbol(startswith(s, 'ρ') ? chop(s; head = 1, tail = 0) : s))
_rmname(ρ::Projection) = nameof(typeof(RoundOf(ρ)))
_smname(ρ::Projection) = nameof(typeof(SatOf(ρ)))

const TABLE_CACHE8  = Dict{TableKey,Memory{UInt8}}()
const TABLE_CACHE16 = Dict{TableKey,Memory{UInt16}}()
# cumulative elements seen per binary signature, for the adaptive band (the
# unary band needs none: ΣK = K ≤ KMAX = 16 is always inside the eager band)
const TABLE_USE  = Dict{TableKey,Int}()
const TABLE_LOCK = ReentrantLock()

"""The unary/binary table cache holding results coded in this unit."""
@inline tablecache(::Type{UInt8})  = TABLE_CACHE8
@inline tablecache(::Type{UInt16}) = TABLE_CACHE16
@inline tablecache(::Type{F}) where {F<:Binary} = tablecache(CodeType(F))

# ---- ternary tables ----------------------------------------------------------
# A ternary table is 2^(K1+K2+K3) entries: 512 B at K=3, 256 KiB at K=6, 2 MiB
# at K=7, 16 MiB at K=8. The eager band builds on first array use; the adaptive
# band builds only for demonstrably hot signatures and evicts LRU under a byte
# budget; beyond it the compute kernel is the right tradeoff.

"""Value key for a ternary table: op + result + three operand formats + ρ."""
struct TernaryKey
    op::Symbol
    fr::NTuple{4,Int}
    f1::NTuple{4,Int}
    f2::NTuple{4,Int}
    f3::NTuple{4,Int}
    rm::Symbol
    sm::Symbol
end

const CachedTableKey = Union{TableKey,TernaryKey}

@inline _cache_key_sort(k::TableKey) =
    (String(k.op), k.fr, k.f1, k.f2, (0, 0, 0, 0), String(k.rm), String(k.sm))
@inline _cache_key_sort(k::TernaryKey) =
    (String(k.op), k.fr, k.f1, k.f2, k.f3, String(k.rm), String(k.sm))

mutable struct TernaryEntry{U<:Unsigned}
    const tbl::Memory{U}
    tick::Int                  # LRU stamp (monotone; larger = more recent)
end

const TERNARY_CACHE8  = Dict{TernaryKey,TernaryEntry{UInt8}}()
const TERNARY_CACHE16 = Dict{TernaryKey,TernaryEntry{UInt16}}()
const TERNARY_USE  = Dict{TernaryKey,Int}()   # cumulative elements seen (adaptive band)
const TERNARY_TICK = Ref(0)

"""The ternary table cache holding results coded in this unit."""
@inline ternarycache(::Type{UInt8})  = TERNARY_CACHE8
@inline ternarycache(::Type{UInt16}) = TERNARY_CACHE16
@inline ternarycache(::Type{F}) where {F<:Binary} = ternarycache(CodeType(F))

"""The unary/binary cache key. Spelled once; `get_table` and the adaptive
gate must agree on it exactly or the counter would track a key nothing looks
up."""
_bkey(op::Symbol, ::Type{fr}, ::Type{f1}, ::Type{f2},
      ρ::Projection) where {fr<:Binary,f1<:Binary,f2<:Binary} =
    TableKey(op, _fkey(fr), _fkey(f1), _fkey(f2), _rmname(ρ), _smname(ρ))
_bkey(op::Symbol, ::Type{fr}, ::Type{f1},
      ρ::Projection) where {fr<:Binary,f1<:Binary} =
    TableKey(op, _fkey(fr), _fkey(f1), (0, 0, 0, 0), _rmname(ρ), _smname(ρ))

_tkey(op::Symbol, ::Type{fr}, ::Type{f1}, ::Type{f2}, ::Type{f3},
      ρ::Projection) where {fr<:Binary,f1<:Binary,f2<:Binary,f3<:Binary} =
    TernaryKey(op, _fkey(fr), _fkey(f1), _fkey(f2), _fkey(f3), _rmname(ρ), _smname(ρ))

# Cache probe that also refreshes the LRU stamp — a hit must always count as a
# use, so the direct fetch and the adaptive gate share this one path.
function _ternary_probe(::Type{fr}, key::TernaryKey) where {fr<:Binary}
    lock(TABLE_LOCK) do
        e = get(ternarycache(fr), key, nothing)
        e === nothing ? nothing : (e.tick = (TERNARY_TICK[] += 1); e.tbl)
    end
end

# Insert under the byte budget, evicting least-recently-used ternary tables
# first. The new table always inserts (even alone over budget: the caller
# earned it; the budget then simply holds this one table).
function _ternary_insert!(::Type{fr}, key::TernaryKey,
                          tbl::Memory{U}) where {fr<:Binary,U<:Unsigned}
    lock(TABLE_LOCK) do
        cache = ternarycache(fr)
        e = get(cache, key, nothing)
        e !== nothing && return e.tbl                        # racing duplicate build
        budget = TERNARY_CACHE_BYTES[]
        newbytes = length(tbl) * sizeof(U)
        # eviction spans BOTH ternary caches — the byte budget is a statement
        # about memory held, and memory does not care which code unit holds it.
        # The victim is the globally least-recent entry of EITHER cache; an
        # earlier version selected only from the current result-width cache,
        # so a UInt16 table could never be evicted by a UInt8 insert (and vice
        # versa) and the budget was silently exceeded.
        while !(isempty(TERNARY_CACHE8) && isempty(TERNARY_CACHE16)) &&
              _bytes_of(TERNARY_CACHE8) + _bytes_of(TERNARY_CACHE16) + newbytes > budget
            _evict_oldest_ternary!()
        end
        cache[key] = TernaryEntry{U}(tbl, TERNARY_TICK[] += 1)
        tbl
    end
end

# the least-recently-used entry across both ternary caches (caller holds the lock)
function _evict_oldest_ternary!()
    t8 = isempty(TERNARY_CACHE8) ? typemax(Int) : minimum(e -> e.tick, values(TERNARY_CACHE8))
    t16 = isempty(TERNARY_CACHE16) ? typemax(Int) : minimum(e -> e.tick, values(TERNARY_CACHE16))
    if t8 <= t16
        delete!(TERNARY_CACHE8, argmin(k -> TERNARY_CACHE8[k].tick, keys(TERNARY_CACHE8)))
    else
        delete!(TERNARY_CACHE16, argmin(k -> TERNARY_CACHE16[k].tick, keys(TERNARY_CACHE16)))
    end
    nothing
end

# ---- cache accounting --------------------------------------------------------
# Every consumer goes through these: with the caches split by code unit, a
# consumer naming one directly under-reports by exactly the half it forgot —
# and one future consumer is `conformance()`, whose job is truthful totals.

_bytes_of(d::Dict{TableKey,<:Memory}) =
    sum(t -> length(t) * sizeof(eltype(t)), values(d); init = 0)
_bytes_of(d::Dict{TernaryKey,<:TernaryEntry}) =
    sum(e -> length(e.tbl) * sizeof(eltype(e.tbl)), values(d); init = 0)

# ---- the two coherent snapshots ---------------------------------------------
# ONE lock per snapshot, not one per component. `table_bytes()`,
# `table_count()` and `ternary_count()` each took the lock separately, so a
# caller assembling a report from all three could describe three different
# moments of a cache that another task was filling — and then print totals that
# do not add up. Both functions below take the lock once and read everything
# inside it (improveapi3.md §6 Phase 5.7).

# a unary entry is stored in the binary cache with an all-zero f2 sentinel
_binary_arity(k::TableKey) = k.f2 === (0, 0, 0, 0) ? :unary : :binary

"""
    table_stats() -> NamedTuple

One coherent snapshot of the table caches, taken under a single lock.

```julia
(entries, bytes, by_arity = (unary, binary, ternary),
 by_codeunit = (uint8, uint16), adaptive_signatures, ternary_budget)
```

`entries` is the number of cached specializations and `bytes` the memory they
hold; the `by_arity` and `by_codeunit` breakdowns each sum to `entries`.
`adaptive_signatures` counts signatures with a nonzero cumulative-use counter,
which is what the adaptive band builds against. `ternary_budget` is the current
per-table byte cap.

For per-entry detail, see [`table_entries`](@ref); to clear, [`empty_tables!`](@ref).

# Examples

```jldoctest
julia> AIFloats.empty_tables!();

julia> AIFloats.table_stats().entries
0
```
"""
function table_stats()
    lock(TABLE_LOCK) do
        u8 = length(TABLE_CACHE8) + length(TERNARY_CACHE8)
        u16 = length(TABLE_CACHE16) + length(TERNARY_CACHE16)
        tern = length(TERNARY_CACHE8) + length(TERNARY_CACHE16)
        un = count(k -> _binary_arity(k) === :unary, keys(TABLE_CACHE8)) +
             count(k -> _binary_arity(k) === :unary, keys(TABLE_CACHE16))
        bin = (length(TABLE_CACHE8) + length(TABLE_CACHE16)) - un
        (entries = u8 + u16,
         bytes = _bytes_of(TABLE_CACHE8) + _bytes_of(TABLE_CACHE16) +
                 _bytes_of(TERNARY_CACHE8) + _bytes_of(TERNARY_CACHE16),
         by_arity = (unary = un, binary = bin, ternary = tern),
         by_codeunit = (uint8 = u8, uint16 = u16),
         adaptive_signatures = count(>(0), values(TABLE_USE)) +
                               count(>(0), values(TERNARY_USE)),
         ternary_budget = 1 << TABLE_MAX_BITS[])
    end
end

_entry_nt(k::TableKey, nbytes::Int) =
    (op = k.op, arity = _binary_arity(k), result = _unfkey(k.fr),
     operands = _binary_arity(k) === :unary ? (_unfkey(k.f1),) :
                                              (_unfkey(k.f1), _unfkey(k.f2)),
     rounding = _publicmode(k.rm), saturation = _publicmode(k.sm), bytes = nbytes)
_entry_nt(k::TernaryKey, nbytes::Int) =
    (op = k.op, arity = :ternary, result = _unfkey(k.fr),
     operands = (_unfkey(k.f1), _unfkey(k.f2), _unfkey(k.f3)),
     rounding = _publicmode(k.rm), saturation = _publicmode(k.sm), bytes = nbytes)

# The public shape of one cached-table record. A plain comment, not a
# docstring: a docstring here would sit between `table_entries`'s own
# docstring and its definition and silently retarget it.
const TableEntry = @NamedTuple{op::Symbol, arity::Symbol, result::DataType,
                               operands::Tuple, rounding::Symbol,
                               saturation::Symbol, bytes::Int}

"""
    table_entries() -> Vector{AIFloats.TableEntry}

Per-entry detail for every cached table, taken under a single lock and sorted
by operation, arity, result format, operand formats, rounding, then saturation.

Each element is a public named tuple naming FORMAT TYPES, not the internal key
struct:

```julia
(op, arity, result, operands, rounding, saturation, bytes)
```

The `bytes` field sums to [`table_stats`](@ref)`().bytes`.
"""
function table_entries()::Vector{TableEntry}
    lock(TABLE_LOCK) do
        out = Any[]
        for d in (TABLE_CACHE8, TABLE_CACHE16)
            for (k, t) in d
                push!(out, (_cache_key_sort(k), _entry_nt(k, length(t) * sizeof(eltype(t)))))
            end
        end
        for d in (TERNARY_CACHE8, TERNARY_CACHE16)
            for (k, e) in d
                push!(out, (_cache_key_sort(k),
                            _entry_nt(k, length(e.tbl) * sizeof(eltype(e.tbl)))))
            end
        end
        sort!(out; by = first)
        TableEntry[nt for (_, nt) in out]
    end
end

"""Drop every cached table and adaptive counter (they rebuild lazily on next use)."""
empty_tables!() = lock(TABLE_LOCK) do
    empty!(TABLE_CACHE8); empty!(TABLE_CACHE16); empty!(TABLE_USE)
    empty!(TERNARY_CACHE8); empty!(TERNARY_CACHE16); empty!(TERNARY_USE)
    TERNARY_TICK[] = 0
    nothing
end

# tables/cache.jl
