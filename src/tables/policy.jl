# the two budgets, table_for vs get_table, table_policy introspection
#
# Two budgets, answering different questions with different units and failure
# modes:
#   · TABLE_MAX_BITS is *memory* — log2(bytes), compared AS BITS: computing
#     `1 << ΣK` to decide whether `1 << ΣK` is too large overflows silently
#     at ΣK ≥ 64 (a ternary K=16 signature is ΣK = 48; a hypothetical wider
#     grid would wrap). Its job is refusing an impossible allocation.
#   · TABLE_EAGER_BITS is *time* — log2(entries). A build costs one scalar
#     trip per entry, so entry count bounds first-call latency, regardless of
#     how comfortably the bytes fit in RAM.
#
# Where a budget declines, kernels run the scalar path per element instead of
# refusing: a table entry IS one trip through `_scalar_code`, and the fallback
# calls exactly that function per element — declining changes speed, never the
# answer. The suite asserts the equivalence rather than leaving it prose.

"""
Hard ceiling on a single table, as `log2(bytes)`. 25 = 32 MiB.

Compared **as bits**, never by materializing `1 << ΣK` — at large ΣK the shift
wraps and the impossible allocation would look free.
"""
const TABLE_MAX_BITS = Ref(25)

"""
Largest unary/binary table the package will *build*, as `log2(entries)`.
16 = 65,536 entries — the largest table the K ≤ 8 grid builds (8×8 binary),
and exactly a unary table for a K = 16 format.

A bound on **time**, not memory: each entry is one scalar-engine trip.

# Why not 18

Raising this to 18 would admit the K = 9 binary band (2^18 entries, 512 KiB,
comfortably inside `TABLE_MAX_BITS`), and at scale it is a large win — measured
at N = 65,536 the warm gather is ~22 µs whatever the operation, against a
compute call of 238 µs for Add and 2,082 µs for ArcTan2, with the build paying
for itself in 3–5 such calls.

It was measured and **declined** (implmentplan.md Step 9), because this gate
sees no element count. It decides from the format alone, so a single small call
pays the whole build:

| ArcTan2, K = 9 | band 16 | band 18 |
|---|---|---|
| N = 100 | 9.8 µs | 8,506 µs (864x slower) |
| N = 1,000 | 118 µs | 8,874 µs (75x slower) |
| N = 10,000 | 1,215 µs | 8,589 µs (7.1x slower) |

Trading a 864x regression on a one-shot call for a 95x win on a large one is
not a threshold decision, it is a missing mechanism. The mechanism already
exists for ternary signatures — `_ternary_table_for` takes `nelems` and has an
adaptive band gated on `TERNARY_BUILD_ELEMS` cumulative elements. Extending the
binary gate the same way is the way to claim this win; until then the band
stays where a first call can afford it.
"""
const TABLE_EAGER_BITS = Ref(16)

"""
ΣK up to which a **binary** table may build *adaptively*, once the signature has
earned it (default 18 bits = 256 Ki entries, at most 512 KiB per table).

The eager band (`TABLE_EAGER_BITS`) is what a *first* call can afford, because
that gate cannot see how long the call is. This band covers signatures that are
worth a table but too expensive to build speculatively — measured at ΣK = 18
(K = 9 binary), the build costs 542 µs for `Add` and 8.5 ms for `ArcTan2`, which
a single small call must never pay, while the warm gather is ~22 µs per 65,536
elements whatever the operation, against 238 µs (`Add`) to 2,082 µs (`ArcTan2`)
of computation.

Unary signatures never reach this band: ΣK = K ≤ `KMAX` = 16 is already eager.
"""
const TABLE_ADAPTIVE_BITS = Ref(18)

"""
Cumulative elements a binary signature must process before its table is built.

Break-even against the compute kernel at ΣK = 18 is 160 Ki elements for `Add`
and 270 Ki for `ArcTan2` (build cost divided by the per-element saving). The
default is ~4x the slower of those: a signature that has already processed a
million elements has spent far more on computation than the build will cost,
and everything after it is 10–95x faster. Deliberately conservative, and the
same shape of choice as `TERNARY_BUILD_ELEMS`.
"""
const TABLE_BUILD_ELEMS = Ref(1_000_000)

"""ΣK up to which a ternary table builds eagerly on first array call
(default 18 bits = 256 Ki entries — covers every all-K≤6 signature)."""
const TERNARY_EAGER_BITS = Ref(18)
"""ΣK up to which a ternary table may build adaptively once the signature has
processed `TERNARY_BUILD_ELEMS[]` elements (default 21 bits — the K=7 band).
Above this, ternary ops always run the compute kernel."""
const TERNARY_ADAPTIVE_BITS = Ref(21)
"""Cumulative element count at which an adaptive-band signature earns its table."""
const TERNARY_BUILD_ELEMS = Ref(2_000_000)
"""Byte budget for the ternary cache; least-recently-used tables evict first."""
const TERNARY_CACHE_BYTES = Ref(32 * 1024 * 1024)

@inline _sumK() = 0
@inline _sumK(::Type{F}, rest::Vararg{Any}) where {F<:Binary} =
    Int(BitwidthOf(F)) + _sumK(rest...)

"""`log2` of the bytes a table over `Fs` with results in `fr` would occupy."""
@inline tablebits(::Type{fr}, Fs::Vararg{Any,N}) where {fr<:Binary,N} =
    _sumK(Fs...) + trailing_zeros(sizeof(CodeType(fr)))
"""Would this table fit the byte budget? (Memory, not build time.)"""
@inline within_byte_budget(::Type{fr}, Fs::Vararg{Any,N}) where {fr<:Binary,N} =
    tablebits(fr, Fs...) <= TABLE_MAX_BITS[]

@noinline function _refuse_over_budget(op::Symbol, ::Type{fr},
                                       Fs::Vararg{Any,N}) where {fr<:Binary,N}
    throw(ArgumentError(
        "a table for $op⟨$(formatname(fr)); $(join(map(formatname, Fs), ", "))⟩ would be " *
        "2^$(_sumK(Fs...)) entries of $(sizeof(CodeType(fr))) byte(s) = " *
        "2^$(tablebits(fr, Fs...)) bytes, over the 2^$(TABLE_MAX_BITS[])-byte budget. " *
        "Array kernels fall back to the scalar path automatically; `get_table` does " *
        "not, because its contract is to return a table"))
end

"""Stochastic ρ is a distribution over R, never a table."""
@inline _check_tabulable(ρ::Projection) =
    isstochastic(ρ) && throw(ArgumentError("stochastic ρ $ρ is not tabulable: its result is a distribution, not a value"))

"""
    table_policy(op, fr, f1[, f2[, f3]], ρ; nelems=0)

Return `shape`, sizes, and the adaptive state the matching kernel policy would
observe. `nelems` is the size of a prospective array call; introspection reads
but never increments the cumulative-use counter.

Which shape an array call on this signature will take, and why — `:A` for the
table gather, `:B` for the per-element scalar path. Reads the same predicates
the kernels do, so it cannot drift from them.
"""
function table_policy(op::Symbol, ::Type{fr}, Fs::Vararg{Any};
                      nelems::Int = 0) where {fr<:Binary}
    nelems >= 0 || throw(ArgumentError("nelems must be nonnegative"))
    ρ = last(Fs)
    fs = Base.front(Fs)
    bits = _sumK(fs...)
    entries = bits >= 63 ? typemax(Int) : 1 << bits
    bytes = tablebits(fr, fs...) >= 63 ? typemax(Int) : 1 << tablebits(fr, fs...)
    isstochastic(ρ) && return (; shape=:B, entries, bytes, state=:stochastic,
        cumulative=0, threshold=0,
        reason="stochastic ρ is a distribution over R, never a table")
    !within_byte_budget(fr, fs...) && return (; shape=:B, entries, bytes,
        state=:over_byte_budget, cumulative=0, threshold=0,
        reason="over the 2^$(TABLE_MAX_BITS[])-byte budget")

    narg = length(fs)
    eager = narg == 3 ? TERNARY_EAGER_BITS[] : TABLE_EAGER_BITS[]
    adaptive = narg == 3 ? TERNARY_ADAPTIVE_BITS[] :
               narg == 2 ? TABLE_ADAPTIVE_BITS[] : eager
    bits <= eager && return (; shape=:A, entries, bytes, state=:eager,
        cumulative=0, threshold=0, reason="eager build band")
    bits > adaptive && return (; shape=:B, entries, bytes, state=:over_adaptive_band,
        cumulative=0, threshold=0, reason="beyond the adaptive build band")

    if narg == 2
        key = _bkey(op, fr, fs[1], fs[2], ρ)
        cached, used = lock(TABLE_LOCK) do
            haskey(tablecache(fr), key), get(TABLE_USE, key, 0)
        end
        threshold = TABLE_BUILD_ELEMS[]
    elseif narg == 3
        key = _tkey(op, fr, fs[1], fs[2], fs[3], ρ)
        cached, used = lock(TABLE_LOCK) do
            haskey(ternarycache(fr), key), get(TERNARY_USE, key, 0)
        end
        threshold = TERNARY_BUILD_ELEMS[]
    else
        return (; shape=:B, entries, bytes, state=:over_adaptive_band,
            cumulative=0, threshold=0, reason="unary signature beyond eager band")
    end
    cached && return (; shape=:A, entries, bytes, state=:adaptive_cached,
        cumulative=used, threshold, reason="adaptive table is cached")
    earned = used + nelems >= threshold
    (; shape=earned ? :A : :B, entries, bytes,
       state=earned ? :adaptive_earned : :adaptive_pending,
       cumulative=used, threshold,
       reason=earned ? "prospective call earns adaptive table" :
                       "adaptive table needs $(threshold - used) more cumulative elements")
end

# ---- fetch -------------------------------------------------------------------

"""
    get_table(op, fr, f1, [f2, [f3,]] ρ) -> Memory{CodeType(fr)}

Fetch (building and caching on first use) the complete result table for the
pure-ρ specialization `op⟨fr; f1…⟩ under ρ`: entry `c + 1` (unary),
`(c1 << K2) + c2 + 1` (binary), or `((c1 << K2 | c2) << K3) + c3 + 1` (ternary)
holds the result code point for those operand code points. Throws for
stochastic ρ, and throws when the table would exceed the byte budget — its
contract is to return a table, so it says so rather than returning `nothing`.
Callers that can fall back want [`table_for`](@ref).

`@noinline` by design: kernels call this once per array operation and index
the returned table in their hot loop.
"""
function get_table end

# Double-checked pattern: probe under lock, build OUTSIDE the lock (builds may
# run MPFR escalations), insert under lock; a racing duplicate build is benign
# and rare. Written once so the unary and binary fetches cannot acquire, probe,
# or insert differently from one another.
function _cached_table(::Type{fr}, key::TableKey,
                       build::F)::Memory{CodeType(fr)} where {fr<:Binary,F}
    cache = tablecache(fr)
    t = lock(() -> get(cache, key, nothing), TABLE_LOCK)
    t !== nothing && return t
    built = build()
    lock(() -> get!(cache, key, built), TABLE_LOCK)
end

@noinline function get_table(op::Symbol, ::Type{fr}, ::Type{f1},
                             ρ::Projection)::Memory{CodeType(fr)} where {fr<:Binary,f1<:Binary}
    _check_tabulable(ρ)
    within_byte_budget(fr, f1) || _refuse_over_budget(op, fr, f1)
    _cached_table(fr, _bkey(op, fr, f1, ρ), () -> _build_unary(op, fr, f1, ρ))
end
@noinline function get_table(op::Symbol, ::Type{fr}, ::Type{f1}, ::Type{f2},
                             ρ::Projection)::Memory{CodeType(fr)} where {fr<:Binary,f1<:Binary,f2<:Binary}
    _check_tabulable(ρ)
    within_byte_budget(fr, f1, f2) || _refuse_over_budget(op, fr, f1, f2)
    _cached_table(fr, _bkey(op, fr, f1, f2, ρ), () -> _build_binary(op, fr, f1, f2, ρ))
end
@noinline function get_table(op::Symbol, ::Type{fr}, ::Type{f1}, ::Type{f2}, ::Type{f3},
                             ρ::Projection)::Memory{CodeType(fr)} where {fr<:Binary,f1<:Binary,f2<:Binary,f3<:Binary}
    _check_tabulable(ρ)
    within_byte_budget(fr, f1, f2, f3) || _refuse_over_budget(op, fr, f1, f2, f3)
    key = _tkey(op, fr, f1, f2, f3, ρ)
    t = _ternary_probe(fr, key)
    t !== nothing && return t
    _ternary_insert!(fr, key, _build_ternary(op, fr, f1, f2, f3, ρ))   # build outside the lock
end

"""
    table_for(op, fr, f1[, f2], ρ) -> Union{Nothing, Memory{CodeType(fr)}}

The kernel-facing gate for unary and binary specializations: the table if
policy grants one, `nothing` if the caller should run the scalar path per
element.

Separate from [`get_table`](@ref) on purpose — **one name per question.**
`get_table`'s contract is "return the table", so it throws when it cannot
honour that. `table_for` asks "should there be a table at all", and answers
`nothing` without prejudice. Its `Union` return costs nothing because kernels
call it once per array operation and branch outside the loop.
"""
@noinline function table_for(op::Symbol, ::Type{fr}, ::Type{f1},
                             ρ::Projection)::Union{Nothing,Memory{CodeType(fr)}} where {fr<:Binary,f1<:Binary}
    isstochastic(ρ) && return nothing
    (_sumK(f1) <= TABLE_EAGER_BITS[] && within_byte_budget(fr, f1)) || return nothing
    get_table(op, fr, f1, ρ)
end
@noinline function table_for(op::Symbol, ::Type{fr}, ::Type{f1}, ::Type{f2},
                             ρ::Projection)::Union{Nothing,Memory{CodeType(fr)}} where {fr<:Binary,f1<:Binary,f2<:Binary}
    isstochastic(ρ) && return nothing
    (_sumK(f1, f2) <= TABLE_EAGER_BITS[] && within_byte_budget(fr, f1, f2)) || return nothing
    get_table(op, fr, f1, f2, ρ)
end

"""
    table_for(op, fr, f1, f2, ρ, nelems) -> Union{Nothing, Memory}

The kernel-facing binary policy gate, called once per array operation with the
call's element count — the same shape as [`_ternary_table_for`](@ref), and for
the same reason.

Eager band (ΣK ≤ `TABLE_EAGER_BITS[]`): fetch or build now. Adaptive band
(≤ `TABLE_ADAPTIVE_BITS[]`): return the cached table if one exists, otherwise
accumulate `nelems` against the signature and build only once it has earned
`TABLE_BUILD_ELEMS[]`. Beyond the adaptive band: always `nothing`.

The element count is the whole point. The five-argument method above decides
from the formats alone, so it must stay where a first call can afford the
build; this one knows how much work the caller is actually bringing, so it can
admit signatures whose tables cost milliseconds.

!!! note "Aggregate cache size"
    Like the eager cache, the adaptive band is bounded per table (by
    `within_byte_budget`) but not in aggregate — the binary caches have no LRU.
    In practice `TABLE_BUILD_ELEMS` is the bound that matters: filling the cache
    with adaptive tables requires processing a million elements *per distinct
    signature*. An aggregate byte cap belongs to the eager and adaptive bands
    together, and is deliberately left to a separate change.
"""
@noinline function table_for(op::Symbol, ::Type{fr}, ::Type{f1}, ::Type{f2},
                             ρ::Projection,
                             nelems::Int)::Union{Nothing,Memory{CodeType(fr)}} where {fr<:Binary,f1<:Binary,f2<:Binary}
    isstochastic(ρ) && return nothing
    within_byte_budget(fr, f1, f2) || return nothing
    ΣK = _sumK(f1, f2)
    ΣK <= TABLE_EAGER_BITS[] && return get_table(op, fr, f1, f2, ρ)
    ΣK <= TABLE_ADAPTIVE_BITS[] || return nothing
    key = _bkey(op, fr, f1, f2, ρ)
    cache = tablecache(fr)
    hit = lock(() -> get(cache, key, nothing), TABLE_LOCK)
    hit === nothing || return hit
    n = lock(() -> (TABLE_USE[key] = get(TABLE_USE, key, 0) + nelems), TABLE_LOCK)
    n >= TABLE_BUILD_ELEMS[] || return nothing
    get_table(op, fr, f1, f2, ρ)                  # builds and caches under the lock
end

"""
    _ternary_table_for(op, fr, f1, f2, f3, ρ, nelems) -> Union{Nothing, Memory}

The kernel-facing ternary policy gate, called once per array operation with the
call's element count. Eager band (ΣK ≤ `TERNARY_EAGER_BITS[]`): fetch/build
now. Adaptive band (≤ `TERNARY_ADAPTIVE_BITS[]`): return the cached table if
present, otherwise accumulate `nelems` against the signature and build only
once it has earned `TERNARY_BUILD_ELEMS[]`. Beyond the adaptive band: always
`nothing` — the compute kernel is the right tradeoff there.
"""
@noinline function _ternary_table_for(op::Symbol, ::Type{fr}, ::Type{f1}, ::Type{f2},
                                      ::Type{f3}, ρ::Projection,
                                      nelems::Int)::Union{Nothing,Memory{CodeType(fr)}} where {fr<:Binary,f1<:Binary,f2<:Binary,f3<:Binary}
    isstochastic(ρ) && return nothing
    # the byte budget is the outer bound; the eager/adaptive bands are the
    # *build-cost* policy inside it — both must pass, and they are not
    # redundant: 3 × K=7 is 2^21 entries, inside the adaptive band and inside
    # the byte budget, while 3 × K=16 is 2^48 entries and fails the byte
    # budget long before any band is consulted
    within_byte_budget(fr, f1, f2, f3) || return nothing
    ΣK = _sumK(f1, f2, f3)
    ΣK <= TERNARY_EAGER_BITS[] && return get_table(op, fr, f1, f2, f3, ρ)
    ΣK <= TERNARY_ADAPTIVE_BITS[] || return nothing
    key = _tkey(op, fr, f1, f2, f3, ρ)
    hit = _ternary_probe(fr, key)
    hit !== nothing && return hit
    n = lock(() -> (TERNARY_USE[key] = get(TERNARY_USE, key, 0) + nelems), TABLE_LOCK)
    n >= TERNARY_BUILD_ELEMS[] || return nothing
    _ternary_insert!(fr, key, _build_ternary(op, fr, f1, f2, f3, ρ))
end

# tables/policy.jl
