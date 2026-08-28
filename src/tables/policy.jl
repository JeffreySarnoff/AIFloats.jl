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
"""
const TABLE_EAGER_BITS = Ref(16)

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
    table_policy(op, fr, f1[, f2[, f3]], ρ) -> (; shape, entries, bytes, reason)

Which shape an array call on this signature will take, and why — `:A` for the
table gather, `:B` for the per-element scalar path. Reads the same predicates
the kernels do, so it cannot drift from them.
"""
function table_policy(op::Symbol, ::Type{fr}, Fs::Vararg{Any}) where {fr<:Binary}
    ρ = last(Fs)
    fs = Base.front(Fs)
    bits = _sumK(fs...)
    entries = bits >= 63 ? typemax(Int) : 1 << bits
    bytes = tablebits(fr, fs...) >= 63 ? typemax(Int) : 1 << tablebits(fr, fs...)
    reason =
        isstochastic(ρ) ? "stochastic ρ is a distribution over R, never a table" :
        !within_byte_budget(fr, fs...) ? "over the 2^$(TABLE_MAX_BITS[])-byte budget" :
        length(fs) == 3 ?
            (bits <= TERNARY_EAGER_BITS[] ? "ternary eager band" :
             bits <= TERNARY_ADAPTIVE_BITS[] ? "ternary adaptive band: needs $(TERNARY_BUILD_ELEMS[]) elements first" :
             "beyond the ternary adaptive band") :
        bits <= TABLE_EAGER_BITS[] ? "within the 2^$(TABLE_EAGER_BITS[])-entry build band" :
                                     "over the 2^$(TABLE_EAGER_BITS[])-entry build band"
    granted = !isstochastic(ρ) && within_byte_budget(fr, fs...) &&
              (length(fs) == 3 ? bits <= TERNARY_ADAPTIVE_BITS[] : bits <= TABLE_EAGER_BITS[])
    (; shape = granted ? :A : :B, entries, bytes, reason)
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
    key = TableKey(op, _fkey(fr), _fkey(f1), (0, 0, 0, 0), _rmname(ρ), _smname(ρ))
    _cached_table(fr, key, () -> _build_unary(op, fr, f1, ρ))
end
@noinline function get_table(op::Symbol, ::Type{fr}, ::Type{f1}, ::Type{f2},
                             ρ::Projection)::Memory{CodeType(fr)} where {fr<:Binary,f1<:Binary,f2<:Binary}
    _check_tabulable(ρ)
    within_byte_budget(fr, f1, f2) || _refuse_over_budget(op, fr, f1, f2)
    key = TableKey(op, _fkey(fr), _fkey(f1), _fkey(f2), _rmname(ρ), _smname(ρ))
    _cached_table(fr, key, () -> _build_binary(op, fr, f1, f2, ρ))
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
