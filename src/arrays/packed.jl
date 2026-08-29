# sub-byte packed storage
#
# Compute unpacked, store packed, convert at boundaries. PackedVector packs
# code points at K bits per element into 64-bit words; elementwise kernels run
# unpack → ordinary kernel → emit, tile by tile. In-place packed arithmetic is
# a deliberate scope limit (plan §13). Portable shift/mask splices only.

"""
    PackedVector{T<:BinaryValue} <: AbstractVector{T}

Bit-packed storage of datums at `K = BitwidthOf(T)` bits per element.
Construct with `PackedVector(A::AbstractVector{T})`; recover with `Vector(pv)`
or `collect(pv)`. Memory: `⌈n·K/64⌉` words against `n · sizeof(CodeType(T))`
unpacked.

It saves nothing when `K` equals the storage unit's width (K = 8 and K = 16),
where the packed layout is bit-for-bit the unpacked one; [`packing_saves`](@ref)
says so — a query, not a refusal, because both widths are equally the identity
and remain correct.
"""
struct PackedVector{T<:BinaryValue} <: AbstractVector{T}
    data::Vector{UInt64}
    n::Int
end

# element i at K bits/element begins at bit p = (i-1)K: word w = p ÷ 64
# (1-based) at offset off = p mod 64; elements with off + K > 64 splice
# across w, w+1
@inline _wordpos(K::Int, i::Int) = ((((i - 1) * K) >> 6) + 1, ((i - 1) * K) & 63)
@inline _crosses_word(off::Int, K::Int) = off + K > 64

# ---- the branch-free bulk extractor -----------------------------------------
# Reading element i as ONE unaligned 64-bit load starting at the byte holding
# its first bit removes both the cross-word splice and the branch that selects
# it: K ≤ KMAX = 16, so the element always lies inside those 64 bits. Measured
# at N = 65,536 against the word-indexed loop above: K = 5 26.3 → 19.3 µs,
# K = 8 18.7 → 6.9, K = 16 18.6 → 7.6. The branch alone was ~32% of the loop.
#
# The load reads up to 7 bytes past the element's own bytes, so it is valid
# only while that window stays inside `data`. `_safe_count` is that bound in
# closed form and the caller runs a scalar tail beyond it — the one part of
# this that must be exactly right, since an unsafe load past the buffer is the
# failure mode.
@inline function _safe_count(n::Int, K::Int, nbytes::Int)
    nbytes < 8 && return 0
    min(n, div((nbytes - 8) * 8 + 7, K) + 1)
end

"""
    _unpack_codes!(f, pv, n) -> nothing

Call `f(i, code)` for `i in 1:n` with each element's raw code, branch-free for
as long as the unaligned window is in bounds and word-indexed for the tail.
`f` is the caller's own store, so this serves both `collect` and the packed
table gather without materializing anything in between.
"""
@inline function _unpack_codes!(f::F, pv::PackedVector{T}, n::Int = pv.n) where {F,T}
    K = Int(BitwidthOf(T)); mask = _packmask(K); data = pv.data
    safe = _safe_count(n, K, length(data) * 8)
    GC.@preserve data begin
        base = pointer(data)
        @inbounds for i in 1:safe
            p = (i - 1) * K
            v = unsafe_load(Ptr{UInt64}(base + (p >> 3)))
            f(i, (v >> (p & 7)) & mask)
        end
    end
    @inbounds for i in (safe + 1):n
        w, off = _wordpos(K, i)
        c = data[w] >> off
        _crosses_word(off, K) && (c |= data[w + 1] << (64 - off))
        f(i, c & mask)
    end
    nothing
end
@inline _packmask(K::Int) = typemax(UInt64) >> (64 - K)        # by complement

function PackedVector(A::AbstractVector{T}) where {T<:BinaryValue}
    K = Int(BitwidthOf(T))
    n = length(A)
    words = zeros(UInt64, cld(n * K, 64))
    @inbounds for (i, v) in enumerate(A)
        w, off = _wordpos(K, i)
        c = UInt64(codepoint(v))
        words[w] |= c << off
        if _crosses_word(off, K)
            words[w + 1] |= c >> (64 - off)
        end
    end
    PackedVector{T}(words, n)
end

Base.size(pv::PackedVector) = (pv.n,)
Base.IndexStyle(::Type{<:PackedVector}) = IndexLinear()
Base.@propagate_inbounds function Base.getindex(pv::PackedVector{T}, i::Int) where {T}
    @boundscheck checkbounds(pv, i)
    K = Int(BitwidthOf(T))
    w, off = _wordpos(K, i)
    c = @inbounds pv.data[w] >> off
    if _crosses_word(off, K)
        c |= @inbounds(pv.data[w + 1]) << (64 - off)
    end
    rawvalue(BinaryFormatOf(T), CodeType(T)(c & _packmask(K)))
end
Base.@propagate_inbounds function Base.setindex!(pv::PackedVector{T}, v::T, i::Int) where {T}
    @boundscheck checkbounds(pv, i)
    K = Int(BitwidthOf(T))
    mask = _packmask(K)
    w, off = _wordpos(K, i)
    c = UInt64(codepoint(v))
    @inbounds pv.data[w] = (pv.data[w] & ~(mask << off)) | (c << off)
    if _crosses_word(off, K)
        hi = K - (64 - off)                                    # bits spilling into w+1
        @inbounds pv.data[w + 1] = (pv.data[w + 1] & ~(_packmask(hi))) | (c >> (64 - off))
    end
    pv
end
Base.similar(pv::PackedVector{T}) where {T} = PackedVector(Vector{T}(undef, pv.n))

# `collect`/`Vector` would otherwise walk `getindex`, recomputing the word
# position and taking the cross-word branch per element.
#
# Deliberately NOT a `Base.copyto!` method: every signature general enough to be
# useful is ambiguous with one of Base's (`PermutedDimsArray` among them), and
# this package keeps Aqua's ambiguity check clean. `collect` and `Vector` are
# the two entry points that matter and they are unambiguous.
function _unpack_into!(dest::AbstractVector{T}, pv::PackedVector{T}) where {T<:BinaryValue}
    length(dest) >= pv.n || throw(BoundsError(dest, pv.n))
    F = BinaryFormatOf(T); U = CodeType(T)
    _unpack_codes!((i, c) -> (@inbounds dest[i] = rawvalue(F, U(c)); nothing), pv)
    dest
end
Base.collect(pv::PackedVector{T}) where {T} = _unpack_into!(Vector{T}(undef, pv.n), pv)
Base.Vector(pv::PackedVector{T}) where {T} = collect(pv)

"""
    packing_saves(T) -> Bool

Whether `PackedVector{T}` is smaller than `Vector{T}`: `false` exactly when
`BitwidthOf(T)` equals the storage unit's width (K = 8, K = 16).
"""
packing_saves(::Type{T}) where {T<:BinaryValue} = Int(BitwidthOf(T)) < 8 * sizeof(CodeType(T))
packing_saves(::Type{F}) where {F<:Binary} = packing_saves(BinaryValue(F))
packing_saves(pv::PackedVector{T}) where {T} = packing_saves(T)

const PACK_TILE = 256

# vmap over packed storage: unpack a tile into a scratch, run the ordinary
# kernel (table-aware, threaded as it likes) into the output, repeat. The tile
# loop is a function barrier with the result format as a type parameter so
# the views reach vmap! statically. The stochastic path shares ONE rng across
# tiles, so the stream is the same as the unpacked call's.
function vmap(op::Symbol, fr::Type{<:Binary}, ρ::Projection, pv::PackedVector;
              rng::MaybeRNG = nothing)
    # the output datum type is a TYPE PARAMETER of the tile loop, so the views
    # reach vmap! statically (a `Vector{BinaryValue{FR, CodeType(FR)}}` spelled
    # inside the loop is not inferable)
    _vmap_packed(Val(op), BinaryValue(fr), ρ, pv, isstochastic(ρ) ? _resolve_rng(rng) : nothing)
end
vmap(op::Symbol, fr::Type{<:BinaryValue}, ρ::Projection, pv::PackedVector; kw...) =
    vmap(op, BinaryFormatOf(fr), ρ, pv; kw...)

function _vmap_packed(v::Val{op}, ::Type{OUT}, ρ::Projection, pv::PackedVector{T},
                      rng::MaybeRNG) where {op, OUT<:BinaryValue, T<:BinaryValue}
    out = Vector{OUT}(undef, pv.n)
    isempty(pv) && return out
    # DIRECT GATHER: when policy grants a unary table there is nothing for the
    # scratch tile to buy — the table is indexed by the code, and the code is
    # what the packed words already hold. Extract, index, store; no scratch, no
    # views, no per-tile vmap! dispatch. Measured 52.3 → 13 µs at K = 5,
    # N = 65,536 (implmentplan.md Step 6). The tiled adapter below stays for
    # stochastic ρ and for signatures policy declines to tabulate.
    if !isstochastic(ρ)
        FR, F1 = BinaryFormatOf(OUT), BinaryFormatOf(T)
        tbl = table_for(op, FR, F1, ρ)
        if tbl !== nothing
            # Bit positions are derived from i, never carried across iterations.
            # That was MEASURED against the obvious alternative: carrying the
            # word index and offset removes a multiply per element but adds a
            # loop-carried dependency, and the out-of-order engine loses more to
            # the serial chain than the arithmetic ever cost — 26.9 µs
            # recomputed vs 65.1 µs carried at K = 5, N = 65,536.
            _unpack_codes!((i, c) -> (@inbounds out[i] = rawvalue(FR, tbl[Int(c) + 1]); nothing), pv)
            return out
        end
    end
    buf = Vector{T}(undef, PACK_TILE)
    i = 1
    while i <= pv.n
        len = min(PACK_TILE, pv.n - i + 1)
        @inbounds for j in 1:len
            buf[j] = pv[i + j - 1]
        end
        vmap!(view(out, i:i + len - 1), v, ρ, view(buf, 1:len); rng)
        i += len
    end
    out
end
