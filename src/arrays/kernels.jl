# vmap/vmap! — the array surface
#
# Two hot-loop shapes, written once and instantiated by the registry:
#   Shape A (gather):  out[i] = tbl[key(a[i]…)]   — pure ρ, table affordable
#   Shape B (compute): per-element scalar path    — everything else
# The table getter is @noinline and called ONCE per array call, hoisted out of
# the loop; loop bodies index a local `Memory` with no dict lookups, locks, or
# global loads per element.
#
# Every arity chooses between the shapes; none assumes Shape A. The choice is
# policy, never correctness: a table entry is one trip through the scalar
# path, and Shape B calls that same path per element — the two shapes cannot
# disagree, and the suite measures it rather than assuming it.

# one indirection serving builders and both kernel shapes: the registry ops go
# through apply_op (ωeval + finish); Convert has no ω-semantics and is a bare
# projection of its decoded operand
@inline _kernel_result(op::Val, ::Type{FR}, ρ::Projection, R::Int,
                       xs...) where {FR<:Binary} = apply_op(op, FR, ρ, R, xs...)
@inline _kernel_result(::Val{:Convert}, ::Type{FR}, ρ::Projection, R::Int,
                       x) where {FR<:Binary} = project(FR, ρ, x; R)

"""
Minimum element count before a pure-ρ **compute** loop threads.

Only the compute kernels consult this. The Shape-A gather is a flat indexed
loop over a memoized table and is never threaded: measured at K = 8 it runs at
memory bandwidth already, and 1 vs 4 threads is 1.00x at every N from 1 Ki to
64 Ki.

Refit from measurement (implmentplan.md Step 9), 4 threads, K = 12 compute,
speedup of 4 threads over 1:

| N | Add | Log |
|---|---|---|
| 64 | 0.47x | 0.77x |
| 128 | 0.88x | 1.30x |
| 256 | 1.41x | 2.23x |
| 1024 | 2.66x | 3.19x |
| 4096 | 3.58x | 2.10x |
| 65536 | 3.83x | 3.98x |

The true crossover is N ≈ 128–256 for both a cheap (Add) and an expensive (Log)
op — within a factor of two of each other, so ONE threshold serves both and no
per-op cost class is warranted. 1024 sits comfortably past the crossover,
leaving margin for machines with fewer cores or slower task spawn than the
one measured. The previous value, 1 << 15, left 2.7–3.8x unclaimed on every
array between the crossover and 32 Ki.
"""
const THREAD_MIN_ELEMS = Ref(1 << 10)
"""Master switch for threaded compute loops, at every arity."""
const THREADED_KERNELS = Ref(true)

# the threading predicate, written ONCE — two copies would drift.
# `inds isa AbstractUnitRange` is not a formality: Threads.@threads partitions
# by index arithmetic, so a non-unit-range eachindex (CartesianIndices, an
# offset axis) must stay on the sequential path.
@inline _should_thread(inds) =
    THREADED_KERNELS[] && Threads.nthreads() > 1 &&
    length(inds) >= THREAD_MIN_ELEMS[] && inds isa AbstractUnitRange

"""
    vmap!(dest, op::Symbol, ρ, A[, B[, C]]; rng) -> dest
    vmap(op::Symbol, fr, ρ, A...; rng) -> Array

Elementwise draft operation over arrays of datums, projecting into `dest`'s
(or `fr`'s) format under ρ. Pure ρ runs the Shape-A table gather whenever
policy grants a table; stochastic ρ (and untabled signatures) run the scalar
path per element. The stochastic loop is sequential by construction — it draws
from a single rng stream, so seeded results are reproducible in index order
and never depend on the scheduler.
"""
function vmap! end

@inline function vmap!(dest::AbstractArray{<:BinaryValue}, op::Symbol, ρ::Projection,
                       As::AbstractArray{<:BinaryValue}...; rng::MaybeRNG = nothing)
    _validate_runtime_op(:vmap!, op, length(As))     # the same boundary as `vmap`
    vmap!(dest, Val(op), ρ, As...; rng)
end

# ---- Shape A: unary gather
function vmap!(dest::AbstractArray{BinaryValue{FR,UR}}, v::Val{op}, ρ::Projection,
               A::AbstractArray{BinaryValue{F1,U1}};
               rng::MaybeRNG = nothing) where {op,FR,UR,F1,U1}
    axes(dest) == axes(A) || throw(DimensionMismatch("dest and A must share axes"))
    isstochastic(ρ) && return _vmap_scalar!(dest, v, FR, ρ, A; rng)
    tbl = table_for(op, FR, F1, ρ)                       # hoisted; @noinline
    tbl === nothing && return _vmap_compute!(dest, v, FR, ρ, A)
    @inbounds for i in eachindex(dest, A)
        dest[i] = _rawvalue(FR, tbl[Int(codepoint(A[i])) + 1])
    end
    dest
end

# ---- Shape A: binary gather, index = (c1 << K2) | c2
function vmap!(dest::AbstractArray{BinaryValue{FR,UR}}, v::Val{op}, ρ::Projection,
               A::AbstractArray{BinaryValue{F1,U1}}, B::AbstractArray{BinaryValue{F2,U2}};
               rng::MaybeRNG = nothing) where {op,FR,UR,F1,U1,F2,U2}
    axes(dest) == axes(A) == axes(B) ||
        throw(DimensionMismatch("dest, A, B must share axes"))
    isstochastic(ρ) && return _vmap_scalar!(dest, v, FR, ρ, A, B; rng)
    tbl = table_for(op, FR, F1, F2, ρ, length(dest))     # hoisted; @noinline
    tbl === nothing && return _vmap_compute!(dest, v, FR, ρ, A, B)
    K2 = Int(BitwidthOf(F2))
    @inbounds for i in eachindex(dest, A, B)
        dest[i] = _rawvalue(FR, tbl[(Int(codepoint(A[i])) << K2) + Int(codepoint(B[i])) + 1])
    end
    dest
end

# ---- ternary: gather where policy grants (eager/adaptive bands), compute else
function vmap!(dest::AbstractArray{BinaryValue{FR,UR}}, v::Val{op}, ρ::Projection,
               A::AbstractArray{BinaryValue{F1,U1}}, B::AbstractArray{BinaryValue{F2,U2}},
               C::AbstractArray{BinaryValue{F3,U3}};
               rng::MaybeRNG = nothing) where {op,FR,UR,F1,U1,F2,U2,F3,U3}
    axes(dest) == axes(A) == axes(B) == axes(C) ||
        throw(DimensionMismatch("operand axes must match"))
    isstochastic(ρ) && return _vmap_scalar!(dest, v, FR, ρ, A, B, C; rng)
    tbl = _ternary_table_for(op, FR, F1, F2, F3, ρ, length(dest))   # hoisted; @noinline
    if tbl !== nothing
        K2, K3 = Int(BitwidthOf(F2)), Int(BitwidthOf(F3))
        @inbounds for i in eachindex(dest, A, B, C)
            idx = ((Int(codepoint(A[i])) << K2 | Int(codepoint(B[i]))) << K3) +
                  Int(codepoint(C[i])) + 1
            dest[i] = _rawvalue(FR, tbl[idx])
        end
        return dest
    end
    _vmap_compute!(dest, v, FR, ρ, A, B, C)
end

# ---- Shape B, pure ρ: the compute loops that thread.
# Separate from _vmap_scalar! on purpose: that function serves stochastic ρ
# and must stay sequential, and the sequential requirement is carried by WHICH
# FUNCTION you are in, not by a branch someone can later hoist. R = 0 is
# passed literally: under pure ρ _drawR returns 0 without touching an rng.
# Threading safety at rung 2/3 rests on setprecision's function form being
# ScopedValue-backed (task-local) on Julia ≥ 1.12.
@inline function _vmap_compute!(dest, v::Val, ::Type{FR}, ρ::Projection,
                                A) where {FR<:Binary}
    inds = eachindex(dest, A)
    if _should_thread(inds)
        Threads.@threads for i in inds
            @inbounds dest[i] = _kernel_result(v, FR, ρ, 0, decode(A[i]))
        end
        return dest
    end
    @inbounds for i in inds
        dest[i] = _kernel_result(v, FR, ρ, 0, decode(A[i]))
    end
    dest
end
@inline function _vmap_compute!(dest, v::Val, ::Type{FR}, ρ::Projection,
                                A, B) where {FR<:Binary}
    inds = eachindex(dest, A, B)
    if _should_thread(inds)
        Threads.@threads for i in inds
            @inbounds dest[i] = _kernel_result(v, FR, ρ, 0, decode(A[i]), decode(B[i]))
        end
        return dest
    end
    @inbounds for i in inds
        dest[i] = _kernel_result(v, FR, ρ, 0, decode(A[i]), decode(B[i]))
    end
    dest
end
@inline function _vmap_compute!(dest, v::Val, ::Type{FR}, ρ::Projection,
                                A, B, C) where {FR<:Binary}
    inds = eachindex(dest, A, B, C)
    if _should_thread(inds)
        Threads.@threads for i in inds
            @inbounds dest[i] = _kernel_result(v, FR, ρ, 0,
                                               decode(A[i]), decode(B[i]), decode(C[i]))
        end
        return dest
    end
    @inbounds for i in inds
        dest[i] = _kernel_result(v, FR, ρ, 0, decode(A[i]), decode(B[i]), decode(C[i]))
    end
    dest
end

# ---- the sequential stochastic kernel (single rng stream, index order)
function _vmap_scalar!(dest, v::Val, ::Type{FR}, ρ::Projection, A;
                       rng::MaybeRNG = nothing) where {FR<:Binary}
    rr = _resolve_rng(rng)                      # hoisted: resolved once per call
    @inbounds for i in eachindex(dest, A)
        dest[i] = _kernel_result(v, FR, ρ, _drawR(ρ, rr, nothing), decode(A[i]))
    end
    dest
end
function _vmap_scalar!(dest, v::Val, ::Type{FR}, ρ::Projection, A, B;
                       rng::MaybeRNG = nothing) where {FR<:Binary}
    rr = _resolve_rng(rng)
    @inbounds for i in eachindex(dest, A, B)
        dest[i] = _kernel_result(v, FR, ρ, _drawR(ρ, rr, nothing),
                                 decode(A[i]), decode(B[i]))
    end
    dest
end
function _vmap_scalar!(dest, v::Val, ::Type{FR}, ρ::Projection, A, B, C;
                       rng::MaybeRNG = nothing) where {FR<:Binary}
    rr = _resolve_rng(rng)
    @inbounds for i in eachindex(dest, A, B, C)
        dest[i] = _kernel_result(v, FR, ρ, _drawR(ρ, rr, nothing),
                                 decode(A[i]), decode(B[i]), decode(C[i]))
    end
    dest
end

# The runtime-symbol boundary. Validate ONCE here — the operation exists and
# the operand count matches its arity — then cross into `Val(op)`, after which
# every inner loop is statically dispatched and no element pays for a lookup.
# Without this, an unknown symbol reached `Val(op)` and surfaced as a
# MethodError from somewhere deep in the kernel, naming nothing a caller could
# act on (improveapi3.md §6 Phase 7.2/7.3).
@inline function vmap(op::Symbol, fr::Type{<:Binary}, ρ::Projection,
                      As::AbstractArray{<:BinaryValue}...; rng::MaybeRNG = nothing)
    _validate_runtime_op(:vmap, op, length(As))
    isempty(As) && throw(ArgumentError("vmap needs at least one operand array"))
    dest = similar(first(As), BinaryValue(fr))
    vmap!(dest, Val(op), ρ, As...; rng)
end
@inline vmap(op::Symbol, fr::Type{<:BinaryValue}, ρ::Projection,
             As::AbstractArray{<:BinaryValue}...; rng::MaybeRNG = nothing) =
    vmap(op, BinaryFormatOf(fr), ρ, As...; rng)

# ---- registry-generated array surface: Op(fr, ρ, A...) mirrors the scalar
# signature, plus the same-format convenience under the session default ρ
for op in OP_REGISTRY
    op.name === :Convert && continue
    name = op.name
    xs = [Symbol(:A, i) for i in 1:op.arity]
    spec = [:($(x)::AbstractArray{<:BinaryValue}) for x in xs]
    same = [:($(x)::AbstractArray{T}) for x in xs]
    @eval begin
        @inline $name(fr::Type{<:Binary}, ρ::Projection, $(spec...);
                      rng::MaybeRNG = nothing) =
            vmap($(QuoteNode(name)), fr, ρ, $(xs...); rng)
        @inline $name(fr::Type{<:BinaryValue}, ρ::Projection, $(spec...); kw...) =
            $name(BinaryFormatOf(fr), ρ, $(xs...); kw...)
        @inline function $name($(same...); kw...) where {T<:BinaryValue}
            ρ = DefaultProjection()                     # the speculation guard, as in scalar.jl
            ρ === RTE_SN && return $name(BinaryFormatOf(T), RTE_SN, $(xs...); kw...)
            $name(BinaryFormatOf(T), ρ, $(xs...); kw...)
        end
    end
end

# Convert's array forms: the datum-array form rides the Shape-A gather (its
# table is built by _kernel_result's bare-projection row); external float
# arrays are not enumerable, so they run a Shape-B loop with exact widening
# per element. rng is threaded like every other array operation's — pure ρ
# never resolves it.
Convert(fr::Type{<:Binary}, ρ::Projection, A::AbstractArray{<:BinaryValue};
        rng::MaybeRNG = nothing) = vmap(:Convert, fr, ρ, A; rng)

# The value-array loop calls the SAME `_convert_value` family the scalar
# surface calls (ops/scalar.jl), so the two cannot disagree about a carrier
# rung. `similar` preserves the source's axes and shape; the RNG is resolved
# once and drawn exactly once per element, in `eachindex` order.
function Convert(fr::Type{<:Binary}, ρ::Projection,
                 A::AbstractArray{<:ConvertNumber}; rng::MaybeRNG = nothing)
    dest = similar(A, BinaryValue(fr))
    rr = isstochastic(ρ) ? _resolve_rng(rng) : nothing
    @inbounds for i in eachindex(dest, A)
        dest[i] = _convert_value(fr, ρ, A[i], _drawR(ρ, rr, nothing))
    end
    dest
end

# An element type that is not one of the accepted sources is REFUSED, not
# silently accommodated: accepting it would put a dynamic dispatch inside the
# element loop and, for a type whose own conversion rounds, an unproved double
# rounding inside each element (improveapi3.md §6 Phase 3.6). Spelled on bare
# `AbstractArray` so `Vector{Any}` and `Vector{Real}` alike get the message
# rather than a MethodError that names no alternative.
@noinline Convert(fr::Type{<:Binary}, ρ::Projection, A::AbstractArray; kw...) =
    throw(ArgumentError(
        "Convert does not accept an array of $(eltype(A)): the accepted element " *
        "types are BinaryValue, Float16/Float32/Float64/BFloat16, Float128, " *
        "BigFloat, and Integer. Convert the array to one of those first, so the " *
        "rounding you get is one you chose."))

Convert(fr::Type{<:BinaryValue}, ρ::Projection, A::AbstractArray; kw...) =
    Convert(BinaryFormatOf(fr), ρ, A; kw...)

# same-format array convenience under the task's default projection. The
# default is resolved ONCE, before the loop, and never per element.
@inline function Convert(fr::Type{<:Binary}, A::AbstractArray; rng::MaybeRNG = nothing)
    ρ = DefaultProjection()
    ρ === RTE_SN && return Convert(fr, RTE_SN, A; rng)
    Convert(fr, ρ, A; rng)
end
@inline Convert(fr::Type{<:BinaryValue}, A::AbstractArray; kw...) =
    Convert(BinaryFormatOf(fr), A; kw...)

export vmap, vmap!

# arrays/kernels.jl
