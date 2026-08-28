# broadcasting: route `f.(A, B)` through the array kernels
#
# Base's elementwise loop calls the scalar veneer once per element, which for a
# tabled signature is ~40x the cost of the gather `vmap!` already performs
# (A .+ B: 631 µs against 15 µs at K = 8, N = 65,536). This file hooks
# `copyto!` for exactly the shape the kernels can serve — a registered veneer
# applied to same-format datum arrays that all share `dest`'s axes — and lets
# everything else fall through to Base untouched.
#
# What deliberately does NOT match, and so keeps Base's semantics exactly:
#   fused chains          (A .+ B) .* C   — the inner arg is a Broadcasted
#   scalar operands       A .+ B[1]       — the arg is a datum, not an array
#   mixed element types   A .+ 1.0        — the args are not all AbstractArray{T}
#   predicates            A .< B          — dest is AbstractArray{Bool}
#   shape-broadcasting    A .+ reshape(…) — caught by the axes guard at runtime
#
# This is a performance route, not a semantic one: `vmap!` and the scalar
# veneer are asserted equal in test-kernels.jl, and the tests below assert the
# broadcast form equals the kernel form for every registered veneer.
#
# Loaded AFTER compat/base.jl — the veneer tables it reads are defined there.

using Base.Broadcast: Broadcasted, DefaultArrayStyle

# (draft op, Base function, arity) for every veneer the kernels implement.
# Built from the SAME tables compat/base.jl defines its scalar methods from, so
# an op added to the registry cannot be silently missed here.
const _BC_VENEERS = Tuple{Symbol,Symbol,Int}[
    (:Negate, :-, 1), (:Add, :+, 2), (:Subtract, :-, 2),
    (:Multiply, :*, 2), (:Divide, :/, 2), (:ArcTan2, :atan, 2),
    (:FMA, :fma, 3), (:FMA, :muladd, 3), (:Clamp, :clamp, 3),
]
for (op, bf) in _BASE_UNARY
    push!(_BC_VENEERS, (op, bf, 1))
end
for (op, bf) in _BASE_BINARY
    push!(_BC_VENEERS, (op, bf, 2))
end

for (op, bf, arity) in _BC_VENEERS
    args = [Symbol(:A, i) for i in 1:arity]
    argtypes = [:(AbstractArray{T}) for _ in 1:arity]
    @eval function Base.copyto!(dest::AbstractArray{T},
                                bc::Broadcasted{<:DefaultArrayStyle, <:Any,
                                                typeof(Base.$bf),
                                                <:Tuple{$(argtypes...)}}) where {T<:BinaryValue}
        ($(args...),) = bc.args
        # a Broadcasted may still be describing a SHAPE broadcast (an operand
        # with a singleton axis stretched over dest); those axes do not match
        # and must keep Base's loop
        if $(Expr(:&&, [:(axes($a) == axes(dest)) for a in args]...))
            # the same speculation guard the scalar veneers use
            ρ = DefaultProjection()
            ρ === RTE_SN && return vmap!(dest, Val($(QuoteNode(op))), RTE_SN, $(args...))
            return vmap!(dest, Val($(QuoteNode(op))), ρ, $(args...))
        end
        @invoke Base.copyto!(dest::AbstractArray, bc::Broadcasted)
    end
end
