# OP_REGISTRY — the single source (invariant 7)
#
# The scalar methods, the Convert surface, and (later) the Base veneers, array
# kernels, table enumeration, and conformance all derive from these rows. No
# hand-written per-op variants anywhere: a variant that cannot be written
# unevenly cannot diverge.

struct OpInfo
    name::Symbol
    arity::Int
    group::Symbol   # :A exact arithmetic/selection, :B enclosure, :C extremum, :conv
    factors::Int    # max datum factors in any monomial of the exact result —
                    # the CARRIER-WIDTH driver. Too low picks a carrier that
                    # overflows rather than one that errors. Not arity: FAA has
                    # three operands and one factor.
end

const OP_REGISTRY = OpInfo[]
register_op!(name::Symbol, arity::Int, group::Symbol, factors::Int = 1) =
    push!(OP_REGISTRY, OpInfo(name, arity, group, factors))
opinfo(name::Symbol) = OP_REGISTRY[findfirst(o -> o.name === name, OP_REGISTRY)]

const _UNARY_OPS = (:Abs, :Negate, :Sqrt, :RSqrt, :Recip,
                    :Exp, :Exp2, :ExpMinusOne, :Log, :Log2, :LogOnePlus,
                    :Sin, :Cos, :Tan, :ArcSin, :ArcCos, :ArcTan,
                    :Sinh, :Cosh, :Tanh, :ArcSinh, :ArcCosh, :ArcTanh,
                    :SinPi, :CosPi, :TanPi, :ArcSinPi, :ArcCosPi, :ArcTanPi,
                    :Softplus)
const _BINARY_OPS = (:CopySign, :Add, :Subtract, :Multiply, :Divide,
                     :Hypot, :ArcTan2, :ArcTan2Pi,
                     :Maximum, :Minimum, :MaximumNumber, :MinimumNumber,
                     :MaximumMagnitude, :MinimumMagnitude,
                     :MaximumMagnitudeNumber, :MinimumMagnitudeNumber,
                     :MinimumFinite, :MaximumFinite)
const _TERNARY_OPS = (:FMA, :FAA, :Clamp)

# ops whose exact result is a two-factor monomial (product/quotient span)
const _TWO_FACTOR_OPS = (:Multiply, :Divide, :Hypot, :FMA)

# exact selections: one implementation, parametric in the carrier
const _EXACT_SELECTION = (:Abs, :Negate, :CopySign, :Clamp,
                          :Maximum, :Minimum, :MaximumNumber, :MinimumNumber,
                          :MaximumMagnitude, :MinimumMagnitude,
                          :MaximumMagnitudeNumber, :MinimumMagnitudeNumber,
                          :MinimumFinite, :MaximumFinite)
# exact arithmetic: error-free transforms / exact escalation
const _EXACT_ARITH = (:Add, :Subtract, :Multiply, :FMA, :FAA)

for op in _UNARY_OPS
    g = op in _EXACT_SELECTION ? :A : :B
    register_op!(op, 1, g, 1)
end
for op in _BINARY_OPS
    g = op in _EXACT_SELECTION ? :C :
        op in _EXACT_ARITH ? :A : :B
    register_op!(op, 2, g, op in _TWO_FACTOR_OPS ? 2 : 1)
end
for op in _TERNARY_OPS
    register_op!(op, 3, :A, op in _TWO_FACTOR_OPS ? 2 : 1)
end
register_op!(:Convert, 1, :conv, 1)

# the enclosure-evaluated set is DERIVED by exclusion, and gate-tested to
# partition the registry — a mis-classified op is caught by an assertion, not
# a MethodError far from the mistake
const _LADDER_OPS = Tuple(o.name for o in OP_REGISTRY
    if !(o.name in _EXACT_SELECTION) && !(o.name in _EXACT_ARITH) &&
       !(o.name in (:Divide, :Recip, :Sqrt, :RSqrt)) && o.name !== :Convert)
const _QUOTIENT_OPS = (:Divide, :Recip, :Sqrt, :RSqrt)

# factor count as a Val-dispatched trait, so it folds
for op in OP_REGISTRY
    @eval @inline opfactors(::Val{$(QuoteNode(op.name))}) = $(op.factors)
end
@noinline opfactors(::Val{OP}) where {OP} =
    throw(ArgumentError("$OP is not in OP_REGISTRY"))

"""
    rung(op::Val, Fs::Type{<:Binary}...) -> Head

The carrier for evaluating `op` over operands of formats `Fs`: the JOIN of the
operand bound (no head is narrower than any operand's own rung — decode has
already produced that carrier) and the monomial bound
(`_rungindex_span(opfactors(op) · maxB)`). Omitting the operand bound is the
recorded subtle error. For one format at two factors this equals `rung(F)`.
"""
@inline function rung(op::Val, F::Type{<:Binary}, Fs::Vararg{Type{<:Binary}, N}) where {N}
    h = rung(F)
    maxB = ExponentBiasOf(F)
    for G in Fs
        h = joinhead(h, rung(G))
        maxB = max(maxB, ExponentBiasOf(G))
    end
    joinhead(h, _rung(Val(_rungindex_span(opfactors(op) * maxB)), F))
end
@inline rung(op::Val, x::BinaryValue, xs::BinaryValue...) =
    rung(op, BinaryFormatOf(x), map(BinaryFormatOf, xs)...)