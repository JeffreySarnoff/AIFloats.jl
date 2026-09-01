# the κ registry: approximate implementations, measured not promised
#
# Two guarantees, machine-checkable:
#   1. Nothing approximate is reachable from the default API — approximate
#      kernels live in their own registry, retrieved only by explicit name.
#   2. Every declared κ is VERIFIED by enumeration at registration (feasible
#      because value sets are tiny); an understated declaration is rejected.
#
# κ (draft §4.4–§4.6, Annex worked example): the maximum distance, in
# result-format code-point steps along the total order, between the
# implementation's result and the defined result over all inputs whose defined
# result is finite. κ = NaN when the implementation mismatches on any input
# whose defined result is NaN or ±Inf, or returns a non-finite value where the
# defined result is finite — unbounded in the code-point metric.

"""
    codedistance(a::T, b::T) -> Int

Distance between two datums of one format in code-point steps along the total
order. Not exported.
"""
@inline codedistance(a::T, b::T) where {T<:BinaryValue} =
    abs(Int(order_key(a)) - Int(order_key(b)))

@inline _mixed_radix_codes(lin::Int, ::Tuple{}) = ()
@inline function _mixed_radix_codes(lin::Int, Ks::Tuple{Int, Vararg{Int}})
    K = first(Ks)
    (lin & ((1 << K) - 1), _mixed_radix_codes(lin >> K, Base.tail(Ks))...)
end

"""
    measure_kappa(fn, op, FR, argformats, ρ; max_exhaustive = 2^22, rng, samples = 2^20)
        -> (κ::Float64, exhaustive::Bool)

Measure κ of `fn(x::argformats[1], …)::BinaryValue{FR}` against the defined
results of draft operation `op` under the deterministic projection `ρ`.
Enumerates the full input cross-product when it has at most `max_exhaustive`
points; otherwise measures on `samples` uniform draws and reports
`exhaustive = false`. Stochastic `ρ` is refused — κ is defined against
deterministic defined results.
"""
function measure_kappa(fn::Fn, op::Symbol, fr::Type{<:Binary},
                       argformats::NTuple{N, DataType}, ρ::Projection;
                       max_exhaustive::Int = 1 << 22,
                       rng::Random.AbstractRNG = Random.default_rng(),
                       samples::Int = 1 << 20) where {Fn, N}
    max_exhaustive >= 0 || throw(ArgumentError("max_exhaustive must be nonnegative"))
    samples >= 0 || throw(ArgumentError("samples must be nonnegative"))
    isstochastic(ρ) &&
        throw(ArgumentError("κ is defined against deterministic defined results; stochastic ρ is not measurable"))
    any(o -> o.name === op, OP_REGISTRY) || throw(ArgumentError("unknown draft operation :$op"))
    arity = opinfo(op).arity
    arity == N || throw(ArgumentError(":$op has arity $arity, got $N argument formats"))
    all(f -> f <: Binary || f <: BinaryValue, argformats) ||
        throw(ArgumentError("argument formats must be Binary formats or concrete BinaryValue types"))
    FR = BinaryValue(fr)
    fmts = map(f -> f <: BinaryValue ? BinaryFormatOf(f) : f, argformats)
    Ks = map(f -> Int(BitwidthOf(f)), fmts)
    total = prod(1 .<< Ks)
    exhaustive = total <= max_exhaustive
    !exhaustive && samples == 0 &&
        throw(ArgumentError("samples must be positive when the input space is not examined exhaustively"))
    κ = 0.0
    defined = (args...) -> op === :Convert ?
        project(fr, ρ, decode(args[1])) :
        apply_op(Val(op), fr, ρ, 0, map(decode, args)...)
    function visit(codes::NTuple{N, Int})
        args = ntuple(i -> _rawvalue(fmts[i], CodeType(fmts[i])(codes[i])), Val(N))
        want = defined(args...)
        got = fn(args...)::FR
        if isnan(want) || isinf(want)
            isequal(want, got) || return NaN              # non-finite defined must match
            return 0.0
        end
        (isnan(got) || isinf(got)) && return NaN          # unbounded deviation
        Float64(codedistance(got, want))
    end
    if exhaustive
        for lin in 0:total - 1
            d = visit(_mixed_radix_codes(lin, Ks))
            isnan(d) && return (NaN, true)
            κ = max(κ, d)
        end
    else
        for _ in 1:samples
            codes = ntuple(i -> Int(rand(rng, UInt32) & ((1 << Ks[i]) - 1)), Val(N))
            d = visit(codes)
            isnan(d) && return (NaN, false)
            κ = max(κ, d)
        end
    end
    (κ, exhaustive)
end
measure_kappa(fn, op::Symbol, fr::Type{<:BinaryValue}, args::Tuple, ρ::Projection; kw...) =
    measure_kappa(fn, op, BinaryFormatOf(fr), args, ρ; kw...)
measure_kappa(fn, op::Symbol, fr::Binary, args::Tuple, ρ::Projection; kw...) =
    measure_kappa(fn, op, typeof(fr), map(a -> a isa Binary ? typeof(a) : a, args), ρ; kw...)

"""
    ApproxImpl

A registered κ-approximate implementation of one operation specialization:
`name`, `op`, result format `fr`, `argformats`, `ρ`, the callable `fn`, and
the declared and measured κ (with whether the measurement was exhaustive).
"""
struct ApproxImpl{Fn}
    name::Symbol
    op::Symbol
    fr::DataType
    argformats::Tuple{Vararg{DataType}}
    ρ::Projection
    fn::Fn
    kappa_declared::Float64
    kappa_measured::Float64
    exhaustive::Bool
end
kappa(a::ApproxImpl) = a.kappa_declared
kappa_measured(a::ApproxImpl) = a.kappa_measured

const APPROX_REGISTRY = Dict{Symbol, ApproxImpl}()
const APPROX_LOCK = ReentrantLock()

"""
    register_approx!(name, op, FR, argformats, ρ, fn; κ = nothing, kwargs...) -> ApproxImpl

Register `fn` as the named κ-approximate implementation of
`op⟨argformats → FR, ρ⟩`. κ is measured by enumeration ([`measure_kappa`](@ref));
a declared `κ` smaller than the measured value is **rejected**. Omitting `κ`
declares the measured value. An implementation whose measured κ is NaN
(non-finite mismatches) can be registered only by declaring `κ = NaN`.
"""
function register_approx!(name::Symbol, op::Symbol, fr::Type{<:Binary},
                          argformats::NTuple{N, DataType}, ρ::Projection, fn::Fn;
                          κ::Union{Nothing, Real} = nothing, kwargs...) where {Fn, N}
    any(o -> o.name === op, OP_REGISTRY) || throw(ArgumentError("unknown draft operation :$op"))
    arity = opinfo(op).arity
    arity == N || throw(ArgumentError(":$op has arity $arity, got $N argument formats"))
    κm, exh = measure_kappa(fn, op, fr, argformats, ρ; kwargs...)
    if isnan(κm)
        (κ !== nothing && isnan(κ)) || throw(ArgumentError(
            "implementation mismatches on non-finite defined results (measured κ = NaN); " *
            "register with explicit κ=NaN to acknowledge, or fix it"))
        κd = NaN
    else
        κd = κ === nothing ? κm : Float64(κ)
        (!isnan(κd) && κd < κm) &&
            throw(ArgumentError("declared κ = $κd understates measured κ = $κm — registration rejected"))
    end
    fmts = map(f -> f <: BinaryValue ? BinaryFormatOf(f) : f, argformats)
    impl = ApproxImpl(name, op, fr, Tuple(fmts), ρ, fn, κd, κm, exh)
    lock(APPROX_LOCK) do
        haskey(APPROX_REGISTRY, name) &&
            throw(ArgumentError("approximate implementation :$name already registered"))
        APPROX_REGISTRY[name] = impl
    end
    impl
end
register_approx!(name::Symbol, op::Symbol, fr::Type{<:BinaryValue}, args::Tuple, ρ::Projection, fn; kw...) =
    register_approx!(name, op, BinaryFormatOf(fr), args, ρ, fn; kw...)
register_approx!(name::Symbol, op::Symbol, fr::Binary, args::Tuple, ρ::Projection, fn; kw...) =
    register_approx!(name, op, typeof(fr), map(a -> a isa Binary ? typeof(a) : a, args), ρ, fn; kw...)

"""Retrieve a registered approximate implementation (callable via `.fn`)."""
approx(name::Symbol) = lock(APPROX_LOCK) do
    get(APPROX_REGISTRY, name) do
        throw(KeyError("no approximate implementation :$name registered"))
    end
end
kappa(name::Symbol) = kappa(approx(name))
"""Sorted names of all registered κ-approximate implementations."""
list_approx() = lock(() -> sort!(collect(keys(APPROX_REGISTRY))), APPROX_LOCK)
"""Remove a registered κ-approximate implementation (no-op if absent)."""
unregister_approx!(name::Symbol) = lock(() -> (delete!(APPROX_REGISTRY, name); nothing), APPROX_LOCK)

# ---- the draft Annex's worked example: flush subnormal results ---------------
"""
    ftz_variant(op, FR, F1, ρ) -> fn

The Annex-style approximate unary implementation: compute the defined result,
then flush subnormal results to zero or `MinNormalOf(FR)`, whichever is nearer,
ties toward zero (magnitude-symmetric for signed formats). Suitable for
[`register_approx!`](@ref); for precision `P ≥ 2` its κ is `2^(P-2)`, and `0`
when `P == 1` (no subnormals exist).
"""
function ftz_variant(op::Symbol, fr::Type{<:Binary}, f1::Type{<:Binary}, ρ::Projection)
    P = Int(PrecisionOf(fr))
    half = 1 << max(P - 2, 0)                    # subnormal codes 1 … 2^(P-1)-1; tie at 2^(P-2)
    minnorm = MinNormalOf(fr)
    FR = BinaryValue(fr)
    function fn(x::BinaryValue)
        r = (op === :Convert ? project(fr, ρ, decode(x)) :
                               apply_op(Val(op), fr, ρ, 0, decode(x)))::FR
        issubnormal(r) || return r
        m = Int(codepoint(r) & ~signmask(fr))    # magnitude code
        neg = is_signed(fr) && codepoint(r) >= signmask(fr)
        m <= half && return zero(FR)             # nearer to zero (ties to zero)
        neg ? Negate(minnorm) : minnorm
    end
    fn
end
ftz_variant(op::Symbol, fr::Type{<:BinaryValue}, f1::Type{<:BinaryValue}, ρ::Projection) =
    ftz_variant(op, BinaryFormatOf(fr), BinaryFormatOf(f1), ρ)
ftz_variant(op::Symbol, fr::BinarySpecifier, f1::BinarySpecifier, ρ::Projection) =
    ftz_variant(op, _formattype(fr), _formattype(f1), ρ)
