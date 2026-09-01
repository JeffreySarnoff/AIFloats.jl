# the scalar flow: decode operands → ωeval → _finish → a datum
#
# Draft parameter order is Op(F, ρ, operands...). The registry generates every
# method; nothing per-op is written by hand.

# ---- RNG plumbing -----------------------------------------------------------
# The default is nothing, NOT default_rng(): a pure-ρ call must never touch
# RNG state.
const MaybeRNG = Union{Nothing, Random.AbstractRNG}
const MaybeR = Union{Nothing, Int}

@inline _resolve_rng(rng::MaybeRNG) = rng === nothing ? Random.default_rng() : rng

@inline function _drawR(ρ::Projection, rng::MaybeRNG, R::MaybeR)
    isstochastic(ρ) || return 0
    N = nrandbits(ρ)::Int
    if R === nothing
        return Int(rand(_resolve_rng(rng), UInt64) & ((UInt64(1) << N) - 1))
    end
    0 <= R < (1 << N) ||
        throw(ArgumentError("explicit R=$R outside 0:$(2^N - 1) for N=$N random bits"))
    R
end

# ---- result resolution ------------------------------------------------------
# exact carrier values project directly; an Enclosure goes to the interval
# oracle (sound for every mode at fixed R)
@inline _finish(::Type{F}, ρ::Projection, R::Int, res::AbstractFloat) where {F<:Binary} =
    project(F, ρ, res; R)
function _finish(::Type{F}, ρ::Projection, R::Int, e::Enclosure) where {F<:Binary}
    if FAST_ENCLOSURE[]
        # stage 1: the eager Float64 estimate inside its 2^-45 envelope
        yd = e.yd
        if isfinite(yd) && abs(yd) >= _F64_MINNORMISH
            Ed = ldexp(abs(yd), _F64_RELEXP)
            dd = project(F, ρ, yd - Ed; R, sticky = +1)
            du = project(F, ρ, yd + Ed; R, sticky = -1)
            codepoint(dd) == codepoint(du) && return dd
        end
    end
    project_interval(F, ρ, e.f; R)                 # rigorous fallback always decides
end
@inline _finish(::Type{F}, ρ::Projection, R::Int, res::Dyadic) where {F<:Binary} =
    project(F, ρ, res; R)
# the sticky-directed projection: the universal correct-rounding decision for
# a value with one neglected tail of known direction
@inline _finish(::Type{F}, ρ::Projection, R::Int, s::Sticky) where {F<:Binary} =
    project(F, ρ, s.v; R, sticky = s.sgn)

# ---- apply_op ---------------------------------------------------------------
# the explicit Float64 union split keeps the widened result union off the hot
# path (measured in SmallFloats: 399 → 269 ns/element); everything else goes
# through the @noinline finisher. Vararg carries a LENGTH parameter so the
# splat compiles to a static call rather than a boxing dynamic apply.
@inline _eval_narrow(op::Val, xs...) = ωeval(op, xs...)
@inline function _eval_narrow(op::Val, x::Float128)
    x64 = _try_f64_exact(x)
    x64 === nothing ? ωeval(op, x) : ωeval(op, x64)
end
@inline function _eval_narrow(op::Val, x::Float128, y::Float128)
    x64 = _try_f64_exact(x)
    x64 === nothing && return ωeval(op, x, y)
    y64 = _try_f64_exact(y)
    y64 === nothing ? ωeval(op, x, y) : ωeval(op, x64, y64)
end
@inline function _eval_narrow(op::Val, x::Float128, y::Float128, z::Float128)
    x64 = _try_f64_exact(x)
    x64 === nothing && return ωeval(op, x, y, z)
    y64 = _try_f64_exact(y)
    y64 === nothing && return ωeval(op, x, y, z)
    z64 = _try_f64_exact(z)
    z64 === nothing ? ωeval(op, x, y, z) : ωeval(op, x64, y64, z64)
end

@inline function apply_op(op::Val, ::Type{F}, ρ::Projection, R::Int,
                          x, xs::Vararg{Any, N}) where {F<:Binary, N}
    res = _eval_narrow(op, x, xs...)
    res isa Float64 && return project(F, ρ, res; R)
    _finish_slow(F, ρ, R, res)
end
@noinline _finish_slow(::Type{F}, ρ::Projection, R::Int, res) where {F<:Binary} =
    _finish(F, ρ, R, res)

# ---- the generated spec register --------------------------------------------
# For each registry op:
#   Op(F, ρ, x::BinaryValue...; rng, R)   — the draft form (F a format or a
#                                           datum type/alias)
#   Op(x::T...; ...) same-format          — under the session default ρ
for op in OP_REGISTRY
    op.name === :Convert && continue
    name = op.name
    V = Val{name}
    xs = [Symbol(:x, i) for i in 1:op.arity]
    spec = [:($(x)::BinaryValue) for x in xs]
    same = [:($(x)::T) for x in xs]
    dec = [:(decode($x)) for x in xs]
    bar = Symbol(:_default_, name)          # the projection-typed barrier
    @eval begin
        @inline function $name(fr::Type{<:Binary}, ρ::Projection, $(spec...);
                               rng::MaybeRNG = nothing, R::MaybeR = nothing)
            apply_op($V(), fr, ρ, _drawR(ρ, rng, R), $(dec...))
        end
        @inline $name(fr::Type{<:BinaryValue}, ρ::Projection, $(spec...); kw...) =
            $name(BinaryFormatOf(fr), ρ, $(xs...); kw...)
        @inline $name(fr::Binary, ρ::Projection, $(spec...); kw...) =
            $name(typeof(fr), ρ, $(xs...); kw...)
        # The PROJECTION-TYPED FUNCTION BARRIER (improveapi3.md §4.3). The
        # scoped default is a `ScopedValue{Projection}`, so reading it yields an
        # abstractly typed projection; passing that straight to the operation
        # leaves every downstream decision dynamic — 182 ns against the 2.5 ns
        # of the same call with a concrete projection.
        #
        # Three things about the signature are load-bearing:
        #
        #   * NOT `@inline`. Inlining it back into the guard would put the
        #     abstract projection right back where it was.
        #   * `Projection{RM,SM}`, not `ρ::P where P<:Projection`. An argument
        #     statically typed `Projection` SATISFIES `P<:Projection`, so Julia
        #     binds `P = Projection` and makes a static call to an abstract
        #     specialization — the barrier compiles away to nothing. It cannot
        #     satisfy `Projection{RM,SM}` for any particular `RM, SM`, which is
        #     what forces the runtime dispatch this seam is paying for.
        #   * The format comes from the DATUM, not from a leading `::Type{T}`.
        #     A `Type` argument in a dynamically dispatched call is expensive to
        #     match: measured 148 ns with it against 28 ns without, for the same
        #     body. That single argument cost more than everything else here.
        #   * `rng` and `R` cross the boundary POSITIONALLY. A `; kw...` splat
        #     through a dynamic call materializes its named tuple, and that was
        #     two of the three allocations this seam used to make.
        function $bar(ρ::Projection{RM,SM}, $(same...),
                      rng, R) where {T<:BinaryValue, RM, SM}
            $name(BinaryFormatOf(T), ρ, $(xs...); rng, R)::T
        end
        # same-format convenience under the task's default projection. The
        # SPECULATION GUARD: the untouched default RTE_SN is tested by
        # identity and called with the literal constant, so the overwhelmingly
        # common unscoped path is a static, allocation-free call and never
        # reaches the barrier. Spelled inline — a closure would defeat the split.
        @inline function $name($(same...); rng::MaybeRNG = nothing,
                               R::MaybeR = nothing) where {T<:BinaryValue}
            ρ = DefaultProjection()
            ρ === RTE_SN && return $name(BinaryFormatOf(T), RTE_SN, $(xs...); rng, R)::T
            $bar(ρ, $(xs...), rng, R)::T
        end
        export $name
    end
end

# ---- Convert ----------------------------------------------------------------
# the one op accepting external operands: each method is a bare projection
# after an EXACT widening. Rational and Irrational inputs are rejected rather
# than double-rounded silently.

"""
    Convert(F, ρ, x; rng, R) -> BinaryValue

Project `x` into format `F` under projection `ρ` — the draft's Convert.
Accepts a `BinaryValue` (any format), `Float64`/`Float32`/`Float16`/`BFloat16`
(exact widening), `Float128`, `BigFloat`, or an `Integer` (widened exactly).

`Rational` and `Irrational` inputs are refused: their exact projection is not
representable as a single rounding of a float, and silently double-rounding
would be a lie.

# Examples

```jldoctest
julia> Convert(Binary(8, 4, SIGNED, EXTENDED), RTE_SF, 1.6)
1.625
```
"""
# an Integer with |x| ≤ 2^53 is EXACT in Float64, so the widening is not a
# rounding and the projection below is still the one and only rounding. The
# BigFloat route stays for everything wider (BigInt, the top of Int64/UInt64).
# The comparisons are exact for every Integer type: Julia compares mixed
# integer types by value, never by a lossy promotion.
const _F64_EXACT_INT = Int64(1) << 53

"""
    _exact_in_float128(x::Integer) -> Bool

Whether `x` is EXACTLY representable as a `Float128`. Not a magnitude test: a
bound like `|x| ≤ 2^113` is safe but rejects `2^10000`, which is exact. What
matters is the significant bits left after the trailing zeroes, plus the
exponent fitting binary128's finite range (float128use.md §2).

Works for every `Integer` — signed, `typemin`, `UInt128`, `BigInt` — without
narrowing first, which is why the arithmetic below stays in the integer domain.
"""
@inline function _exact_in_float128(x::Integer)
    iszero(x) && return true
    nbits = ndigits(x, base = 2)                # bit length of |x|
    sigbits = nbits - trailing_zeros(x)
    sigbits <= 113 || return false
    (nbits - 1) <= Int(exponent(floatmax(Float128)))
end

# The carrier ladder for an integer value, cheapest gate first. Each rung is
# EXACT, so the projection below it remains the one and only rounding — none of
# this is a double rounding.
# ---- the one conversion seam ------------------------------------------------
# `_convert_value(F, ρ, x, R)` is the single implementation of "project this
# source value into F". Scalar `Convert` resolves `R` once and calls it; the
# array loop resolves the RNG once and calls it per element. There is no second
# ladder to drift from this one (improveapi3.md §6 Phase 3.3) — the array
# surface used to carry a private copy, and a copy of a carrier ladder is
# exactly the kind of duplicate that stays right until the day it does not.
#
# Every rung is EXACT, so the `project` below it remains the one and only
# rounding. That is the property the whole family exists to preserve.
@inline _convert_value(::Type{F}, ρ::Projection, x::BinaryValue,
                       R::Int) where {F<:Binary} = project(F, ρ, decode(x); R)
@inline _convert_value(::Type{F}, ρ::Projection, x::Float64,
                       R::Int) where {F<:Binary} = project(F, ρ, x; R)
@inline _convert_value(::Type{F}, ρ::Projection, x::Union{Float32,Float16,BFloat16},
                       R::Int) where {F<:Binary} = project(F, ρ, Float64(x); R)
@inline _convert_value(::Type{F}, ρ::Projection, x::Float128,
                       R::Int) where {F<:Binary} = project(F, ρ, x; R)
@inline _convert_value(::Type{F}, ρ::Projection, x::BigFloat,
                       R::Int) where {F<:Binary} = project(F, ρ, x; R)
@inline function _convert_value(::Type{F}, ρ::Projection, x::Integer,
                                R::Int) where {F<:Binary}
    -_F64_EXACT_INT <= x <= _F64_EXACT_INT && return project(F, ρ, Float64(x); R)
    _exact_in_float128(x) && return project(F, ρ, Float128(x); R)
    b = setprecision(BigFloat, max(64, ndigits(x, base = 2) + 8)) do
        BigFloat(x)                             # exact at this width
    end
    project(F, ρ, b; R)
end

"""
    AIFloats.ConvertNumber

The closed set of non-datum sources `Convert` accepts: `Float16`, `Float32`,
`Float64`, `BFloat16`, `Float128`, `BigFloat`, and any `Integer`.

Closed on purpose. A generic `Real` fallback would have to reach `BigFloat`
through `convert`, and for a type whose own conversion already rounds, that is
a double rounding this package cannot prove anything about.
"""
const ConvertNumber = Union{Float16, Float32, Float64, BFloat16,
                            Float128, BigFloat, Integer}

"""
    AIFloats.ConvertSource

[`AIFloats.ConvertNumber`](@ref) together with `BinaryValue` — everything the
scalar and array `Convert` surfaces accept.
"""
const ConvertSource = Union{BinaryValue, ConvertNumber}

@inline Convert(fr::Type{<:Binary}, ρ::Projection, x::ConvertSource;
                rng::MaybeRNG = nothing, R::MaybeR = nothing) =
    _convert_value(fr, ρ, x, _drawR(ρ, rng, R))

@noinline Convert(fr::Type{<:Binary}, ρ::Projection, x::Rational; kw...) =
    throw(ArgumentError("Convert does not accept Rational: its exact projection is not a single float rounding — convert explicitly and own the double rounding"))
@noinline Convert(fr::Type{<:Binary}, ρ::Projection, x::Irrational; kw...) =
    throw(ArgumentError("Convert does not accept Irrational: supply a rounded float, or use the interval route"))
@inline Convert(fr::Type{<:BinaryValue}, ρ::Projection, x; kw...) =
    Convert(BinaryFormatOf(fr), ρ, x; kw...)
export Convert

# ---- a format type constructs a datum ----------------------------------------
# `Binary8p4se(1.5)` is the convenient spelling and must keep working now that
# the named aliases ARE format types (improveapi.md §4.1.2, Phase 1.4).
#
# Note what this means: `F(x) isa F` is FALSE — a format type's constructor
# returns a `BinaryValue`, not a `Binary`. That is deliberate and is the price
# of the convenience; a format is not a number and cannot be one. Anyone who
# wants the datum TYPE writes `BinaryValue(F)`, which is the only spelling that
# yields something `x isa` answers true for.
@inline (::Type{F})(x::Real; kw...) where {F<:Binary} =
    BinaryValue{F, CodeType(F)}(x; kw...)::BinaryValue{F, CodeType(F)}

# ---- construction from a value ----------------------------------------------
# the BinaryValue value constructor: an Unsigned is a code point (defined with
# the struct); every other Real is a value and goes through Convert — under an
# explicit projection keyword, defaulting to the session projection.
#
# `projection` defaults to `nothing`, not to `DefaultProjection()`: an eagerly
# evaluated default would read the abstract Ref on EVERY call and force the
# dynamic, boxing call through it. `nothing` means "ask the session", and the
# ask carries the same SPECULATION GUARD the generated op methods use — the
# untouched default RTE_SN is tested by identity and passed as the literal
# constant, so the common construction is a static, allocation-free call.
@inline function (::Type{BinaryValue{F,U}})(x::Real;
        projection::Union{Nothing, Projection} = nothing,
        rng::MaybeRNG = nothing, R::MaybeR = nothing) where {F<:Binary, U<:Unsigned}
    projection === nothing || return _default_convert(_witness(F), projection, x, rng, R)
    ρ = DefaultProjection()
    ρ === RTE_SN && return Convert(F, RTE_SN, x; rng, R)::BinaryValue{F,U}
    _default_convert(_witness(F), ρ, x, rng, R)
end

# Value construction's projection-typed barrier — same shape, same three
# constraints as the generated ops' (see the comment there). It needs the
# format, and there is no datum argument to read it from, so it takes a
# WITNESS: the zero datum of F, which is isbits and free to make. A leading
# `::Type{F}` would be the obvious spelling and is the expensive one — 169 ns
# against this form's 24 ns, for an identical body.
@inline _witness(::Type{F}) where {F<:Binary} = _rawvalue(F, zero(CodeType(F)))
_default_convert(::BinaryValue{F,U}, ρ::Projection{RM,SM}, x, rng,
                 R) where {F<:Binary, U<:Unsigned, RM, SM} =
    Convert(F, ρ, x; rng, R)::BinaryValue{F,U}
