# the Base register — Julia's own vocabulary over datums
#
# Every method here is either one same-format register call under the session
# default projection, a code-point read, or a refusal that says why. There is
# no third semantics: nothing in this file rounds outside `project`.
#
# Scope decisions:
#   · Same-format operands only. Promotion between distinct Binary formats is
#     deliberately absent — mixing formats is an explicit `Convert`, not a
#     silent widening. A datum meeting an external number (Float64, Int, …)
#     promotes to the format's `promotecarrier`.
#   · The extremum veneers map Base's IEEE semantics: `min`/`max` propagate
#     NaN, which is exactly draft Minimum/Maximum. The NaN-ignoring (Number),
#     magnitude, and finite families have no Base spelling — call them by
#     their draft names.
#   · The total order is the draft's: NaN FIRST, below −Inf. `sort` puts NaN
#     in front — a deliberate, documented divergence from Base's float
#     convention.

# =============================================================================
# 1. Base veneers, from the registry
# =============================================================================
#
# The mapping is a declarative table partitioned over the registry's op lists:
# each op is either mapped here or listed in _NO_BASE_COUNTERPART. The suite
# asserts the partition is exhaustive, so adding an op to the registry forces
# a decision here — the same non-divergence mechanism as the registry itself.

const _BASE_UNARY = (
    :Abs => :abs,   :Recip => :inv,  :Sqrt => :sqrt,
    :Exp => :exp,   :Exp2 => :exp2,  :ExpMinusOne => :expm1,
    :Log => :log,   :Log2 => :log2,  :LogOnePlus => :log1p,
    :Sin => :sin,   :Cos => :cos,    :Tan => :tan,
    :ArcSin => :asin, :ArcCos => :acos, :ArcTan => :atan,
    :Sinh => :sinh, :Cosh => :cosh,  :Tanh => :tanh,
    :ArcSinh => :asinh, :ArcCosh => :acosh, :ArcTanh => :atanh,
    :SinPi => :sinpi, :CosPi => :cospi, :TanPi => :tanpi,
)
for (op, bf) in _BASE_UNARY
    @eval Base.$bf(x::BinaryValue) = $op(x)
end

# operators and irregular spellings (arity or argument order differs)
Base.:-(x::BinaryValue) = Negate(x)
Base.:+(x::T, y::T) where {T<:BinaryValue} = Add(x, y)
Base.:-(x::T, y::T) where {T<:BinaryValue} = Subtract(x, y)
Base.:*(x::T, y::T) where {T<:BinaryValue} = Multiply(x, y)
Base.:/(x::T, y::T) where {T<:BinaryValue} = Divide(x, y)
Base.atan(y::T, x::T) where {T<:BinaryValue} = ArcTan2(y, x)     # Base's (y, x) order
const _BASE_OPERATOR = (:Negate, :Add, :Subtract, :Multiply, :Divide, :ArcTan2)

const _BASE_BINARY = (
    :CopySign => :copysign, :Hypot => :hypot,
    :Maximum => :max, :Minimum => :min,
)
for (op, bf) in _BASE_BINARY
    @eval Base.$bf(x::T, y::T) where {T<:BinaryValue} = $op(x, y)
end

Base.fma(x::T, y::T, z::T) where {T<:BinaryValue} = FMA(x, y, z)
Base.muladd(x::T, y::T, z::T) where {T<:BinaryValue} = FMA(x, y, z)   # one rounding
Base.clamp(x::T, lo::T, hi::T) where {T<:BinaryValue} = Clamp(x, lo, hi)
const _BASE_TERNARY = (:FMA, :Clamp)

# composites: Base functions with no single draft op, defined componentwise so
# each component carries its defined result
Base.sincos(x::BinaryValue) = (Sin(x), Cos(x))
Base.sincospi(x::BinaryValue) = (SinPi(x), CosPi(x))
Base.minmax(x::T, y::T) where {T<:BinaryValue} = (Minimum(x, y), Maximum(x, y))

# draft ops with no Base counterpart — call these by their draft names. One
# auditable set; the suite asserts mapped ∪ this == the registry.
const _NO_BASE_COUNTERPART = (
    :RSqrt, :Softplus,                                   # no Base function
    :ArcSinPi, :ArcCosPi, :ArcTanPi, :ArcTan2Pi,         # Base has the sinpi family only
    :MaximumNumber, :MinimumNumber,                      # no NaN-ignoring pair in Base
    :MaximumMagnitude, :MinimumMagnitude,
    :MaximumMagnitudeNumber, :MinimumMagnitudeNumber,
    :MinimumFinite, :MaximumFinite,
    :FAA,                                                # no fused add-add
    :Convert,                                            # `convert`/constructors below
)

# projection-first convenience: Op(ρ, x) ⇒ Op(typeof(x), ρ, x). The result
# format defaults to the operand's; keywords pass through. Generated from the
# registry's unary list, scalar and array forms alike.
for op in _UNARY_OPS
    @eval begin
        @inline $op(ρ::Projection, x::BinaryValue; kw...) = $op(typeof(x), ρ, x; kw...)
        $op(ρ::Projection, A::AbstractArray{T}; kw...) where {T<:BinaryValue} =
            $op(T, ρ, A; kw...)
    end
end

# =============================================================================
# 2. Comparison and the total order
# =============================================================================

# order_key strict-< IS the draft's TotalOrder-derived isless, NaN first:
# isless(NaN, x) is true for every non-NaN x, isless(NaN, NaN) is false.
"""
    isless(x::T, y::T) where {T<:BinaryValue}

The draft's total order: NaN sorts **first**, below −Inf (Base's floats put
NaN last). `sort` on datums follows it.
"""
Base.isless(x::T, y::T) where {T<:BinaryValue} = order_key(x) < order_key(y)

# numeric comparison is defined only when neither operand is NaN — IEEE
# unorderedness; keys are order-isomorphic to values off NaN
@inline _comparable(x::BinaryValue, y::BinaryValue) = !(isnan(x) | isnan(y))
Base.:(==)(x::T, y::T) where {T<:BinaryValue} = _comparable(x, y) && codepoint(x) == codepoint(y)
Base.:(<)(x::T, y::T)  where {T<:BinaryValue} = _comparable(x, y) && order_key(x) < order_key(y)
Base.:(<=)(x::T, y::T) where {T<:BinaryValue} = _comparable(x, y) && order_key(x) <= order_key(y)

# ---- counting sort over the key space: ≤ 2^K + 1 distinct keys, and equal
# keys are identical code points, so stability is moot and one pass counts.
"""
    CodeCountingSort

The default `sort` algorithm for datum vectors: a counting sort over the
`2^K + 1` order keys (NaN first). Falls back to Base's default algorithm for
vectors shorter than `2^K` and for orderings other than forward/reverse.
Not exported.
"""
struct CodeCountingSort <: Base.Sort.Algorithm end
Base.Sort.defalg(::AbstractArray{<:BinaryValue}) = CodeCountingSort()
# any ordering we do not specialize falls back to the stock algorithm
Base.sort!(v::AbstractVector{T}, lo::Int, hi::Int, ::CodeCountingSort,
           o::Base.Order.Ordering) where {T<:BinaryValue} =
    sort!(v, lo, hi, Base.Sort.DEFAULT_UNSTABLE, o)
function Base.sort!(v::AbstractVector{T}, lo::Int, hi::Int, ::CodeCountingSort,
                    o::Union{Base.Order.ForwardOrdering,
                             Base.Order.ReverseOrdering{Base.Order.ForwardOrdering}}) where {T<:BinaryValue}
    K = Int(BitwidthOf(T))
    U = CodeType(T)
    # counting sort pays 2^K of setup before it looks at the data: 257 buckets
    # at K = 8, 65 537 at K = 16. Below 2^K elements the stock algorithm wins,
    # and both produce the same permutation because equal keys are identical
    # code points.
    n = hi - lo + 1
    n < (1 << K) && return sort!(v, lo, hi, Base.Sort.DEFAULT_UNSTABLE, o)
    nk = (1 << K) + 1                              # buckets: NaN (key 0), then keys 1..2^K
    counts = zeros(Int, nk)
    key2code = Vector{U}(undef, nk)
    bucket(k) = Int(k) + 1
    for c in zero(U):U((1 << K) - 1)               # key ↔ code inversion
        key2code[bucket(order_key(rawvalue(BinaryFormatOf(T), c)))] = c
    end
    @inbounds for i in lo:hi
        counts[bucket(order_key(v[i]))] += 1
    end
    rev = o isa Base.Order.ReverseOrdering
    i = rev ? hi : lo
    step = rev ? -1 : 1
    @inbounds for b in 1:nk
        c = counts[b]
        c == 0 && continue
        # ascending buckets emitted backward under Reverse puts the NaN bucket
        # at the back — exactly Base's rev=true isless semantics
        val = rawvalue(BinaryFormatOf(T), key2code[b])
        for _ in 1:c
            v[i] = val
            i += step
        end
    end
    v
end

# lattice neighbors under Base's names. Unlike Base's saturating nextfloat,
# these run OFF the lattice into NaN at both ends (the draft's NextUp/NextDown).
Base.nextfloat(x::BinaryValue) = NextGreaterThan(x)
Base.prevfloat(x::BinaryValue) = NextLessThan(x)

# =============================================================================
# 3. The AbstractFloat contract
# =============================================================================
#
# `BinaryValue <: AbstractFloat` is a promise: generic Julia code reaches for
# this interface without asking. Two rules govern everything below. No method
# may round outside `project` — where a Base verb's contract would force a
# rounding the engine did not perform, it refuses. And a refusal says so:
# "absent" and "refused" must not look alike.

"""Refuse a Base verb with a reason. Absence and refusal must not look alike."""
@noinline _unsupported(f, ::Type{T}, why::AbstractString) where {T<:BinaryValue} =
    throw(ArgumentError("$(f) is not defined for $(formatname(T)): $why"))

# ---- constants of the type
Base.zero(::Type{T}) where {T<:BinaryValue} = rawvalue(BinaryFormatOf(T), zero(CodeType(T)))
Base.zero(::T) where {T<:BinaryValue} = zero(T)
# 1 = 2^0 is a datum of every format in the grid (exponent 0 is always in
# range, and the extended top code is never it); the suite asserts so on all
# 504. The projection cannot round, so its mode is immaterial.
Base.one(::Type{T}) where {T<:BinaryValue} = project(BinaryFormatOf(T), RTE_SN, 1.0)
Base.one(::T) where {T<:BinaryValue} = one(T)
Base.typemax(::Type{T}) where {T<:BinaryValue} =
    is_extended(T) ? rawvalue(BinaryFormatOf(T), posinf_code(T)) : MaxFiniteOf(T)
Base.typemin(::Type{T}) where {T<:BinaryValue} =
    (is_signed(T) && is_extended(T)) ? rawvalue(BinaryFormatOf(T), neginf_code(T)) :
                                       MinFiniteOf(T)
Base.floatmax(::Type{T}) where {T<:BinaryValue} = MaxFiniteOf(T)
Base.floatmin(::Type{T}) where {T<:BinaryValue} = MinNormalOf(T)
# eps(T) = 2^(1-P): a datum since the grid's lowest exponent 2−P−B ≤ 1−P
Base.eps(::Type{T}) where {T<:BinaryValue} =
    project(BinaryFormatOf(T), RTE_SN, ldexp(1.0, 1 - Int(PrecisionOf(T))))
function Base.precision(::Type{T}; base::Integer = 2) where {T<:BinaryValue}
    base > 1 || throw(DomainError(base, "`base` cannot be less than 2."))
    P = Int(PrecisionOf(T))
    base == 2 ? P : floor(Int, P / log2(base))
end
Base.precision(x::BinaryValue; base::Integer = 2) = precision(typeof(x); base)

# ---- decompose ⇒ hash ⇒ Dict keys and Set elements
#
# Base.hash(::Real) is written in terms of Base.decompose. A datum IS
# sign · S · 2^Q, and the engine already computes that split: round_to_precision
# on an exact datum is pure extraction, not rounding, so the triple cannot
# drift from the engine's own normalization. hash/isequal consistency is easier
# here than in Base: one NaN and no −0.
function Base.decompose(x::BinaryValue)
    isnan(x) && return (0, 0, 0)
    isinf(x) && return (signbit(x) ? -1 : 1, 0, 0)
    r = _canonical_rounded(x)
    (Int(r.sign) * Int(r.S), Int(r.Q), 1)
end
@inline _canonical_rounded(x::BinaryValue) =
    round_to_precision(Int(PrecisionOf(x)), ExponentBiasOf(x), RTE, decode(x), 0, 0)

# ---- widen: the format's promotion carrier. The honest widening of a format
# is not another format (the grid is not a join semilattice) but the carrier
# promotion already targets.
Base.widen(::Type{T}) where {T<:BinaryValue} = promotecarrier(T)

# ---- exponent, significand, frexp
function Base.exponent(x::BinaryValue)
    (isfinite(x) && !iszero(x)) ||
        throw(DomainError(x, "exponent is defined only for finite nonzero values"))
    Int(exponent(decode(x)))
end

# significand must return the SAME type, and the significand of a datum is not
# always a datum of its own format. Whether it can be is a property of the
# FORMAT: significand(x) ∈ [1, 2) needs the binade e = 0 fully populated. An
# extended format spends its top magnitude code on Inf, so that binade is
# complete unless it IS the top binade — exactly when B == 1.
@inline _binade0_complete(::Type{T}) where {T<:BinaryValue} =
    !is_extended(T) || ExponentBiasOf(T) > 1

function Base.significand(x::T) where {T<:BinaryValue}
    (isfinite(x) && !iszero(x)) ||
        throw(DomainError(x, "significand is defined only for finite nonzero values"))
    _binade0_complete(T) || _unsupported("significand", T,
        "the binade [1, 2) of this format is truncated by its Inf encoding, so a " *
        "significand is not always a datum of it, and rounding one here would " *
        "round outside `project`. Use `significand(decode(x))`.")
    d = decode(x)
    # exact: scaling by a power of two moves the exponent field and nothing else
    project(BinaryFormatOf(T), RTE_SN, ldexp(d, -Int(exponent(d))))
end

Base.frexp(x::BinaryValue) = (significand(x) / oftype(x, 2), exponent(x) + 1)

# ---- ldexp: exact on every carrier, then ONE projection. The projection
# rounds only where the result leaves the datum set — below the subnormal
# step (as Base's ldexp does for Float64) or past the range, where the SESSION
# saturation mode decides, agreeing with floor/ceil/round about the top of the
# range. Nearest-even is the rounding, as for every Base verb here.
function Base.ldexp(x::T, n::Integer) where {T<:BinaryValue}
    isfinite(x) || return x                        # NaN and ±Inf are fixed points
    project(BinaryFormatOf(T), Projection(RTE, DefaultSaturationMode()),
            ldexp(decode(x), Int(n)))
end

# ---- eps(x): the ulp at x, from the engine's normalization. Q of the
# canonical form IS the binary exponent of the ulp — normal: e − P + 1;
# subnormal: the constant 2 − B − P. Base's fallback routes through ldexp with
# a floatmin guard; this needs neither. The result is always a datum (every
# power of two in range is), so the projection cannot round.
function Base.eps(x::T) where {T<:BinaryValue}
    isfinite(x) || return rawvalue(BinaryFormatOf(T), nan_code(T))   # Base's oftype(x, NaN)
    iszero(x) && return MinPositiveOf(T)                           # Base's nextfloat(zero)
    r = _canonical_rounded(x)
    project(BinaryFormatOf(T), RTE_SN, ldexp(one(datumcarrier(T)), Int(r.Q)))
end

# ---- round / floor / ceil / trunc
#
# One rounding, not two: the integer-valued result is formed EXACTLY on the
# carrier and projected once. The saturation mode is the session default's, so
# these agree with the other verbs about the top of the range; the ROUNDING
# is the one the verb names.
@inline function _project_default_sat(::Type{F}, μ::RoundingMode, x) where {F<:Binary}
    σ = DefaultSaturationMode()
    if σ === SN
        μ === RTE && return project(F, RTE_SN, x)
        μ === RTA && return project(F, RTA_SN, x)
        μ === RTP && return project(F, RTP_SN, x)
        μ === RTN && return project(F, RTN_SN, x)
        μ === RTZ && return project(F, RTZ_SN, x)
    end
    project(F, Projection(μ, σ), x)
end

for (verb, mode) in ((:trunc, :RTZ), (:floor, :RTN), (:ceil, :RTP), (:round, :RTE))
    @eval function Base.$verb(x::T) where {T<:BinaryValue}
        isfinite(x) || return x
        _project_default_sat(BinaryFormatOf(T), $mode, $verb(decode(x)))
    end
end

# Julia RoundingMode → draft ρ. One method per mode, not one generic
# `::Base.RoundingMode`: Base specializes `round` on individual mode singletons
# for AbstractFloat, so a method generic in the mode is ambiguous with them.
# The list IS the statement of which Julia modes have a P3109 counterpart.
_projmode(::Base.RoundingMode{:Nearest})         = RTE
_projmode(::Base.RoundingMode{:NearestTiesAway}) = RTA
_projmode(::Base.RoundingMode{:Up})              = RTP
_projmode(::Base.RoundingMode{:Down})            = RTN
_projmode(::Base.RoundingMode{:ToZero})          = RTZ
for R in (:Nearest, :NearestTiesAway, :Up, :Down, :ToZero)
    @eval function Base.round(x::T, r::Base.RoundingMode{$(QuoteNode(R))}) where {T<:BinaryValue}
        isfinite(x) || return x
        _project_default_sat(BinaryFormatOf(T), _projmode(r), round(decode(x), r))
    end
end

# the two Base modes with no draft counterpart: RoundNearestTiesUp breaks ties
# toward +∞ where the draft offers ties-to-even and ties-away only; RoundFromZero
# has no ρ at all. Refusing by name beats inheriting Base's fallback, which
# would compute on the carrier and project a result the draft never defined.
for R in (:NearestTiesUp, :FromZero)
    @eval Base.round(::T, ::Base.RoundingMode{$(QuoteNode(R))}) where {T<:BinaryValue} =
        _unsupported("round(x, Round" * $(string(R)) * ")", T,
            "the draft defines no such rounding mode. Its modes with a Julia " *
            "spelling are RoundNearest (RTE), RoundNearestTiesAway (RTA), RoundUp " *
            "(RTP), RoundDown (RTN) and RoundToZero (RTZ); RTO and the stochastic " *
            "families have no `RoundingMode` spelling — name a `Projection` instead.")
end

# ---- deliberate refusals, stated. rem/mod have no draft counterpart: the
# exact remainder is frequently not a datum, so every answer would be a
# rounding the draft does not define.
for f in (:rem, :mod)
    @eval Base.$f(::T, ::T) where {T<:BinaryValue} = _unsupported($(QuoteNode(f)), T,
        "the draft defines no remainder; the exact result is generally not a " *
        "datum, so any answer would round outside `project`. Compute on " *
        "`decode(x)` and `Convert` back if that is what you want.")
end

# =============================================================================
# 4. Conversion and promotion
# =============================================================================

# outbound: the external floats. Float64 is exact for every rung-1 format and
# a rounding conversion (ordinary Julia sense) for the wide ones; the narrow
# targets route through Float64, so the narrowing is one rounding.
Base.Float64(x::BinaryValue) = Float64(decode(x))
Base.Float32(x::BinaryValue) = Float32(Float64(x))
Base.Float16(x::BinaryValue) = Float16(Float64(x))
(::Type{BFloat16})(x::BinaryValue) = BFloat16(Float64(x))
(::Type{Float128})(x::BinaryValue) = Float128(decode(x))
Base.BigFloat(x::BinaryValue) = BigFloat(decode(x))
# integers: exact or InexactError, as for every float. Bool spelled out —
# Base's Bool(::Real) would otherwise be ambiguous with the Integer method.
(::Type{T})(x::BinaryValue) where {T<:Integer} = T(decode(x))
Base.Bool(x::BinaryValue) = Bool(decode(x))

# inbound: `convert` is the value-preserving exception to "Unsigned means code
# point" (plan §4) — assignment into a datum array converts VALUES, so an
# Integer (unsigned included) converts as its value, through Convert.
(::Type{BinaryValue{F,U}})(x::BinaryValue{F,U}) where {F<:Binary, U<:Unsigned} = x
# @inline on both spellings below is worth 4.5x and was measured: without it
# the forwarding method is not inlined and the call costs 7.2 ns against the
# 1.6 ns of the fully spelled `BinaryValue{F,U}(x)` it forwards to. Nothing
# else differs — same guard, same zero allocations.
@inline (::Type{BinaryValue{F}})(x::Real; kw...) where {F<:Binary} =
    BinaryValue{F, CodeType(F)}(x; kw...)
# the two-argument spelling, mirroring `BinaryValue(F, code)` in
# types/binaryvalue.jl. The split there is the split here: an `Unsigned` is a
# CODE POINT and takes no projection, every other `Real` is a VALUE and goes
# through `Convert`. `Unsigned` is the more specific signature, so it keeps
# winning and the two meanings cannot collide.
#
# `Real` rather than the narrower `AbstractFloat`, so that this form accepts
# exactly what the one-argument form accepts — `BinaryValue{F}(3)` works, and
# `BinaryValue(F, 3)` would be a surprising hole. Forwards to the same guarded
# constructor, so it inherits the speculation on the session default and costs
# the same ~2 ns.
@inline BinaryValue(::Type{F}, x::Real; kw...) where {F<:Binary} =
    BinaryValue{F, CodeType(F)}(x; kw...)
@inline BinaryValue(fmt::Binary, x::Real; kw...) = BinaryValue(typeof(fmt), x; kw...)
Base.convert(::Type{T}, x::T) where {T<:BinaryValue} = x
Base.convert(::Type{T}, x::BinaryValue) where {T<:BinaryValue} = T(x)
Base.convert(::Type{T}, x::Real) where {T<:BinaryValue} = T(x)
# the same speculation guard as the value constructor: reading the abstract
# default Ref unconditionally would make every conversion a dynamic call
function Base.convert(::Type{T}, x::Unsigned) where {T<:BinaryValue}
    ρ = DefaultProjection()
    ρ === RTE_SN && return Convert(T, RTE_SN, x)::T
    Convert(T, ρ, x)::T
end
# Rational: consistent with Convert's policy — refused rather than double-rounded
# (and it disambiguates against Base's (::Type{T})(::Rational) for AbstractFloat)
# Spelled once per constructor signature, matching them exactly: a looser
# `T<:BinaryValue` method is ambiguous with both of them.
@noinline _refuse_rational(::Type{T}) where {T<:BinaryValue} =
    throw(ArgumentError("cannot exactly project a Rational into $(formatname(T)); " *
                        "convert explicitly, e.g. $(formatname(T))(Float64(x)), and own the double rounding"))
(::Type{BinaryValue{F,U}})(x::Rational{R}; kw...) where {R, F<:Binary, U<:Unsigned} =
    _refuse_rational(BinaryValue{F,U})
(::Type{BinaryValue{F}})(x::Rational{R}; kw...) where {R, F<:Binary} =
    _refuse_rational(BinaryValue{F, CodeType(F)})
BinaryValue(::Type{F}, x::Rational{R}; kw...) where {R, F<:Binary} =
    _refuse_rational(BinaryValue{F, CodeType(F)})

# promotion: datum ⋄ external number → the format's PUBLIC carrier, never
# Float64 by fiat (a B = 32768 datum has no Float64 at all). promote_rule is
# inherently type-returning and resolves at compile time — a carve-out from
# "no trait returns a Type from a branch", but still derived from a trait.
Base.promote_rule(::Type{T}, ::Type{Float64}) where {T<:BinaryValue} = promotecarrier(T)
Base.promote_rule(::Type{T}, ::Type{Float32}) where {T<:BinaryValue} = promotecarrier(T)
Base.promote_rule(::Type{T}, ::Type{Float16}) where {T<:BinaryValue} = promotecarrier(T)
Base.promote_rule(::Type{T}, ::Type{BFloat16}) where {T<:BinaryValue} = promotecarrier(T)
Base.promote_rule(::Type{T}, ::Type{<:Integer}) where {T<:BinaryValue} = promotecarrier(T)
# the wide carriers themselves: a narrow format meeting a Float128 must not
# come back down to Float64
Base.promote_rule(::Type{T}, ::Type{Float128}) where {T<:BinaryValue} =
    _joinfloat(promotecarrier(T), Float128)
Base.promote_rule(::Type{T}, ::Type{BigFloat}) where {T<:BinaryValue} = BigFloat
_joinfloat(::Type{BigFloat}, ::Type{<:AbstractFloat}) = BigFloat
_joinfloat(::Type{Float128}, ::Type{Float128}) = Float128
_joinfloat(::Type{Float64}, ::Type{Float128}) = Float128

# =============================================================================
# 5. Containers: similar and reinterpret
# =============================================================================

# `Vector{BinaryValue{F}}` (U unspecified) has a non-isbits element type and
# boxes every element — every answer stays right and the performance story is
# gone, silently. Stop the abstraction PROPAGATING through `similar`. Three
# signatures, not one: Base fixes the DIMENSION (similar(::Vector{T})), and a
# fixed dimension outranks a bounded element type.
@inline _concrete_elt(::Type{T}) where {T<:BinaryValue} =
    isconcretetype(T) ? T : BinaryValue{BinaryFormatOf(T), CodeType(T)}

Base.similar(a::AbstractArray{T}) where {T<:BinaryValue} = similar(a, _concrete_elt(T))
Base.similar(a::Vector{T}) where {T<:BinaryValue} = Vector{_concrete_elt(T)}(undef, length(a))
Base.similar(a::Matrix{T}) where {T<:BinaryValue} = Matrix{_concrete_elt(T)}(undef, size(a))

# reinterpret is the idiomatic "same bits, different type", and Julia's generic
# bitcast already applies to an isbits datum — bypassing the representation
# invariant. This more specific method checks what the generic one never
# could. The other direction needs no check: the high bits are already zero.
function Base.reinterpret(::Type{T}, u::U) where {T<:BinaryValue, U<:Unsigned}
    sizeof(U) == sizeof(T) ||
        throw(ArgumentError("reinterpret($(formatname(T)), ::$U): sizes differ " *
                            "($(sizeof(T)) vs $(sizeof(U)) bytes)"))
    u <= codemask(T) ||
        throw(ArgumentError("reinterpret($(formatname(T)), $(repr(u))): the code point " *
                            "must occupy the low $(Int(BitwidthOf(T))) bits (representation " *
                            "invariant); high bits are set. Use `T(u)` for a range-checked " *
                            "code point."))
    rawvalue(BinaryFormatOf(T), CodeType(T)(u))
end
