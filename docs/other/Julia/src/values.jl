# Source: lib/xreal.maude, lib/rational-math.maude.
const ExactRational = Rational{BigInt}

"""A finite exact rational datum; zero has a single representation."""
struct FiniteValue
    value::ExactRational
    function FiniteValue(value::ExactRational)
        denominator(value) != 0 || throw(DomainError(value, "finite rational required"))
        new(value)
    end
end
"""Construct a finite datum without floating-point approximation."""
finite(x::Union{Integer,Rational}) = FiniteValue(ExactRational(x))

@enum SpecialValue NAN POS_INF NEG_INF
const ExactValue = Union{FiniteValue,SpecialValue}
@enum Decision UNKNOWN

"""An unevaluated operation with its arguments and an explicit reason."""
struct Residual
    operation::Symbol
    arguments::Tuple
    reason::Symbol
end
residual(op, args...; reason = :undecided) = Residual(op, args, reason)

Base.:(==)(x::FiniteValue, y::FiniteValue) = x.value == y.value
Base.isequal(x::FiniteValue, y::FiniteValue) = x == y
Base.hash(x::FiniteValue, h::UInt) = hash(x.value, hash(:FiniteValue, h))
Base.:(==)(x::Residual, y::Residual) =
    x.operation == y.operation && x.arguments == y.arguments && x.reason == y.reason
Base.isequal(x::Residual, y::Residual) = x == y
Base.hash(x::Residual, h::UInt) = hash((x.operation, x.arguments, x.reason), h)
Base.show(io::IO, x::FiniteValue) = print(io, "finite(", x.value, ")")
Base.show(io::IO, x::Residual) =
    print(io, "Residual(", x.operation, ", ", x.arguments, ", ", x.reason, ")")

is_nan(x) = x === NAN
is_infinite(x) = x === POS_INF || x === NEG_INF
is_finite(x::FiniteValue) = true
is_finite(x::SpecialValue) = false
is_finite(x::Residual) = false
is_negative(x::FiniteValue) = x.value < 0
is_negative(x::SpecialValue) = x === NEG_INF
value_sign(x::FiniteValue) = sign(x.value)
value_sign(x::SpecialValue) =
    x === POS_INF ? 1 : x === NEG_INF ? -1 : throw(DomainError(x, "NaN has no mathematical sign"))

mathematical_equal(x::FiniteValue, y::FiniteValue) = x == y
mathematical_equal(x::ExactValue, y::ExactValue) = !is_nan(x) && !is_nan(y) && x == y
mathematical_equal(x, y) = UNKNOWN
function mathematical_less(x::ExactValue, y::ExactValue)
    (is_nan(x) || is_nan(y) || x === POS_INF || y === NEG_INF) && return false
    x === NEG_INF && return y !== NEG_INF
    y === POS_INF && return true
    return x.value < y.value
end
mathematical_less(x, y) = UNKNOWN
known_or(x, y) = x === true || y === true ? true : x === false && y === false ? false : UNKNOWN
known_and(x, y) = x === false || y === false ? false : x === true && y === true ? true : UNKNOWN
mathematical_le(x, y) = known_or(mathematical_less(x, y), mathematical_equal(x, y))

pow2(n::Integer) = n >= 0 ? (big(1) << n) // big(1) : big(1) // (big(1) << -n)
function floor_log2(x::Rational)
    x > 0 || throw(DomainError(x, "log2 requires a positive rational"))
    k = ndigits(numerator(x), base = 2) - ndigits(denominator(x), base = 2)
    return x < pow2(k) ? k - 1 : k
end
floor_log2(x::Integer) = floor_log2(big(x) // big(1))
nearest_even_integer(x::Rational) = round(BigInt, x, RoundNearest)
