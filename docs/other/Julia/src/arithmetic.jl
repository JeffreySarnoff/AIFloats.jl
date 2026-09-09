# Source: lib/omega-arithmetic.maude, lib/omega-extrema.maude.
negate(x::FiniteValue) = finite(-x.value)
negate(x::SpecialValue) = x === NAN ? NAN : x === POS_INF ? NEG_INF : POS_INF
magnitude(x::FiniteValue) = finite(abs(x.value))
magnitude(x::SpecialValue) = x === NAN ? NAN : POS_INF
function add(x::ExactValue, y::ExactValue)
    (is_nan(x) || is_nan(y)) && return NAN
    x isa FiniteValue && y isa FiniteValue && return finite(x.value+y.value)
    is_infinite(x) && is_infinite(y) && return x === y ? x : NAN
    return is_infinite(x) ? x : y
end
function multiply(x::ExactValue, y::ExactValue)
    (is_nan(x) || is_nan(y)) && return NAN
    x isa FiniteValue && y isa FiniteValue && return finite(x.value*y.value)
    (mathematical_equal(x, finite(0)) || mathematical_equal(y, finite(0))) && return NAN
    return is_negative(x) == is_negative(y) ? POS_INF : NEG_INF
end
function divide(x::ExactValue, y::ExactValue)
    (is_nan(x) || is_nan(y) || mathematical_equal(y, finite(0))) && return NAN
    is_infinite(x) && is_infinite(y) && return NAN
    is_infinite(y) && return finite(0)
    is_infinite(x) && return is_negative(x) == is_negative(y) ? POS_INF : NEG_INF
    return finite(x.value/y.value)
end
subtract(x, y) = add(x, negate(y))
reciprocal(x) = divide(finite(1), x)
fused_multiply_add(x, y, z) = add(multiply(x, y), z)
fused_add_add(x, y, z) = add(add(x, y), z)
function copy_sign(x, y)
    (is_nan(x) || is_nan(y)) && return NAN
    s = is_negative(y)
    return s === UNKNOWN ? residual(:omegaCopySign, x, y) : s ? negate(magnitude(x)) : magnitude(x)
end
function extrema(x, y; maximum = false, number = false, finite_only = false, by_magnitude = false)
    is_nan(x) && return number || finite_only ? y : NAN
    is_nan(y) && return number || finite_only ? x : NAN
    if finite_only
        is_infinite(x) && is_finite(y) && return y
        is_finite(x) && is_infinite(y) && return x
    end
    a, b = by_magnitude ? (magnitude(x), magnitude(y)) : (x, y)
    lt, le = mathematical_less(a, b), mathematical_le(b, a)
    if by_magnitude && mathematical_equal(a, b) === true
        return extrema(x, y; maximum)
    end
    lt === true && return maximum ? y : x
    le === true && return maximum ? x : y
    return residual(:extrema, x, y, maximum, number, finite_only, by_magnitude)
end
function clamp_value(x, low, high)
    (is_nan(x) || is_nan(low) || is_nan(high)) && return NAN
    mathematical_less(high, low) === true && return NAN
    mathematical_le(low, high) === true || return residual(:omegaClamp, x, low, high)
    return extrema(extrema(x, low; maximum = true), high)
end

# A partial subexpression remains visible when composed with another operation.
negate(x::Residual) = residual(:omegaNegate, x)
magnitude(x::Residual) = residual(:omegaAbs, x)
add(x::Residual, y) = residual(:omegaAdd, x, y)
add(x, y::Residual) = residual(:omegaAdd, x, y)
add(x::Residual, y::Residual) = residual(:omegaAdd, x, y)
multiply(x::Residual, y) = residual(:omegaMultiply, x, y)
multiply(x, y::Residual) = residual(:omegaMultiply, x, y)
multiply(x::Residual, y::Residual) = residual(:omegaMultiply, x, y)
divide(x::Residual, y) = residual(:omegaDivide, x, y)
divide(x, y::Residual) = residual(:omegaDivide, x, y)
divide(x::Residual, y::Residual) = residual(:omegaDivide, x, y)
