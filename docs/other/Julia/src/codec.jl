# Source: lib/codec.maude. Membership deliberately does not call encode.
"""Decode a validated integer code to an exact datum."""
function decode(f::BinaryFormat, code::Integer)
    c = checked_code(f, code)
    c == nan_code(f) && return NAN
    domain(f) == EXTENDED && c == positive_limit(f) && return POS_INF
    domain(f) == EXTENDED &&
        signedness(f) == SIGNED &&
        c == (big(1)<<bitwidth(f))-1 &&
        return NEG_INF
    negative = signedness(f) == SIGNED && c > nan_code(f)
    return finite((negative ? -1 : 1) * decode_positive(f, negative ? c-nan_code(f) : c))
end
function decode_positive(f::BinaryFormat, c::Integer)
    q = big(1) << trailing_bits(f)
    e, t = divrem(c, q)
    return (e == 0 ? t : q+t) * pow2(max(e, 1)-exponent_bias(f)-trailing_bits(f))
end
function magnitude_code(f::BinaryFormat, r::Rational)
    r > 0 || throw(DomainError(r, "positive magnitude required"))
    e = max(floor_log2(r), 1-exponent_bias(f))
    c = floor(BigInt, r*pow2(trailing_bits(f)-e))
    return c + (
        e == 1-exponent_bias(f) && r < pow2(e) ? 0 :
        (e+exponent_bias(f)-1) * (big(1)<<trailing_bits(f))
    )
end
function is_datum(f::BinaryFormat, x::ExactValue)
    x === NAN && return true
    x === POS_INF && return domain(f) == EXTENDED
    x === NEG_INF && return domain(f) == EXTENDED && signedness(f) == SIGNED
    r = x.value
    iszero(r) && return true
    r < 0 && signedness(f) == UNSIGNED && return false
    c = magnitude_code(f, abs(r))
    return 0 <= c <= max_finite_code(f) && decode_positive(f, c) == abs(r)
end
"""Encode an exactly representable datum; use `project` for rounding."""
function encode(f::BinaryFormat, x::ExactValue)
    is_datum(f, x) || throw(DomainError(x, "datum is not representable"))
    x === NAN && return nan_code(f)
    x === POS_INF && return positive_limit(f)
    x === NEG_INF && return (big(1)<<bitwidth(f))-1
    iszero(x.value) && return big(0)
    return magnitude_code(f, abs(x.value)) + (x.value < 0 ? nan_code(f) : 0)
end
