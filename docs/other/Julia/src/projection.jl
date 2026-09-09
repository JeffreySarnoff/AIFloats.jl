# Source: lib/rounding.maude, lib/saturation.maude, lib/project.maude.
function round_away(m::RoundPolicy, x, fraction, even)
    mode = m.mode
    mode == TO_ZERO && return false
    mode == UP && return fraction > 0 && x > 0
    mode == DOWN && return fraction > 0 && x < 0
    mode == NEAREST_AWAY && return fraction >= 1//2
    if mode == NEAREST_EVEN
        return fraction > 1//2 || (fraction == 1//2 && !even)
    end
    mode == TO_ODD && return fraction > 0 && even
    n, r = m.bits, m.random
    mode == STOCHASTIC_A && return floor(BigInt, fraction*pow2(n))+r >= pow2(n)
    mode == STOCHASTIC_B && return floor(BigInt, fraction*pow2(n+1))+2r+1 >= pow2(n+1)
    return nearest_even_integer(fraction*pow2(n))+r >= pow2(n)
end
function round_to_precision(p::Integer, bias::Integer, m::RoundPolicy, x::ExactValue)
    p >= 1 && bias >= 1 || throw(ArgumentError("invalid precision or bias"))
    x isa SpecialValue && return x
    r = x.value
    iszero(r) && return x
    e = max(floor_log2(abs(r)), 1-bias)-p+1
    t = abs(r)*pow2(-e)
    q = floor(BigInt, t)
    even = p > 1 ? iseven(q) : iszero(q) || iseven(e+bias)
    return finite(sign(r)*(q+round_away(m, r, t-q, even))*pow2(e))
end
function overflow(s::Signedness, d::Domain, positive::Bool)
    d == FINITE && return NAN
    return positive ? POS_INF : s == SIGNED ? NEG_INF : NAN
end
function saturate(
    low,
    high,
    sat::Saturation,
    m::RoundPolicy,
    x::ExactValue,
    s::Signedness,
    d::Domain,
)
    low <= high || throw(ArgumentError("reversed saturation bounds"))
    x === NAN && return NAN
    x isa FiniteValue && low <= x.value <= high && return x
    if sat == SAT_FINITE
        return mathematical_less(x, finite(low)) ? finite(low) : finite(high)
    elseif sat == SAT_PROPAGATE
        x === POS_INF && return d == EXTENDED ? POS_INF : finite(high)
        x === NEG_INF && return d == EXTENDED && s == SIGNED ? NEG_INF : finite(low)
        return x.value < low ? finite(low) : finite(high)
    end
    x === POS_INF && return overflow(s, d, true)
    x === NEG_INF && return overflow(s, d, false)
    x.value > high && m.mode in (TO_ZERO, DOWN) && return finite(high)
    x.value < low && m.mode in (TO_ZERO, UP) && return finite(low)
    return overflow(s, d, x.value > high)
end
"""Project an exact value by rounding, ordered saturation, then encoding once."""
function project(f::BinaryFormat, p::Projection, x::ExactValue)
    x === NAN && return nan_code(f)
    low = decode(f, min_finite_code(f)).value
    high = decode(f, max_finite_code(f)).value
    rounded = round_to_precision(precision_bits(f), exponent_bias(f), p.rounding, x)
    return encode(
        f,
        saturate(low, high, p.saturation, p.rounding, rounded, signedness(f), domain(f)),
    )
end
project(f::Format, p::Projection, x::Residual) =
    residual(:project, f, p, x; reason = :uncertified_projection)
