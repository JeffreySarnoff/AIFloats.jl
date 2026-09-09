# Source: lib/projection-spec.maude.
@enum RoundMode NEAREST_EVEN NEAREST_AWAY UP DOWN TO_ZERO TO_ODD STOCHASTIC_A STOCHASTIC_B STOCHASTIC_C
@enum Saturation SAT_NONE SAT_FINITE SAT_PROPAGATE

struct RoundPolicy
    mode::RoundMode
    bits::BigInt
    random::BigInt
    function RoundPolicy(mode::RoundMode, bits::Integer = 0, random::Integer = 0)
        mode <= TO_ODD &&
            (bits != 0 || random != 0) &&
            throw(ArgumentError("deterministic rounding has no random input"))
        random_in_range(bits, random) || throw(ArgumentError("invalid stochastic input"))
        new(mode, big(bits), big(random))
    end
end
random_in_range(n::Integer, r::Integer) = n >= 0 && 0 <= r < big(1) << n
deterministic(m::RoundPolicy) = m.mode <= TO_ODD
struct Projection
    rounding::RoundPolicy
    saturation::Saturation
end
Projection(m::RoundMode, s::Saturation = SAT_NONE) = Projection(RoundPolicy(m), s)
struct BlockProjection{R}
    mode::RoundMode
    saturation::Saturation
    bits::BigInt
    randoms::R
    function BlockProjection(m::RoundMode, s::Saturation = SAT_NONE, n::Integer = 0, rs = ())
        m <= TO_ODD &&
            (n != 0 || !isempty(rs)) &&
            throw(ArgumentError("deterministic block rounding has no random inputs"))
        n >= 0 && all(r -> random_in_range(n, r), rs) ||
            throw(ArgumentError("invalid block random inputs"))
        new{typeof(rs)}(m, s, big(n), rs)
    end
end
valid_block_projection(p::BlockProjection, n) =
    n >= 1 && (
        p.mode <= TO_ODD ||
        (length(p.randoms) == n && all(r -> random_in_range(p.bits, r), p.randoms))
    )
function projection_at(p::BlockProjection, j::Integer)
    j >= 0 || throw(BoundsError(p.randoms, j))
    p.mode <= TO_ODD && return Projection(p.mode, p.saturation)
    j < length(p.randoms) || throw(BoundsError(p.randoms, j))
    r = first(Iterators.drop(p.randoms, Int(j)))
    return Projection(RoundPolicy(p.mode, p.bits, r), p.saturation)
end
singleton_lift(p::Projection) = BlockProjection(
    p.rounding.mode,
    p.saturation,
    p.rounding.bits,
    deterministic(p.rounding) ? () : (p.rounding.random,),
)
Base.:(==)(x::RoundPolicy, y::RoundPolicy) =
    (x.mode, x.bits, x.random) == (y.mode, y.bits, y.random)
Base.:(==)(x::Projection, y::Projection) = x.rounding == y.rounding && x.saturation == y.saturation
Base.:(==)(x::BlockProjection, y::BlockProjection) =
    (x.mode, x.saturation, x.bits, Tuple(x.randoms)) ==
    (y.mode, y.saturation, y.bits, Tuple(y.randoms))
