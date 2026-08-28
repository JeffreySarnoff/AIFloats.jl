# random datum generation — every method produces its value through Convert,
# i.e. the single write path into a code point.
#
# rand defaults to RTZ_SN — floor on [0, 1), so each code point receives
# exactly the real measure of its floor interval and the result is provably
# < 1, preserving Julia's documented rand contract. randn defaults to RTE_SF
# so tail draws beyond MaxFiniteOf clamp to the extremal finite datum, never
# ±Inf or NaN.

Random.rand(rng::Random.AbstractRNG,
            ::Random.SamplerTrivial{Random.CloseOpen01{BV}}) where {BV<:BinaryValue} =
    Convert(BV, RTZ_SN, rand(rng, Float64))::BV

@inline Random.rand(rng::Random.AbstractRNG, ::Type{BV};
                    projection::Projection = RTZ_SN) where {BV<:BinaryValue} =
    Convert(BV, projection, rand(rng, Float64); rng)::BV
@inline Random.rand(::Type{BV}; projection::Projection = RTZ_SN) where {BV<:BinaryValue} =
    Random.rand(Random.default_rng(), BV; projection)

function Random.randn(rng::Random.AbstractRNG, ::Type{BV};
                      projection::Projection = RTE_SF) where {BV<:BinaryValue}
    is_signed(BV) ||
        throw(ArgumentError("randn requires a signed format; $(formatname(BV)) cannot represent negative draws"))
    Convert(BV, projection, randn(rng); rng)::BV
end
Random.randn(::Type{BV}; projection::Projection = RTE_SF) where {BV<:BinaryValue} =
    Random.randn(Random.default_rng(), BV; projection)