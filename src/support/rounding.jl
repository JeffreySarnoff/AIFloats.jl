const RoundStochastic = RoundingMode(:Stochastic)
const RoundToOdd = RoundingMode(:Odd)


function round_up_saturate(xs::T, x::F) where {T<:AbsUnsignedFloat, F<:AbstractFloat}
    idx = searchsortedfirst(floats(xs), x)  # floats(xs)[idx] >= x
    val = floats(xs)[idx]
    if isnan(val)
        idx -= 1
        val = floats(xs)[idx]   
    end
    (idx % typeforcode(nBits(T)), val)
end

function round_down_saturate(xs::T, x::F) where {T<:AbsUnsignedFloat, F<:AbstractFloat}
    idx = searchsortedfirst(floats(xs), x)
    if x == floats(xs)[idx]
        return (idx % typeforcode(nBits(T)), floats(xs)[idx])
    end
    idx = max(1, idx - 1)
    val = floats(xs)[idx]
    (idx % typeforcode(nBits(T)), val)
end

function round_tozero_saturate(xs::T, x::F) where {T<:AbsUnsignedFloat, F<:AbstractFloat}
    round_down_saturate(xs, x)
end

function round_fromzero_saturate(xs::T, x::F) where {T<:AbsUnsignedFloat, F<:AbstractFloat}
    round_up_saturate(xs, x)
end

