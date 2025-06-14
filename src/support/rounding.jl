const RoundStochastic = RoundingMode(:Stochastic)
const RoundToOdd = RoundingMode(:Odd)
#=
Floating-point Round-to-Odd (RO) is defined as follows
[7]: if the infinitely-precise but in-range unrounded result of a
floating-point arithmetic operation cannot be represented
exactly in its destination format, the lsb of the rounded result
is set to a ‘1’; otherwise, the rounded result is the same as the
initial exact unrounded result. In common with the IEEE
Round-to-Nearest/Ties-to-Even rounding mode (RN), RO is
unbiased, but introduces approximately twice as much
rounding error as RN. RO is also much simpler to implement
in hardware than RN because it does not need an addition
(with the potential for the sum to cause the exponent of the
rounded result to increment or even overflow).
- Bfloat16 processing for Neural Networks (ARITH 2019)
also see
S. Boldo & G. Melquiond, “Emulation of a FMA and Correctly
Rounded Sums: Proved Algorithms Using Rounding to Odd”, IEEE
Trans. Comp., Vol. 57, no. 4, pp. 462-471, April 2008 

=#

# =
> map(x->searchsortedfirst([1, 3, 5], x), [0, 1, 2, 5, 6])'
                                           1  1  2  3  4
=#

function round_up(xs::T, x::F) where {T<:AbsUnsignedFloat, F<:AbstractFloat}
    isnan(x) && return x
    n = nValues(xs)
    idx = searchsortedfirst(floats(xs), x)  # floats(xs)[idx] >= x
    idx > n && return floats(xs)[end]
    floats(xs)[idx]
end

function round_down(xs::T, x::F) where {T<:AbsUnsignedFloat, F<:AbstractFloat}
    isnan(x) && return x
    n = nValues(xs)
    idx = searchsortedlast(floats(xs), x)  # floats(xs)[idx] >= x
    iszero(idx) && return floats(xs)[end]
    floats(xs)[idx]
end

function round_tozero(xs::T, x::F) where {T<:AbsUnsignedFloat, F<:AbstractFloat}
    round_down(xs, x)
end

function round_fromzero(xs::T, x::F) where {T<:AbsUnsignedFloat, F<:AbstractFloat}
    round_up(xs, x)
end
 
function round_nearesteven(xs::T, x::F) where {T<:AbsUnsignedFloat, F<:AbstractFloat}
    isnan(x) && return x
    n = nValues(xs)
    idx1 = searchsortedfirst(floats(xs), x)  # floats(xs)[idx] >= x
    val1 = floats(xs)[idx]
    (x == val1 || idx1 === 1) && floats(xs)[idx1]
    idx1 >= n && return floats(xs)[end-1]

    idx0 = idx1 - 1
    val0 = floats(xs)[idx0]
    dval0 = x - val0
    dval1 = val1 - x

    if dval0 < dval1
        return val0
    elseif dval0 > dval1
        return val1
    else # dval0 == dval1
        evenbits0 = trailing_zeros((idx0-1) % typeforcode(nBits(T)))
        evenbits1 = trailing_zeros((idx1-1) % typeforcode(nBits(T)))
        if evenbits0 > evenbits1
            return val0  # round to even
        else
            return val1  # round to odd
        end 
    end
end

function round_nearestodd(xs::T, x::F) where {T<:AbsUnsignedFloat, F<:AbstractFloat}
    isnan(x) && return x
    n = nValues(xs)
    idx1 = searchsortedfirst(floats(xs), x)  # floats(xs)[idx] >= x
    val1 = floats(xs)[idx]
    (x == val1 || idx1 === 1) && floats(xs)[idx1]
    idx1 >= n && return floats(xs)[end-1]

    idx0 = idx1 - 1
    val0 = floats(xs)[idx0]
    dval0 = x - val0
    dval1 = val1 - x

    if dval0 < dval1
        return val0
    elseif dval0 > dval1
        return val1
    else # dval0 == dval1
        evenbits0 = trailing_zeros((idx0-1) % typeforcode(nBits(T)))
        evenbits1 = trailing_zeros((idx1-1) % typeforcode(nBits(T)))
        if evenbits1 > evenbits0
            return val0  # round to even
        else
            return val1  # round to odd
        end 
    end
end

function round_nearesttozero(xs::T, x::F) where {T<:AbsUnsignedFloat, F<:AbstractFloat}
    isnan(x) && return x
    n = nValues(xs)
    idx1 = searchsortedfirst(floats(xs), x)  # floats(xs)[idx] >= x
    val1 = floats(xs)[idx]
    (x == val1 || idx1 === 1) && floats(xs)[idx1]
    idx1 >= n && return floats(xs)[end-1]

    idx0 = idx1 - 1
    val0 = floats(xs)[idx0]
    return val0
end

function round_nearestfromzero(xs::T, x::F) where {T<:AbsUnsignedFloat, F<:AbstractFloat}
    isnan(x) && return x
    n = nValues(xs)
    idx1 = searchsortedfirst(floats(xs), x)  # floats(xs)[idx] >= x
    val1 = floats(xs)[idx]
    (x == val1 || idx1 === 1) && floats(xs)[idx1]
    idx1 >= n && return floats(xs)[end-1]
    return val1
end

function round_nearestaway(xs::T, x::F) where {T<:AbsUnsignedFloat, F<:AbstractFloat}
    round_nearesrfromzero(xs, x)
end

# Unsigned Saturating Rounding

function round_up_saturate(xs::T, x::F) where {T<:AbsUnsignedFloat, F<:AbstractFloat}
    isnan(x) && return x
    x > floats(xs)[end-1-is_extended(xs)] && return floats(xs)[end-1-is_extended(xs)]
    round_up(xs, x)
end

function round_down_saturate(xs::T, x::F) where {T<:AbsUnsignedFloat, F<:AbstractFloat}
    isnan(x) && return x
    x > floats(xs)[end-1-is_extended(xs)] && return floats(xs)[end-1-is_extended(xs)]
    round_down(xs, x)
end

function round_tozero_saturate(xs::T, x::F) where {T<:AbsUnsignedFloat, F<:AbstractFloat}
    round_down_saturate(xs, x)
end

function round_fromzero_saturate(xs::T, x::F) where {T<:AbsUnsignedFloat, F<:AbstractFloat}
    round_up_saturate(xs, x)
end

function round_nearesteven_saturate(xs::T, x::F) where {T<:AbsUnsignedFloat, F<:AbstractFloat}
    isnan(x) && return x
    x > floats(xs)[end-1-is_extended(xs)] && return floats(xs)[end-1-is_extended(xs)]
    round_nearesteven(xs, x)
end

function round_nearestodd_saturate(xs::T, x::F) where {T<:AbsUnsignedFloat, F<:AbstractFloat}
    isnan(x) && return x
    x > floats(xs)[end-1-is_extended(xs)] && return floats(xs)[end-1-is_extended(xs)]
    round_nearestodd(xs, x)
end

function round_nearesttozero_saturate(xs::T, x::F) where {T<:AbsUnsignedFloat, F<:AbstractFloat}
    isnan(x) && return x
    x > floats(xs)[end-1-is_extended(xs)] && return floats(xs)[end-1-is_extended(xs)]
    round_nearesttozero(xs, x)
end

function round_nearestfromzero_saturate(xs::T, x::F) where {T<:AbsUnsignedFloat, F<:AbstractFloat}
    isnan(x) && return x
    x > floats(xs)[end-1-is_extended(xs)] && return floats(xs)[end-1-is_extended(xs)]
    round_nearestfromzero(xs, x)
end

function round_toodd_saturate(xs::T, x::F) where {T<:AbsUnsignedFloat, F<:AbstractFloat}
    isnan(x) && return x
    x > floats(xs)[end-1-is_extended(xs)] && return floats(xs)[end-1-is_extended(xs)] 
    x < floats(xs)[1] && return floats(xs)[1] 
    round_toodd(xs, x)
end

# Signed


function round_tozero(xs::T, x::F) where {T<:AbsSignedFloat, F<:AbstractFloat}
    isnan(x) && return x
    ifelse(!signbit(x), round_down(xs, x), round_up(xs, x))
end

function round_fromzero(xs::T, x::F) where {T<:AbsSignedFloat, F<:AbstractFloat}
    isnan(x) && return x
    ifelse(signbit(x), round_down(xs, x), round_up(xs, x))
end

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

