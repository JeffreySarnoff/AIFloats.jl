
# Unsigned Saturating Rounding

function round_up_saturate(xs::T, x::F) where {T<:AbstractUnsigned, F<:AbstractFloat}
    isnan(x) && return x
    x > floats(xs)[end-1-is_extended(xs)] && return floats(xs)[end-1-is_extended(xs)]
    round_up(xs, x)
end

function round_down_saturate(xs::T, x::F) where {T<:AbstractUnsigned, F<:AbstractFloat}
    isnan(x) && return x
    x > floats(xs)[end-1-is_extended(xs)] && return floats(xs)[end-1-is_extended(xs)]
    round_down(xs, x)
end

function round_tozero_saturate(xs::T, x::F) where {T<:AbstractUnsigned, F<:AbstractFloat}
    round_down_saturate(xs, x)
end

function round_fromzero_saturate(xs::T, x::F) where {T<:AbstractUnsigned, F<:AbstractFloat}
    round_up_saturate(xs, x)
end

function round_nearesteven_saturate(xs::T, x::F) where {T<:AbstractUnsigned, F<:AbstractFloat}
    isnan(x) && return x
    x > floats(xs)[end-1-is_extended(xs)] && return floats(xs)[end-1-is_extended(xs)]
    round_nearesteven(xs, x)
end

function round_nearestodd_saturate(xs::T, x::F) where {T<:AbstractUnsigned, F<:AbstractFloat}
    isnan(x) && return x
    x > floats(xs)[end-1-is_extended(xs)] && return floats(xs)[end-1-is_extended(xs)]
    round_nearestodd(xs, x)
end

function round_nearesttozero_saturate(xs::T, x::F) where {T<:AbstractUnsigned, F<:AbstractFloat}
    isnan(x) && return x
    x > floats(xs)[end-1-is_extended(xs)] && return floats(xs)[end-1-is_extended(xs)]
    round_nearesttozero(xs, x)
end

function round_nearestfromzero_saturate(xs::T, x::F) where {T<:AbstractUnsigned, F<:AbstractFloat}
    isnan(x) && return x
    x > floats(xs)[end-1-is_extended(xs)] && return floats(xs)[end-1-is_extended(xs)]
    round_nearestfromzero(xs, x)
end

function round_toodd_saturate(xs::T, x::F) where {T<:AbstractUnsigned, F<:AbstractFloat}
    isnan(x) && return x
    x > floats(xs)[end-1-is_extended(xs)] && return floats(xs)[end-1-is_extended(xs)] 
    x < floats(xs)[1] && return floats(xs)[1] 
    round_toodd(xs, x)
end

# Signed


function round_tozero(xs::T, x::F) where {T<:AbstractSigned, F<:AbstractFloat}
    isnan(x) && return x
    ifelse(!signbit(x), round_down(xs, x), round_up(xs, x))
end

function round_fromzero(xs::T, x::F) where {T<:AbstractSigned, F<:AbstractFloat}
    isnan(x) && return x
    ifelse(signbit(x), round_down(xs, x), round_up(xs, x))
end

function round_up_saturate(xs::T, x::F) where {T<:AbstractUnsigned, F<:AbstractFloat}
    idx = searchsortedfirst(floats(xs), x)  # floats(xs)[idx] >= x
    val = floats(xs)[idx]
    if isnan(val)
        idx -= 1
        val = floats(xs)[idx]   
    end
    (idx % typeforcode(nBits(T)), val)
end

function round_down_saturate(xs::T, x::F) where {T<:AbstractUnsigned, F<:AbstractFloat}
    idx = searchsortedfirst(floats(xs), x)
    if x == floats(xs)[idx]
        return (idx % typeforcode(nBits(T)), floats(xs)[idx])
    end
    idx = max(1, idx - 1)
    val = floats(xs)[idx]
    (idx % typeforcode(nBits(T)), val)
end

function round_tozero_saturate(xs::T, x::F) where {T<:AbstractUnsigned, F<:AbstractFloat}
    round_down_saturate(xs, x)
end

function round_fromzero_saturate(xs::T, x::F) where {T<:AbstractUnsigned, F<:AbstractFloat}
    round_up_saturate(xs, x)
end

