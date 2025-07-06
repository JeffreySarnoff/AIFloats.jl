import Base: precision, zero, one, eps, nextfloat, prevfloat, floatmax, floatmin, typemax, typemin,
             sign, exponent, significand, sign_mask, exponent_mask, significand_mask

export precision, zero, one, eps, nextfloat, prevfloat, floatmax, floatmin, typemax, typemin,
       sign, exponent, significand, sign_mask, exponent_mask, trailing_significand_mask

function rawbits(x::U) where {U<:Union{UInt8, UInt16}}
    base2 = string(x, base=2)
end

function rawbits(x::U, mask::U) where {U<:Union{UInt8, UInt16}}
    base2 = string(x, base=2)
end

function bits(x::UInt8; uscore=false)
    base2 = string(x, base=2)
    nbits = length(base2)
    xtrabits = 8 - nbits
    morebits = "00000000"[1:xtrabits]
    str = morebits*base2
    if uscore; str = str[1:4] * "_" * str[5:end]; end
    string( "0b", str)
end

# Julia Base primitive attributes

Base.sign_mask(T::Type{<:AbstractUnsigned}) = zero(typeforcode(nBits(T)))
Base.sign_mask(T::Type{<:AbstractSigned}) = one(typeforcode(nBits(T))) << (nBits(T) - 1)

function Base.exponent_mask(T::Type{<:AbstractAIFloat})
    unit = one(typeforcode(nBits(T)))
    mask = (unit << nExpBits(T)) - unit
    mask << nFracBits(T)
end

function trailing_significand_mask(T::Type{<:AbstractAIFloat})
    unit = one(typeforcode(nBits(T)))
    (unit << nFracBits(T)) - unit
end

function unmask(T<:Type{AbstractSigned})
    signmask  = Base.sign_mask(T)
    expmask   = Base.exponent_mask(T)
    fracmask  = Base.trailing_significand_mask(T)
    (; signmask, expmask, fracmask)
end

function unmask(T<:Type{AbstractUnsigned})
    expmask   = Base.exponent_mask(T)
    fracmask  = Base.trailing_significand_mask(T)
    (; expmask, fracmask)
end

function unmask(x::T) where {T<:AbstractSigned}
    smask, emask, fmask = unmask(T)
    sbits, ebits, fbits = (x & smask), (x & emask), (x & fmask)
    "0b" * rawbits(smask, sbits) * "_" * rawbits(emask, ebits) * "_" * rawbits(fmask, fbits)
end

Base.sign(xs::T, x::F) where {T<:AbstractUnsigned, F<:AbstractFloat} = ifelse(iszero(x), x, one(F))
Base.sign(xs::T, x::F) where {T<:AbstractSigned, F<:AbstractFloat} = ifelse(iszero(x), x, (signbit(x) ? -one(F) : one(F)))

Base.precision(T::Type{<:AbstractAIFloat}) = SigBits
Base.precision(x::T) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = SigBits

function Base.eps(xs::T) where {T<:AbstractAIFloat}
    idx1 = index1(T)
    idx1next = idx1 + 0x01
    let flts = view(floats(xs), 1:idx1next)
        flts[end] - flts[end-1]
    end    
end

function Base.eps(xs::T, x::F) where {T<:AbstractUnsignedFinite, F<:AbstractFloat}
    x == 1 && return eps(xs)
    idx1 = value_to_index(xs, x)
    if idx1 === nothing
        return eps(xs)
    end
    idx1 = min(nValues(T)-3, idx1)
    floats(xs)[idx1 + 0x01] - floats(xs)[idx1]
end

function Base.eps(xs::T, x::F) where {T<:AbstractUnsignedExtended, F<:AbstractFloat}
    x == 1 && return eps(xs)
    idx1 = value_to_index(xs, x)
    if idx1 === nothing
        return eps(xs)
    end
    idx1 = min(nValues(T)-4, idx1)
    floats(xs)[idx1 + 0x01] - floats(xs)[idx1]
end

function Base.eps(xs::T, x::F) where {T<:AbstractSignedFinite, F<:AbstractFloat}
    ax = abs(x)
    ax == 1 && return eps(xs)
    idx1 = value_to_index(xs, ax)
    if idx1 === nothing
        return eps(xs)
    end
    idx1 = min((nValues(T)>>1)-1, idx1)
    floats(xs)[idx1 + 0x01] - floats(xs)[idx1]
end

function Base.eps(xs::T, x::F) where {T<:AbstractSignedExtended, F<:AbstractFloat}
    x == 1 && return eps(xs)
    idx1 = value_to_index(xs, x)
    if idx1 === nothing
        return eps(xs)
    end
    idx1 = min(nValues(T)>>1-2, idx1)
    floats(xs)[idx1 + 0x01] - floats(xs)[idx1]
end

function Base.eps(xs::T, x::F) where {T<:AbstractSigned, F<:AbstractFloat}
    x == 1 && return eps(xs)
    idx1 = value_to_index(xs, x)
    if idx1 === nothing
        return eps(xs)
    end
    idx1next = idx1 + 0x01
    if idx1next > nValues(T)
        floats(xs)[idx1] - floats(xs)[idx1 - 1]
    else
        floats(xs)[idx1 + 1] - floats(xs)[idx1]
    end    
end

Base.zero(x::T) where {T<:AbstractAIFloat} = floats(x)[1]
Base.one(x::T) where {T<:AbstractAIFloat} = floats(x)[AIFloats.index1(x)]

function Base.floatmin(x::T) where {T<:AbstractAIFloat}
    nprenormals = nPrenormalMagnitudes(T)
    floats(x)[nprenormals+0x01]
end

function Base.floatmax(x::T) where {T<:AbstractUnsigned}
    floats(x)[nValues(T) - 0x01 - is_extended(T)]
end

function Base.floatmax(x::T) where {T<:AbstractSigned}
    floats(x)[(nValues(T) >> 1) - is_extended(T)]
end

Base.typemin(x::T) where {T<:AbstractUnsigned} = floats(x)[0x01]
Base.typemin(x::T) where {T<:AbstractSigned} = floats(x)[end]

Base.typemax(x::T) where {T<:AbstractUnsigned} = floats(x)[end-1]
Base.typemax(x::T) where {T<:AbstractSigned} = floats(x)[(nValues(T) >> 1)]

"""
    floatleast(x::T) where {T<:AbstractAIFloat}

The smallest positive subnormal value, if any.
Otherwise, the smallest positive normal value.
"""
floatleast(x::T) where {T<:AbstractAIFloat} = floats(x)[2]

function Base.nextfloat(xs::T, x::F) where {T<:AbstractAIFloat, F<:AbstractFloat}
    idx = value_to_index(xs, x)
    if idx === nothing
        return eltype(floats(xs))(NaN)
    end
    if idx == length(floats(xs))
        return floats(xs)[idx]
    end
    floats(xs)[idx + 1]
end

function Base.prevfloat(xs::T, x::F) where {T<:AbstractAIFloat, F<:AbstractFloat}
    idx = value_to_index(xs, x)
    if idx === nothing
        return eltype(floats(xs))(NaN)
    end
    if idx == 1
        return floats(xs)[idx]
    end
    floats(xs)[idx - 1]
end

"""
    ulp_distance(xs, a, b)

For two floating-point numbers a and b, the ULP distance is:
    |a - b| / ULP(max(|a|, |b|))
    where ULP(x) is the spacing between consecutive representable numbers at x.

__UNCHECKED PRECONDITION__: a, b exist in floats(xs)
""" ulp_distance

function ulp_distance(xs, a, b)
    F = eltype(float(xs))
    isnan(a) || isnan(b) && return F(NaN)
    isinf(a) || isinf(b) && return F(Inf)
    a === b && return zero(F)
    
    maxabs = max(abs(a), abs(b))
    ulpvalue = eps(xs, maxabs)
    abs(a - b) / ulpvalue
end
