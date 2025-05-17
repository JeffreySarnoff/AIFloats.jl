import Base: precision, zero, one, eps, nextfloat, prevfloat, floatmax, floatmin, typemax, typemin

# Julia Base primitive attributes

Base.precision(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = SigBits
Base.precision(x::T) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = SigBits

function Base.eps(x::T) where {T<:AbstractAIFloat}
    idx1 = index1(T)
    idx1next = idx1 + 0x01
    let flts = view(floats(x), 1:idx1next)
        flts[end] - flts[end-1]
    end    
end

Base.zero(x::T) where {T<:AbstractAIFloat} = floats(x)[1]
Base.one(x::T) where {T<:AbstractAIFloat} = floats(x)[AIFloats.index1(x)]

function Base.floatmin(x::T) where {T<:AbstractAIFloat}
    nprenormals = nPrenormalMagnitudes(T)
    floats(x)[nprenormals+0x01]
end

function Base.floatmax(x::T) where {T<:AbsUnsignedFloat}
    floats(x)[nValues(T) - 0x01 - is_extended(T)]
end

function Base.floatmax(x::T) where {T<:AbsSignedFloat}
    floats(x)[(nValues(T) >> 1) - is_extended(T)]
end

Base.typemin(x::T) where {T<:AbsUnsignedFloat} = floats(x)[0x01]
Base.typemin(x::T) where {T<:AbsSignedFloat} = floats(x)[end]

Base.typemax(x::T) where {T<:AbsUnsignedFloat} = floats(x)[end-1]
Base.typemax(x::T) where {T<:AbsSignedFloat} = floats(x)[(nValues(T) >> 1)]

"""
    floatleast(x::T) where {T<:AbstractAIFloat}

The smallest positive subnormal value, if any.
Otherwise, the smallest positive normal value.
"""
floatleast(x::T) where {T<:AbstractAIFloat} = floats(x)[2]
