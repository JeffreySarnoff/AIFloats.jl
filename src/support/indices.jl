import Base: isnan, isinf, iszero, isone, isfinite

export isnan, isinf, iszero, isone, isfinite,
       isidx_nan, isofs_nan

"""
    offset_to_index(x)

convert the P3109 encoding `x` into a Julia index as an UInt16
- (0x39) ↦ 0x0040
- (255) ↦ 0x01
- in 0-based languages, this is a do nothing operation
""" offset_to_index
@inline function offset_to_index(x::StaticInt{N}) where {N}
    x % UInt16 + one(UInt16)
end

@inline offset_to_index(x::T) where {T<:Integer} = (x % UInt16) + one(UInt16)

@inline offset_to_index(::Type{Target}, x::T) where {Target<:Integer, T<:Integer} = (x + one(T)) % Target

"""
    offset_to_code(bits, x)

"""

"""
   index_to_offset(x)

convert the Julia index `x` into a P3109 offset as a UInt16
- (0x040) ↦ 0x0039
- in 0-based languages, this is a do nothing operation
""" index_to_offset

@inline function index_to_offset(x::StaticInt{N}) where {N}
    (x % UInt16) - one(UInt16)
end

@inline index_to_offset(x::T) where {T<:Integer} = (x % UInt16) - one(UInt16)

@inline index_to_offset(::Type{Target}, x::T) where {Target<:Integer, T<:Integer} = (x - one(T)) % Target

"""
    index_to_code(bits, index)

convert the Julia index `x` into a P3109 encoding value as a UInt8|16
- (8, 256) ↦ 0xff
- (9, 256) ↦ 0x00ff
""" index_to_code

@inline function index_to_code(bits, index)
    T = bits <= 8 ? UInt8 : UInt16
    index_to_offset(index) % T
end

@inline index1(::Type{T}) where {T<:AbsUnsignedFloat} = nValues(T) >> 0x0001 + 0x01
@inline index1(x::T) where {T<:AbsUnsignedFloat} = index1(T)                                                            

@inline index1(::Type{T}) where {T<:AbsSignedFloat} = nValues(T) >> 0x02 + 0x01
@inline index1(x::T) where {T<:AbsSignedFloat} = index1(T)

@inline function valuetoindex(xs::T, x::F) where {T<:AbstractAIFloat, F<:AbstractFloat}
    findfirst(isequal(x), floats(xs))
end

@inline function indextovalue(xs::T, index::Integer) where {T<:AbstractAIFloat}
    if index < 1 || index > nValues(T)
        return eltype(floats(xs))(NaN)
    end
    floats(xs)[index]
end

@inline function valuetoindexgte(xs::T, x::F) where {T<:AbstractAIFloat, F<:AbstractFloat}
    findfirst(>=(x), floats(xs))
end

@inline function valuetoindices(xs::T, x::F) where {T<:AbstractAIFloat, F<:AbstractFloat}
    hi = valuetoindexgte(xs)
    isnothing(hi) && return (nothing, nothing)
    if !isnothing(hi) && x == float(xs)[hi]
        lo = hi
    else
        lo = hi - 1
    end
    (lo, hi)
end

 idxone(::Type{T}) where {T<:AbsUnsignedFloat} = (((nValues(T) % UInt16) >> 0x0001) + 0x0001)
 idxone(::Type{T}) where {T<:AbsSignedFloat} = (((nValues(T) % UInt16) >> 0x0002) + 0x0001)
 idxnegone(::Type{T}) where {T<:AbsSignedFloat} = ((((nValues(T) % UInt16) >> 0x0002) + 0x0001) + nValues(T)>>1)

 idxnan(::Type{T}) where {T<:AbsUnsignedFloat} = ((nValues(T) % UInt16))
 idxnan(::Type{T}) where {T<:AbsSignedFloat} = (((nValues(T) % UInt16) >> 0x0001) + 0x0001)
 
 idxinf(::Type{T}) where {T<:AbsUnsignedExtendedFloat} = (((nValues(T) - 1) % UInt16))
 idxinf(::Type{T}) where {T<:AbsSignedExtendedFloat} = (((nValues(T) % UInt16) >> 0x0001))
 idxneginf(::Type{T}) where {T<:AbsSignedExtendedFloat} = (((nValues(T) % UInt16) ))
 
 ofsone(T::Type{<:AbstractAIFloat}) = index_to_offset(idxone(T))
 ofsnan(T::Type{<:AbstractAIFloat}) = index_to_offset(idxnan(T))
 ofsinf(::Type{T}) where {T<:AbsUnsignedExtendedFloat} = index_to_offset(idxinf(T))
 ofsinf(::Type{T}) where {T<:AbsSignedExtendedFloat} = index_to_offset(idxinf(T))
 ofsneginf(::Type{T}) where {T<:AbsUnsignedExtendedFloat} = index_to_offset(idxneginf(T))
 ofsneginf(::Type{T}) where {T<:AbsSignedExtendedFloat} = index_to_offset(idxneginf(T))
 
 # cover instantiationsS
 for F in (:idxone, :idxnegone, :idxnan, :idxinf, :idxneginf,
           :ofsone, :ofsnan, :ofsinf, :ofsneginf)
    @eval $F(x::T) where {T<:AbstractAIFloat} = $F(T)
 end

isidx_nan(xs::T, idx::U) where {T<:AbstractAIFloat, U<:Unsigned} = idxnan(xs) == x 
isofs_nan(xs::T, ofs::U) where {T<:AbstractAIFloat, U<:Unsigned} = idxnan(xs) == ofs + 0x01
Base.isnan(xs::T, x::U) where {T<:AbstractAIFloat, U<:Unsigned} = isidx_nan(xs, x)
Base.isnan(xs::T, x::F) where {T<:AbstractAIFloat, F<:AbstractFloat} = isnan(x)

for F in (:isidx_nan, :isofs_nan, :isnan)
    @eval $F(x::T) where {T<:AbstractAIFloat} = $F(T)
end

 

