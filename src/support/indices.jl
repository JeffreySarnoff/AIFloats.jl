import Base: isnan, isinf, iszero, isone, isfinite

export isnan, isinf, iszero, isone, isfinite,
       idxnan, ofsnan, is_idxnan, is_ofsnan

"""
   index_to_offset(x)

convert the Julia index `x` into a P3109 offset as a UInt16
- (0x040) ↦ 0x0039
- in 0-based languages, this is a do nothing operation

""" index_to_offset

"""
    index_to_code(bits, index)

convert the Julia index (1-based) into a P3109 encoding (0-based)
- (8, 31) ↦ 0x1e
- (9, 30) ↦ 0x1d

""" index_to_code

"""
    offset_to_index(x)

convert the P3109 encoding `x` into a Julia index as an UInt16
- (0x39) ↦ 0x0040
- (255) ↦ 0x01
- in 0-based languages, this is a do nothing operation

""" offset_to_index

"""
    offset_to_code(bits, x)

convert the 0-based offset `x` into a P3109 encoding value as a UInt8|16
- (8, 30) ↦ 0x1e
- (9, 0x1d) ↦ 0x1d

""" offset_to_code

"""
    code_to_index(bits, code)

convert the P3019 encoding to a Julia index
- (8, 0x1e) ↦ 31
- (9, 0x1d) ↦ 30

""" code_to_index

"""
    code_to_offset(bits, code)

convert the P3019 encoding to a (0-based) offset
- (8, 0x1e) ↦ 29
- (9, 0x1d) ↦ 0x1c

""" code_to_offset



"""
    code_to_value(values, code)

    - values[code+1] i f   0 <= code < length(values)
                     else NaN
""" code_to_value

offset_to_value = code_to_value

"""
    index_to_value(values, idx)

    - values[idx] if   0 < idx <= length(values)
                  else NaN

""" index_to_value

"""
    value_to_code

""" value_to_code

"""
    value_to_offset

""" value_to_offset


"""
    value_to_index

""" value_to_index


value_to_index = 1 + value_to_offset


@inline function index_to_offset(x::StaticInt{N}) where {N}
    (x % UInt16) - one(UInt16)
end

@inline index_to_offset(x::U) where {U<:Unsigned} = x - one(UInt16)
@inline index_to_offset(x::I) where {I<:Integer} = index_to_offset(x % UInt16)

@inline index_to_offset(::Type{Target}, x::T) where {Target<:Integer, T<:Integer} = (x - one(T)) % Target

@inline function index_to_offset(xs::T, x::I) where {T<:AbstractAIFloat, I<:Integer}
    !(0x01 <= x <= length(floats(xs))) || throw(DomainError(x, "index_to_offset: index $x out of bounds for $T"))
    index_to_offset(x)
end

@inline function index_to_offset(xs::T, x::I) where {T<:Vector{<:AbstractFloat}, I<:Integer}
    !(0x01 <= x <= length(xs)) || throw(DomainError(x, "index_to_offset: index $x out of bounds for $T"))
    index_to_offset(x)
end

@inline function offset_to_index(x::StaticInt{N}) where {N}
    x % UInt16 + one(UInt16)
end

@inline offset_to_index(x::U) where {U<:Unsigned} = x + one(UInt16)
@inline offset_to_index(x::I) where {I<:Integer} = offset_to_index(x % UInt16)

@inline offset_to_index(::Type{Target}, x::T) where {Target<:Integer, T<:Integer} = (x + one(T)) % Target

@inline function offset_to_index(xs::T, x::I) where {T<:AbstractAIFloat, I<:Integer}
    !(0x01 <= x <= length(floats(xs))) || throw(DomainError(x, "index_to_offset: index $x out of bounds for $T"))
    offset_to_index(x)
end

@inline function offset_to_index(xs::T, x::I) where {T<:Vector{<:AbstractFloat}, I<:Integer}
    !(0x01 <= x <= length(xs)) || throw(DomainError(x, "index_to_offset: index $x out of bounds for $T"))
    offset_to_index(x)
end



@inline function index_to_code(bits, index)
    index_to_offset(index) % typeforcode(bits)
end



@inline index1(::Type{T}) where {T<:AbstractUnsigned} = nValues(T) >> 0x0001 + 0x01
@inline index1(x::T) where {T<:AbstractUnsigned} = index1(T)                                                            

@inline index1(::Type{T}) where {T<:AbstractSigned} = nValues(T) >> 0x02 + 0x01
@inline index1(x::T) where {T<:AbstractSigned} = index1(T)

@inline function value_to_index(xs::T, x::F) where {T<:AbstractAIFloat, F<:AbstractFloat}
    idx = findfirst(isequal(x), floats(xs))
    isnothing(idx) && throw(DomainError(x, "value_to_index: value $x not found in $xs"))
    idx
end

@inline function value_to_index(xs::T, x::F) where {T<:Vector{<:AbstractFloat}, F<:AbstractFloat}
    idx = findfirst(isequal(x), xs)
    isnothing(idx) && throw(DomainError(x, "value_to_index: value $x not found in $xs"))
    idx
 end

@inline function index_to_value(xs::T, index::Integer) where {T<:AbstractAIFloat}
    if index < 1 || index > nValues(T)
        return eltype(floats(xs))(NaN)
    end
    floats(xs)[index]
end

@inline function index_to_value(xs::T, index::Integer) where {T<:Vector{AbstractFloat}}
    if index < 1 || index > length(xs)
        return eltype(xs)(NaN)
    end
    xs[index]
end

@inline function value_to_indexgte(xs::T, x::F) where {T<:AbstractAIFloat, F<:AbstractFloat}
    findfirst(>=(x), floats(xs))
end

@inline function value_to_indexgte(xs::T, x::F) where {T<:Vector{<:AbstractFloat}, F<:AbstractFloat}
    findfirst(>=(x), xs)
end

@inline function value_to_indices(xs::T, x::F) where {T<:AbstractAIFloat, F<:AbstractFloat}
    hi = value_to_indexgte(xs, x)
    isnothing(hi) && return (nothing, nothing)
    if !isnothing(hi) && x == float(xs)[hi]
        lo = hi
    else
        lo = hi - 1
    end
    (lo, hi)
end

@inline function value_to_indices(xs::T, x::F) where {T<:Vector{<:AbstractFloat}, F<:AbstractFloat}
    hi = value_to_indexgte(xs, x)
    isnothing(hi) && return (nothing, nothing)
    if !isnothing(hi) && x == xs[hi]
        lo = hi
    else
        lo = hi - 1
    end
    (lo, hi)
end

@inline function value_to_offset(xs::T, x::F) where {T<:AbstractAIFloat, F<:AbstractFloat}
    index_to_offset(value_to_index(xs, x))
end

@inline function value_to_offset(xs::T, x::F) where {T<:Vector{<:AbstractFloat}, F<:AbstractFloat}
    index_to_offset(value_to_index(xs, x))
end

offset_to_value(xs::T, ofs::Integer) where {T<:AbstractAIFloat} = index_to_value(xs, offset_to_index(ofs))
offset_to_value(xs::Vector{<:AbstractFloat}, ofs::Integer) = index_to_value(xs, offset_to_index(ofs))

idxone(::Type{T}) where {T<:AbstractUnsigned} = (((nValues(T) % UInt16) >> 0x0001) + 0x0001)
idxone(::Type{T}) where {T<:AbstractSigned} = (((nValues(T) % UInt16) >> 0x0002) + 0x0001)
idxnegone(::Type{T}) where {T<:AbstractSigned} = ((((nValues(T) % UInt16) >> 0x0002) + 0x0001) + nValues(T)>>1)
idxnegone(::Type{T}) where {T<:AbstractUnsigned} = nothing # throw(DomainError(T, "idxnegone: T must be an AbstractSigned type, not $T"))

idxnan(::Type{T}) where {T<:AbstractUnsigned} = (nValues(T) % UInt16)
idxnan(::Type{T}) where {T<:AbstractSigned} = (((nValues(T) % UInt16) >> 0x0001) + 0x0001)
 
idxinf(::Type{T}) where {T<:AbstractUnsignedExtended} = ((nValues(T) - 1) % UInt16)
idxinf(::Type{T}) where {T<:AbstractSignedExtended} = ((nValues(T) % UInt16) >> 0x0001)

idxneginf(::Type{T}) where {T<:AbstractSignedExtended} = (nValues(T) % UInt16)
idxneginf(::Type{T}) where {T<:AbstractSignedFinite} = nothing # throw(DomainError(T, "idxneginf: T must be an AbstractSignedExtended type, not $T"))
idxneginf(::Type{T}) where {T<:AbstractUnsigned} = nothing # throw(DomainError(T, "idxneginf: T must be an AbstractSignedExtended type, not $T"))

ofsone(T::Type{<:AbstractAIFloat}) = index_to_offset(idxone(T))
ofsnegone(T::Type{<:AbstractAIFloat}) = index_to_offset(idxnegone(T))
ofsnegone(::Type{T}) where {T<:AbstractUnsigned} = nothing # throw(DomainError(T, "ofsnegone: T must be an AbstractSigned type, not $T"))

ofsnan(T::Type{<:AbstractAIFloat}) = index_to_offset(idxnan(T))
ofsinf(::Type{T}) where {T<:AbstractUnsignedExtended} = index_to_offset(idxinf(T))
ofsinf(::Type{T}) where {T<:AbstractSignedExtended} = index_to_offset(idxinf(T))
ofsneginf(::Type{T}) where {T<:AbstractSignedExtended} = index_to_offset(idxneginf(T))
ofsneginf(::Type{T}) where {T<:AbstractSignedFinite} = nothing # throw(DomainError(T, "ofsneginf: T must be an AbstractSignedExtended type, not $T"))
ofsneginf(::Type{T}) where {T<:AbstractUnsigned} = nothing # throw(DomainError(T, "ofsneginf: T must be an AbstractSignedExtended type, not $T"))
 
 # cover instantiations
 for F in (:idxone, :idxnegone, :idxnan, :idxinf, :idxneginf,
           :ofsone, :ofsnan, :ofsinf, :ofsneginf)
    @eval $F(x::T) where {T<:AbstractAIFloat} = $F(T)
 end

is_idxnan(xs::T, idx::U) where {T<:AbstractAIFloat, U<:Unsigned} = idxnan(T) == idx
is_ofsnan(xs::T, ofs::U) where {T<:AbstractAIFloat, U<:Unsigned} = is_idxnan(xs, offset_to_index(ofs))

Base.isnan(xs::T, x::U) where {T<:AbstractAIFloat, U<:Unsigned} = is_idxnan(xs, x)
Base.isnan(xs::T, x::F) where {T<:AbstractAIFloat, F<:AbstractFloat} = isnan(x)

for F in (:is_idxnan, :is_ofsnan, :isnan)
    @eval $F(x::T) where {T<:AbstractAIFloat} = $F(T)
end

 

