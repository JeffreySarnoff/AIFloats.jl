import Base: isnan, isinf, iszero, isone, isfinite


"""
    validate_code(n::Integer, code::Unsigned)

    code or nothing
""" validate_code

@inline function validate_code(n::I, code::U) where {I<:Integer, U<:Unsigned}
    0 <= code < n ? code : nothing
end

"""
    validate_index(n::Integer, code::Unsigned)

    code or nothing
""" validate_index

@inline function validate_index(n::I, idx::U) where {I<:Integer, U<:Unsigned}
    0 <= idx < n ? idx : nothing
end

"""
    code_to_index(n, code)

convert the P3019 encoding to a Julia index
- (64, 0x1e) ↦ 31
- (32, 0x1d) ↦ 30

""" code_to_index

Base.@assume_effects :nothrow function code_to_index(n, code::U) where {U<:Unsigned}
    unsafe_code_to_index(validate_code(n, code))
end

@inline function unsafe_code_to_index(code::U) where {U<:Unsigned}
    code + 0x01
end

unsafe_code_to_index(n::Nothing) = n

code_to_index(code) = unsafe_code_to_index(code)

"""
    index_to_code(n, index)

convert the Julia index (1-based) into a P3109 encoding (0-based)
- (8, 31) ↦ 0x1e
- (9, 30) ↦ 0x1d

""" index_to_code

Base.@assume_effects :nothrow function index_to_code(n, idx::I) where {I<:Integer}
    unsafe_index_to_code(validate_code(n, idx))
end

@inline function unsafe_index_to_code(idx::I) where {I<:Integer}
    idx - one(I)
end

unsafe_index_to_code(n::Nothing) = n

index_to_code(idx) = unsafe_index_to_code(idx)

"""
    code_to_value(values, code)

    - values[code+1] i f   0 <= code < length(values)
                     else NaN
""" code_to_value

function code_to_value(xs::T, code::U) where {T<:AbstractVector{<:AbstractFloat}, U<:Unsigned}
    code = unsafe_code_to_value(xs, code)
    isnothing(code) && throw(DomainError("value $code not found in $xs"))
    code
end

unsafe_code_to_value(xs, code) = xs[unsafe_code_to_index(code)]

"""
    value_to_code

""" value_to_code

function value_to_code(xs::T, val::F) where {T<:AbstractVector{<:AbstractFloat}, F<:AbstractFloat}
    code = unsafe_value_to_code(xs, val)
    isnothing(code) && throw(DomainError(val, "value $val not found in $xs"))
    code
end

unsafe_value_to_code(xs::T, val::F) where {T<:Vector{<:AbstractFloat}, F<:AbstractFloat} =
    unsafe_index_to_code(unsafe_value_to_index(xs, val))

"""
    index_to_value(values, idx)

    - values[idx] if   0 < idx <= length(values)
                  else NaN

""" index_to_value

function index_to_value(xs::T, x::I) where {T<:AbstractVector{<:AbstractFloat}, I<:Integer}
    code = unsafe_index_to_value(xs, x)
    isnothing(code) && throw(DomainError(x, "index $x not found in $xs"))
    code
end

unsafe_index_to_value(xs::T, x::I) where {T<:AbstractVector{<:AbstractFloat}, I<:Integer} = xs[x]

"""
    value_to_index

""" value_to_index

@inline function value_to_index(xs::T, x::F) where {T<:Vector{<:AbstractFloat}, F<:AbstractFloat}
    idx = unsafe_value_to_index(xs, x)
    isnothing(idx) && throw(DomainError(x, "value_to_index: value $x not found in $xs"))
    idx
end

unsafe_value_to_index(xs::T, x::F) where {T<:AbstractVector{<:AbstractFloat}, F<:AbstractFloat} =
    findfirst(isequal(x), xs)

value_to_index(aif::T, x::F) where {T<:AbstractAIFloat, F<:AbstractFloat} =
    value_to_index(floats(aif), x)


@inline function index_to_value(xs::T, index::Integer) where {T<:Vector{AbstractFloat}}
    if index < 1 || index > length(xs)
        return eltype(xs)(NaN)
    end
    xs[index]
end

@inline function value_to_indexgte(aif::T, x::F) where {T<:AbstractAIFloat, F<:AbstractFloat}
    findfirst(>=(x), floats(aif))
end

@inline function value_to_indexgte(xs::T, x::F) where {T<:Vector{<:AbstractFloat}, F<:AbstractFloat}
    findfirst(>=(x), xs)
end

@inline function value_to_indices(aif::T, x::F) where {T<:AbstractAIFloat, F<:AbstractFloat}
    hi = value_to_indexgte(aif, x)
    isnothing(hi) && return (nothing, nothing)
    if !isnothing(hi) && x == float(aif)[hi]
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

# code points

code_zero(T::Type{<:AbstractAIFloat}) = zero(typeforcode(T))

code_one(T::Type{<:AbstractUnsigned}) = ((nvalues(T) % UInt16) >> 0x0001)
code_one(T::Type{<:AbstractSigned}) = ((nvalues(T) % UInt16) >> 0x0002)
code_negone(T::Type{<:AbstractSigned}) = (((nvalues(T) % UInt16) >> 0x0002) + nvalues(T)>>1)
code_negone(T::Type{<:AbstractUnsigned}) = nothing # throw(DomainError(T, "index_negone: T must be an AbstractSigned type, not $T"))

code_nan(T::Type{<:AbstractUnsigned}) = ((nvalues(T) % UInt16) - 0x0001)
code_nan(T::Type{<:AbstractSigned}) = ((nvalues(T) % UInt16) >> 0x0001)
 
code_posinf(T::Type{<:AkoUnsignedExtended}) = ((nvalues(T) - 1) % UInt16)
code_posinf(T::Type{<:AkoSignedExtended}) = ((nvalues(T) % UInt16) >> 0x0001)
code_posinf(T::Type{<:AkoUnsignedFinite}) = nothing
code_posinf(T::Type{<:AkoSignedFinite}) = nothing

code_neginf(T::Type{<:AkoSignedExtended}) = (nvalues(T) % UInt16)
code_neginf(T::Type{<:AkoSignedFinite}) = nothing # throw(DomainError(T, "code_neginf: T must be an AkoSignedExtended type, not $T"))
code_neginf(T::Type{<:AbstractUnsigned}) = nothing # throw(DomainError(T, "code_neginf: T must be an AkoSignedExtended type, not $T"))

index_zero(T::Type{<:AbstractUnsigned}) = code_to_index(code_zero(T))

index_one(T::Type{<:AbstractAIFloat}) = unsafe_code_to_index(code_one(T))
index_negone(T::Type{<:AbstractAIFloat}) = unsafe_code_to_index(code_negone(T))
index_negone(T::Type{<:AbstractUnsigned}) = nothing # throw(DomainError(T, "ofs_negone: T must be an AbstractSigned type, not $T"))

index_nan(T::Type{<:AbstractAIFloat}) = unsafe_code_to_index(code_nan(T))
index_posinf(T::Type{<:AkoUnsignedExtended}) = unsafe_code_to_index(code_posinf(T))
index_posinf(T::Type{<:AkoSignedExtended}) = unsafe_code_to_index(code_posinf(T))
index_neginf(T::Type{<:AkoSignedExtended}) = unsafe_code_to_index(code_neginf(T))
index_neginf(T::Type{<:AkoSignedFinite}) = nothing # throw(DomainError(T, "ofs_neginf: T must be an AkoSignedExtended type, not $T"))
index_neginf(T::Type{<:AbstractUnsigned}) = nothing # throw(DomainError(T, "ofs_neginf: T must be an AkoSignedExtended type, not $T"))
 
 # cover instantiations
 for F in (:code_zero, :code_one, :code_negone, :code_nan, :code_posinf, :code_neginf,
           :index_zero, :index_one, :index_negone, :index_nan, :index_posinf, :index_neginf)
    @eval begin
        $F(aif::T) where {T<:AbstractAIFloat} = $F(T)
        # $F(xs::Vector{T}, x::U) where {T<:AbstractFloat, U<:Unsigned} = $F(T)
    end
 end

# predicates

iscode_zero(T::Type{<:AbstractAIFloat}, code::U) where {U<:Unsigned} = code_zero(T) == code
iscode_one(T::Type{<:AbstractAIFloat}, code::U) where {U<:Unsigned} = code_one(T) == code
iscode_negone(T::Type{<:AbstractSigned}, code::U) where {U<:Unsigned} = code_negone(T) == code
iscode_negone(T::Type{<:AbstractUnsigned}, code::U) where {U<:Unsigned} = false

iscode_nan(T::Type{<:AbstractAIFloat}, code::U) where {U<:Unsigned} = code_nan(T) == code

iscode_posinf(T::Type{<:AkoUnsignedExtended}, code::U) where {U<:Unsigned} = code_posinf(T) == code
iscode_posinf(T::Type{<:AkoSignedExtended}, code::U) where {U<:Unsigned} = code_posinf(T) == code
iscode_neginf(T::Type{<:AkoSignedExtended}, code::U) where {U<:Unsigned} = code_neginf(T) == code
iscode_inf(T::Type{<:AbstractAIFloat}, code::U) where {U<:Unsigned} = iscode_posinf(T, code) || iscode_neginf(T, code)
iscode_posinf(T::Type{<:AkoUnsignedFinite}, code::U) where {U<:Unsigned} = false
iscode_neginf(T::Type{<:AkoUnsignedFinite}, code::U) where {U<:Unsigned} = false
iscode_inf(T::Type{<:AkoUnsignedFinite}, code::U) where {U<:Unsigned} = false
iscode_posinf(T::Type{<:AkoSignedFinite}, code::U) where {U<:Unsigned} = false
iscode_neginf(T::Type{<:AkoSignedFinite}, code::U) where {U<:Unsigned} = false
iscode_inf(T::Type{<:AkoSignedFinite}, code::U) where {U<:Unsigned} = false

isindex_zero(T::Type{<:AbstractAIFloat}, idx::U) where {U<:Unsigned} = iscode_zero(T, index_to_code(idx))
isindex_one(T::Type{<:AbstractAIFloat}, idx::U) where {U<:Unsigned} = iscode_one(T, index_to_code(idx))
isindex_negone(T::Type{<:AbstractAIFloat}, idx::U) where {U<:Unsigned} = iscode_negone(T, index_to_code(idx))

isindex_nan(T::Type{<:AbstractAIFloat}, idx::U) where {U<:Unsigned} = iscode_nan(T, index_to_code(idx))

isindex_posinf(T::Type{<:AbstractAIFloat}, idx::U) where {U<:Unsigned} = iscode_posinf(T, index_to_code(idx))
isindex_neginf(T::Type{<:AbstractAIFloat}, idx::U) where {U<:Unsigned} = iscode_neginf(T, index_to_code(idx))
isindex_inf(T::Type{<:AbstractAIFloat}, idx::U) where {U<:Unsigned} = iscode_inf(T, index_to_code(idx))

for F in (:iscode_zero, :iscode_one, :iscode_negone, :iscode_nan, :iscode_inf, :iscode_posinf, :iscode_neginf,
          :isindex_zero, :isindex_one, :isindex_negone, :isindex_nan, :isindex_inf, :isindex_posinf, :isindex_neginf)
    @eval $F(aif::T) where {T<:AbstractAIFloat} = $F(T)
end
