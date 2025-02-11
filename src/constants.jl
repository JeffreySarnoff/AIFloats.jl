const NTupleOrVec = Union{DenseVector{T}, Tuple{Vararg{T}}} where {T}

const BitsMin = 2
const BitsMaxSmall = 8
const BitsMinLarge = 9
const BitsMax = 15


# internal assurances
const One = Int32(1)
const Two = Int32(2)
const FloatTwo = Float32(2)

const IsUnsigned = false
const IsSigned   = true

const IsFinite   = false
const IsExtended = true

"""
    CODE

The built-in Unsigned Integer types available for encodings.
- `UInt8` for bitwidths <= 8
- `UInt16` for bitwidths > 8

see also [`FLOAT`](@ref)
""" CODE

const CODE_TYPES = (UInt8, UInt16)
const CODE = Union{CODE_TYPES...}

"""
    FLOAT

The built-in floating-point types available for valuations.
- `Float32` for bitwidths <= 8
- `Float64` for bitwidths > 8

see also [`CODE`](@ref)
""" FLOAT

const FLOAT_TYPES = (Float32, Float64)
const FLOAT = Union{FLOAT_TYPES...}

"""
    typeforcode(Bits)

It is an *unchecked error* to set Bits < BitsMin
""" typeforcode

"""
    typeforfloat(Bits)

It is an *unchecked error* to set Bits < BitsMin
""" typeforfloat

typeforcode(Bits::StaticInt{N}) where {N} = 
    ifelse(Bits <= static(BitsMaxSmall), UInt8, UInt16)

typeforfloat(Bits::StaticInt{N}) where {N} =
    ifelse(Bits <= static(BitsMaxSmall), Float32, Float64)

function typeforfloat(Bits::StaticInt{N}, SigBits::StaticInt{M}) where {N, M}
    if SigBits == static(1) && Bits >= static(7)
        Float64
    elseif SigBits == static(3) && Bits >= static(8)
        Float64
    elseif Bits <= static(BitsMaxSmall)
        Float32
    else
        Float64
    end
end
    
typeforcode(Bits::Integer) = 
    ifelse(Bits <= BitsMaxSmall, UInt8, UInt16)

typeforcode(Bits::Integer, SigBits::Integer) = 
    ifelse(Bits <= BitsMaxSmall, UInt8, UInt16)

typeforfloat(Bits::Integer) =
    ifelse(Bits <= BitsMaxSmall, Float32, Float64)

function typeforfloat(Bits::Integer, SigBits::Integer)
    if SigBits == 1 && Bits >= 7
        Float64
    elseif SigBits == 2 && Bits >= 8
        Float64
    elseif Bits <= BitsMaxSmall
        Float32
    else
        Float64
    end
end
