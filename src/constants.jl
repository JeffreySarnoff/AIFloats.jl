<<<<<<< HEAD
# 7 small bitwidths (UInt8 encoded)
const BitsSmallMin, BitsSmallMax =  2, 8
# 7 large bitwidths (UInt16 encoded)
const BitsLargeMin, BitsLargeMax =  9, 15
=======
const BitsMin = 2
const BitsMaxSmall = 8
const BitsMinLarge = 9
const BitsMax = 15
>>>>>>> origin/apply-bestie

# internal assurances
setprecision(BigFloat, 1024)

const One = Int32(1)
const Two = Int32(2)
const fpTwo = Float32(2)
const bfTwo = BigFloat(2)

<<<<<<< HEAD
=======
const IsUnsigned = false
const IsSigned   = true

const IsFinite   = false
const IsExtended = true

>>>>>>> origin/apply-bestie
"""
    CODE

The built-in Unsigned Integer types available for encodings.
- `UInt8` for bitwidths <= 8
- `UInt16` for bitwidths > 8

see also [`FLOAT`](@ref)
""" CODE, CODE_TYPES

const CODE_TYPES = (UInt8, UInt16)
const CODE = Union{CODE_TYPES...}

"""
    FLOAT

The built-in floating-point types available for valuations.
- `Float32` for bitwidths <= 8
- `Float64` for bitwidths > 8

see also [`CODE`](@ref)
""" FLOAT, FLOAT_TYPES

const FLOAT_TYPES = (Float32, Float64)
const FLOAT = Union{FLOAT_TYPES...}

"""
    typeforcode(bitwidth)

The bitstype to be used for encoding values of `bitwidth`

It is an *unchecked error* to set bitwidth outside BitsMin..BitsMax
""" typeforcode

typeforcode(Bits) = CODE_TYPES[1 + (Bits <= BitsSmallMax)]
typeforcode(Bits::StaticInt{N}) where {N} =
    ifelse(Bits <= static(BitsSmallMax), CODE_TYPES[1], CODE_TYPES[2])

"""
    typeforfloat(bitwidth)

The bitstype to be used for storing values of `bitwidth`

It is an *unchecked error* to set bitwidth outside BitsMin..BitsMax
""" typeforfloat

typeforfloat(Bits) = FLOAT_TYPES[1 + (Bits <= BitsSmallMax)]
typeforfloat(Bits::StaticInt{N}) where {N} =
<<<<<<< HEAD
    ifelse(Bits <= static(BitsSmallMax), FLOAT_TYPES[1], FLOAT_TYPES[2]))
=======
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

typeforcode(Bits::Integer) =
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
>>>>>>> origin/apply-bestie
