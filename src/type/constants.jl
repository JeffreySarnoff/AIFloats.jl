# 7 small bitwidths (UInt8 encoded)
const BitsSmallMin, BitsSmallMax =  2, 8
# 7 large bitwidths (UInt16 encoded)
const BitsLargeMin, BitsLargeMax =  11, 15
const BitsTop = 16

# internal assurances
setprecision(BigFloat, 1024)

two(T) = typeforfloat(nbits(T))(2)

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
- `Float32` for bitwidths  <= 7
- `Float64` for bitwidths  > 8
- `Float128` for bitwidths > 11
- `BigFloat` for bitwidths > 13

see also [`CODE`](@ref)
""" FLOAT, FLOAT_TYPES

# const FLOAT_TYPES = (Float32, Float64)
# const FLOAT = Union{FLOAT_TYPES...}

const FLOAT_TYPES = (Float64, Float128, BigFloat)
const FLOAT = Union{FLOAT_TYPES...}

"""
    typeforcode(bitwidth)

The bitstype to be used for encoding values of `bitwidth`

It is an *unchecked error* to set bitwidth outside BitsMin..BitsMax
""" typeforcode

typeforcode(Bits) = CODE_TYPES[1 + (Bits > BitsSmallMax)]
typeforcode(Bits::StaticInt{N}) where {N} =
    ifelse(Bits <= static(BitsSmallMax), CODE_TYPES[1], CODE_TYPES[2])

typeforcode(T::Type{<:AbstractAIFloat}) = typeforcode(nbits(T))

"""
    typeforfloat(bitwidth)

The bitstype to be used for storing values of `bitwidth`

It is an *unchecked error* to set bitwidth outside BitsMin..BitsMax
""" typeforfloat

typeforfloat(Bits) = FLOAT_TYPES[1 + (Bits > BitsSmallMax) + (Bits >= BitsLargeMin)]
typeforfloat(Bits::StaticInt{N}) where {N} =
    ifelse(Bits <= static(BitsSmallMax), FLOAT_TYPES[1], ifelse(Bits < BitsLargeMin, FLOAT_TYPES[2], FLOAT_TYPES[3]))

typeforfloat(T::Type{<:AbstractAIFloat}) = typeforfloat(nbits(T))

