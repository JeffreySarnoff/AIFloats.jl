# 7 small bitwidths (UInt8 encoded)
const BitsSmallMin, BitsSmallMax =  2, 8
# 7 large bitwidths (UInt16 encoded)
const BitsLargeMin, BitsLargeMax =  12, 15
const BitsTop = 16

# internal assurances
setprecision(BigFloat, 1024)

const One = Int32(1)
const Two = Int32(2)

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

# const FLOAT_TYPES = (Float32, Float64)
# const FLOAT = Union{FLOAT_TYPES...}

const FLOAT_TYPES = (Float64, Float64, Float128)
const FLOAT = Union{FLOAT_TYPES...}

"""
    typeforcode(bitwidth)

The bitstype to be used for encoding values of `bitwidth`

It is an *unchecked error* to set bitwidth outside BitsMin..BitsMax
""" typeforcode

typeforcode(Bits) = CODE_TYPES[1 + (Bits > BitsSmallMax)]
typeforcode(Bits::StaticInt{N}) where {N} =
    ifelse(Bits <= static(BitsSmallMax), CODE_TYPES[1], CODE_TYPES[2])

function type4code(bitwidth::Integer)
    (2 <= bitwidth <= 8)  && return UInt8
    (9 <= bitwidth < 16)  && return UInt16
    throw(DomainError(bitwidth, "require: 2 <= bitwidth ($bitwidth) < 16"))
end

"""
    typeforfloat(bitwidth)

The bitstype to be used for storing values of `bitwidth`

It is an *unchecked error* to set bitwidth outside BitsMin..BitsMax
""" typeforfloat

typeforfloat(Bits) = FLOAT_TYPES[1 + (Bits > BitsSmallMax) + (Bits >= BitsLargeMin)]
typeforfloat(Bits::StaticInt{N}) where {N} =
    ifelse(Bits <= static(BitsSmallMax), FLOAT_TYPES[1], ifelse(Bits < BitsLargeMin, FLOAT_TYPES[2], FLOAT_TYPES[3]))

# use with MLFLOATS()
const IsUnsigned = false
const IsSigned   = true
const IsFinite   = false
const IsExtended = true

# convention all caps for Bools, Ints are Static consts

const TRUE = static(true)
const FALSE = static(false)

# use for Bits, SigBits to obtain minimal (fastest) aspect value determinations
for (N, I)  in [(:ZERO, 0), (:ONE, 1), (:TWO, 2), (:THREE, 3), (:FOUR, 4), (:FIVE, 5), (:SIX, 6), (:SEVEN, 7),
                (:EIGHT, 8), (:NINE, 9), (:TEN, 10), (:ELEVEN, 11), (:TWELVE, 12), (:THIRTEEN, 13),
                (:FOURTEEN, 14), (:FIFTEEN, 15), (:SIXTEEN, 16)]
    @eval begin
        const $N = static($I)
    end
end

