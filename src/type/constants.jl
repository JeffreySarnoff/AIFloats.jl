# 7 small bitwidths (UInt8 encoded)
const BitsSmallMin, BitsSmallMax =  2, 8
# 7 large bitwidths (UInt16 encoded)
const BitsMidMin, BitsMidMax =  9, 10
const BitsLargerMin, BitsLargreMax =  11, 12
const BitsLargeMin, BitsLargeMax =  13, 15
const BitsTop = 16

# internal assurances
setprecision(BigFloat, 1024)

"""
    safe_max(x)

allows fma via emulation 
""" safe_max

function safe_max(x::T) where {T} 
    fr, xp = frexp(x)
    ldexp(one(T)/2, (xp >> 1) - 3)
end

function safe_min(x::T) where {T}`` 
    fr, xp = frexp(x)
    ldexp(one(T)/2, -(abs((xp >> 1) - 3)))
end

safe_min2exp(x) = exponent(safe_min(x))
safe_max2exp(x) = exponent(safe_max(x))

const Float16min = floatmin(Float32)
const Float16max = floatmax(Float32)
const Float32min = floatmin(Float32)
const Float32max = floatmax(Float32)
const Float64min = floatmin(Float64)
const Float64max = floatmax(Float64)
const Float128min = floatmin(Float128)
const Float128max = floatmax(Float128)

const SafeFloat16min = safe_min(Float16min)
const SafeFloat16max = safe_max(Float16max)
const SafeFloat32min = safe_min(Float32min)
const SafeFloat32max = safe_max(Float32max)
const SafeFloat64min = safe_min(Float64min)
const SafeFloat64max = safe_max(Float64max)
const SafeFloat128min = safe_min(Float128min)
const SafeFloat128max = safe_max(Float128max)

const Float16min_exp = exponent(Float16min)
const Float16max_exp = exponent(Float16max)
const Float32min_exp = exponent(Float32min)
const Float32max_exp = exponent(Float32max)
const Float64min_exp = exponent(Float64min)
const Float64max_exp = exponent(Float64max)
const Float128min_exp = exponent(Float128min)
const Float128max_exp = exponent(Float128max)

const SafeFloat16min_exp = safe_min2exp(Float16min)
const SafeFloat16max_exp = safe_max2exp(Float16max)
const SafeFloat32min_exp = safe_min2exp(Float32min)
const SafeFloat32max_exp = safe_max2exp(Float32max)
const SafeFloat64min_exp = safe_min2exp(Float64min)
const SafeFloat64max_exp = safe_max2exp(Float64max)
const SafeFloat128min_exp = safe_min2exp(Float128min)
const SafeFloat128max_exp = safe_max2exp(Float128max)

two(::Type{T}) where {T<:AbstractAIFloat} = two(typeforfloat(nbits(T)))
two(::Type{T}) where {T<:AbstractFloat} =  2*one(T) 

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

see also [`CODE`](@ref)
""" FLOAT, FLOAT_TYPES

# const FLOAT_TYPES = (Float32, Float64)
# const FLOAT = Union{FLOAT_TYPES...}

const FLOAT_TYPES = (Float64, Float64, Float128, BigFloat)
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

typeforfloat(bits) = FLOAT_TYPES[(0 < bits) + (BitsMidMax < bits) + (BitsLargeMax <= bits)]
type4float(bits) = FLOAT_TYPES[(0 < bits) + (BitsSmallMax < bits) + (BitsMidMax <= bits) + (BitsLargerMax < bits)]
typeforfloat(Bits::StaticInt{N}) where {N} =
    ifelse(Bits <= static(BitsSmallMax), FLOAT_TYPES[1], ifelse(Bits < BitsLargeMin, FLOAT_TYPES[2], FLOAT_TYPES[3]))

typeforfloat(T::Type{<:AbstractAIFloat}) = typeforfloat(nbits(T))

