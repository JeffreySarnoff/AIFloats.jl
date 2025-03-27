module BaseFloats

export AbstractFloatML, 
         AbstractSignedFloatML, AbstractUnsignedFloatML,
       confg_floatml, encoding, valuation,
       typeforcode, typeforfloat,
       isSigned, isUnsigned, isExtended, isFinite

using AlignedAllocs: memalign_clear
using TupleTools: flatten

"""
    AbstractFloatML{Bits, Precision}

our extended family of floating-point types for machine learning

- `Bits` is the number of bits in the encoding
- `Precision` is the number of bits in the significand
   (includes the implicit bit)
""" AbstractFloatML

"""
    AbstractSignedFloatML{Bits, Precision}

our kinds of signed floating-point types for machine learning

- `Bits` is the number of bits in the encoding
- `Precision` is the number of bits in the significand
   (includes the implicit bit)
""" AbstractSignedFloatML

"""
    AbstractUnsignedFloatML{Bits, Precision}

our kinds of unsigned floating-point types for machine learning

- `Bits` is the number of bits in the encoding
- `Precision` is the number of bits in the significand
   (includes the implicit bit)
""" AbstractUnsignedFloatML

# our extended family of floating-point types for machine learning
abstract type AbstractFloatML{Bits, Precision}  <: AbstractFloat end
# some are Signed, having positive and negative values (and 0, NaN)
abstract type AbstractSignedFloatML{Bits, Precision} <: AbstractFloatML{Bits, Precision} end
# some are Unsigned, having non-negative values only (positives and 0, NaN)
abstract type AbstractUnsignedFloatML{Bits, Precision} <: AbstractFloatML{Bits, Precision} end

# gather the capabilities

include("constants.jl")

include("config.jl")
include("construct.jl")
include("type.jl")

include("aqua.jl")

end  # BaseFloats
