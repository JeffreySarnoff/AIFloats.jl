module BaseFloats

export AbstractFloatML, 
         AbstractSignedFloatML, AbstractUnsignedFloatML,
       confg_floatml, encoding, valuation

"""
    AbstractFloatML{Bitwidth, Precision}

our extended family of floating-point types for machine learning

- `Bitwidth` is the number of bits in the encoding
- `Precision` is the number of bits in the significand
   (includes the implicit bit)
""" AbstractFloatML

"""
    AbstractSignedFloatML{Bitwidth, Precision}

our kinds of signed floating-point types for machine learning

- `Bitwidth` is the number of bits in the encoding
- `Precision` is the number of bits in the significand
   (includes the implicit bit)
""" AbstractSignedFloatML

"""
    AbstractUnsignedFloatML{Bitwidth, Precision}

our kinds of unsigned floating-point types for machine learning

- `Bitwidth` is the number of bits in the encoding
- `Precision` is the number of bits in the significand
   (includes the implicit bit)
""" AbstractUnsignedFloatML

# our extended family of floating-point types for machine learning
abstract type AbstractFloatML{Bitwidth, Precision}  <: AbstractFloat end
# some are Signed, having positive and negative values (and 0, NaN)
abstract type AbstractSignedFloatML{Bitwidth, Precision} <: AbstractFloatML{Bitwidth, Precision} end
# some are Unsigned, having non-negative values only (positives and 0, NaN)
abstract type AbstractUnsignedFloatML{Bitwidth, Precision} <: AbstractFloatML{Bitwidth, Precision} end

include("config.jl")
include("construct.jl")
include("type.jl")

include("aqua.jl")

end  # BaseFloats
