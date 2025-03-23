module BaseFloats

export AbstractMicroFloat, AkoBaseFloat, 
       BaseFloat, 
       bitwidth, precision, encoding, values,
       nvalues, nfractions, nexponents, nfractioncycles, nexponentcycles

import Base: precision, values

"""
    AbstractFloatML{Bitwidth, Precision}

our extended family of floating-point types for machine learning

- `Bitwidth` is the number of bits in the encoding
- `Precision` is the number of bits in the significand
   (includes the implicit bit)
""" AbstractFloatML

"""
    AbsSFloatML{Bitwidth, Precision}
    - AbstractSignedFloatML

our kinds of signed floating-point types for machine learning

- `Bitwidth` is the number of bits in the encoding
- `Precision` is the number of bits in the significand
   (includes the implicit bit)
""" AbsSFloatML

"""
    AbsUFloatML{Bitwidth, Precision}
    - AbstractUnsignedFloatML

our kinds of unsigned floating-point types for machine learning

- `Bitwidth` is the number of bits in the encoding
- `Precision` is the number of bits in the significand
   (includes the implicit bit)
""" AbsUFloatML

"""
    AbstractFloatML{Bitwidth, Precision}

our extended family of floating-point types for machine learning

- `Bitwidth` is the number of bits in the encoding
- `Precision` is the number of bits in the significand
   (includes the implicit bit)
""" AbstractFloatML

# our extended family of floating-point types for machine learning
abstract type AbstractFloatML{Bitwidth, Precision}  <: AbstractFloat end
# some are Signed, having positive and negative values (and 0, NaN)
abstract type AbsSFloatML{B,P} <: AbstractMicroFloat{Bitwidth, Precision} end
# some are Unsigned, having non-negative values only (positives and 0, NaN)
abstract type AbsUFloatML{B,P} <: AbstractMicroFloat{Bitwidth, Precision} end

include("config.jl")
include("construct.jl")
include("type.jl")

include("aqua.jl")

end  # BaseFloats
