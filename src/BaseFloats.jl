module BaseMicroFloats

export AbstractMicroFloat, AkoBaseMicroFloat, 
       BaseMicroFloat, 
       bitwidth, precision, encoding, values,
       nvalues, nfractions, nexponents, nfractioncycles, nexponentcycles

import Base: precision, values

abstract type AbstractMicroFloat{Bitwidth, Precision}  <: AbstractFloat end
abstract type AkoBaseMicroFloat{Bitwidth, Precision} <: AbstractMicroFloat{Bitwidth, Precision} end

include("construct.jl")
include("type.jl")

include("aqua.jl")

end  # BaseMicroFloats
