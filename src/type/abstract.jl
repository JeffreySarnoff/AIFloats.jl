abstract type AbstractAIFloat{Bits, SigBits, IsSigned} <: AbstractFloat end

abstract type AbstractSigned{Bits, SigBits} <: AbstractAIFloat{Bits, SigBits, true} end
abstract type AbstractUnsigned{Bits, SigBits} <: AbstractAIFloat{Bits, SigBits, false} end

abstract type AkoSignedFinite{Bits, SigBits} <: AbstractSigned{Bits, SigBits} end
abstract type AkoSignedExtended{Bits, SigBits} <: AbstractSigned{Bits, SigBits} end

abstract type AkoUnsignedFinite{Bits, SigBits} <: AbstractUnsigned{Bits, SigBits} end
abstract type AkoUnsignedExtended{Bits, SigBits} <: AbstractUnsigned{Bits, SigBits} end

# a broader view of appropriate float types
# UnsignedFinite{bits, sigbits, T<:AbstractFP, S<:Unsigned} <: AkoUnsignedFinite{bits, sigbits}
# 
abstract type AbstractAIFloat{Bits, SigBits, IsSigned} <: AbstractFloat end
const AbstractFP = Union{AbstractFloat, AbstractAIFloat, ArbReal}

