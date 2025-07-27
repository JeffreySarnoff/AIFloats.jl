abstract type AbstractAIFloat{Bits, SigBits} <: AbstractFloat end

abstract type AbstractSigned{Bits, SigBits} <: AbstractAIFloat{Bits, SigBits} end
abstract type AbstractUnsigned{Bits, SigBits} <: AbstractAIFloat{Bits, SigBits} end

abstract type AkoSignedFinite{Bits, SigBits} <: AbstractSigned{Bits, SigBits} end
abstract type AkoSignedExtended{Bits, SigBits} <: AbstractSigned{Bits, SigBits} end

abstract type AkoUnsignedFinite{Bits, SigBits} <: AbstractUnsigned{Bits, SigBits} end
abstract type AkoUnsignedExtended{Bits, SigBits} <: AbstractUnsigned{Bits, SigBits} end

