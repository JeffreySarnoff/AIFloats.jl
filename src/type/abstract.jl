abstract type AbstractAIFloat{Bits, SigBits, IsSigned} <: AbstractFloat end

abstract type AbstractSigned{Bits, SigBits} <: AbstractAIFloat{Bits, SigBits, true} end
abstract type AbstractUnsigned{Bits, SigBits} <: AbstractAIFloat{Bits, SigBits, false} end

abstract type AbstractSignedFinite{Bits, SigBits} <: AbstractSigned{Bits, SigBits} end
abstract type AbstractSignedExtended{Bits, SigBits} <: AbstractSigned{Bits, SigBits} end

abstract type AbstractUnsignedFinite{Bits, SigBits} <: AbstractUnsigned{Bits, SigBits} end
abstract type AbstractUnsignedExtended{Bits, SigBits} <: AbstractUnsigned{Bits, SigBits} end
