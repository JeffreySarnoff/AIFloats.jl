abstract type AbstractAIFloat{Bits, SigBits, IsSigned} <: AbstractFloat end

abstract type AbstractSignedFloat{Bits, SigBits} <: AbstractAIFloat{Bits, SigBits, true} end
abstract type AbstractUnsignedFloat{Bits, SigBits} <: AbstractAIFloat{Bits, SigBits, false} end

abstract type AbstractSignedFinite{Bits, SigBits} <: AbstractSignedFloat{Bits, SigBits} end
abstract type AbstractSignedExtended{Bits, SigBits} <: AbstractSignedFloat{Bits, SigBits} end

abstract type AbstractUnsignedFinite{Bits, SigBits} <: AbstractUnsignedFloat{Bits, SigBits} end
abstract type AbstractUnsignedExtended{Bits, SigBits} <: AbstractUnsignedFloat{Bits, SigBits} end
