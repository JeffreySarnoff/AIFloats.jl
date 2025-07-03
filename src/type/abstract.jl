abstract type AbstractAIFloat{Bits, SigBits, IsSigned} <: AbstractFloat end

abstract type AbsSignedFloat{Bits, SigBits} <: AbstractAIFloat{Bits, SigBits, true} end
abstract type AbsUnsignedFloat{Bits, SigBits} <: AbstractAIFloat{Bits, SigBits, false} end

abstract type AbsSignedFiniteFloat{Bits, SigBits} <: AbsSignedFloat{Bits, SigBits} end
abstract type AbsSignedExtendedFloat{Bits, SigBits} <: AbsSignedFloat{Bits, SigBits} end

abstract type AbsUnsignedFiniteFloat{Bits, SigBits} <: AbsUnsignedFloat{Bits, SigBits} end
abstract type AbsUnsignedExtendedFloat{Bits, SigBits} <: AbsUnsignedFloat{Bits, SigBits} end
