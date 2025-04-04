
abstract type AbstractMLFloat{Bits, SigBits} <: AbstractFloat end

abstract type AbsSignedMLFloat{Bits, SigBits}   <: AbstractMLFloat{Bits, SigBits} end
abstract type AbsUnsignedMLFloat{Bits, SigBits} <: AbstractMLFloat{Bits, SigBits} end

abstract type AbsSignedFiniteMLFloat{Bits, SigBits}   <: AbsSignedMLFloat{Bits, SigBits} end
abstract type AbsSignedExtendedMLFloat{Bits, SigBits} <: AbsSignedMLFloat{Bits, SigBits} end

abstract type AbsUnsignedFiniteMLFloat{Bits, SigBits}   <: AbsUnsignedMLFloat{Bits, SigBits} end
abstract type AbsUnsignedExtendedMLFloat{Bits, SigBits} <: AbsUnsignedMLFloat{Bits, SigBits} end

bitwidth(T::Type{<:AbstractMLFloat{Bits, SigBits}}) where {Bits, SigBits} = Bits
Base.precision(T::Type{<:AbstractMLFloat{Bits, SigBits}}) where {Bits, SigBits} = SigBits
