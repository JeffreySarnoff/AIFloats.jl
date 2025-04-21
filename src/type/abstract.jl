
abstract type AbstractFloatML{Bits, SigBits} <: AbstractFloat end

abstract type AbsSignedFloatML{Bits, SigBits}   <: AbstractFloatML{Bits, SigBits} end
abstract type AbsUnsignedFloatML{Bits, SigBits} <: AbstractFloatML{Bits, SigBits} end

abstract type AbsSFiniteFloatML{Bits, SigBits}   <: AbsSignedFloatML{Bits, SigBits} end
abstract type AbsSExtendedFloatML{Bits, SigBits} <: AbsSignedFloatML{Bits, SigBits} end

abstract type AbsUFiniteFloatML{Bits, SigBits}   <: AbsUnsignedFloatML{Bits, SigBits} end
abstract type AbsUExtendedFloatML{Bits, SigBits} <: AbsUnsignedFloatML{Bits, SigBits} end

bitwidth(T::Type{<:AbstractFloatML{Bits, SigBits}}) where {Bits, SigBits} = Bits
Base.precision(T::Type{<:AbstractFloatML{Bits, SigBits}}) where {Bits, SigBits} = SigBits
