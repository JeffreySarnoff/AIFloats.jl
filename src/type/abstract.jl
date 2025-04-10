
abstract type AbstractFloatML{Bits, SigBits} <: AbstractFloat end

abstract type AbsSFloatML{Bits, SigBits}   <: AbstractFloatML{Bits, SigBits} end
abstract type AbsUFloatML{Bits, SigBits} <: AbstractFloatML{Bits, SigBits} end

abstract type AbsSFiniteFloatML{Bits, SigBits}   <: AbsSFloatML{Bits, SigBits} end
abstract type AbsSExtendedFloatML{Bits, SigBits} <: AbsSFloatML{Bits, SigBits} end

abstract type AbsUFiniteFloatML{Bits, SigBits}   <: AbsUFloatML{Bits, SigBits} end
abstract type AbsUExtendedFloatML{Bits, SigBits} <: AbsUFloatML{Bits, SigBits} end

bitwidth(T::Type{<:AbstractFloatML{Bits, SigBits}}) where {Bits, SigBits} = Bits
Base.precision(T::Type{<:AbstractFloatML{Bits, SigBits}}) where {Bits, SigBits} = SigBits
