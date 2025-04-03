
abstract type AbstractMLFloat{Bits, SigBits} <: AbstractFloat end

abstract type AbsSignedMLFloat{Bits, SigBits}   <: AbstractMLFloat{Bits, SigBits} end
abstract type AbsUnsignedMLFloat{Bits, SigBits} <: AbstractMLFloat{Bits, SigBits} end

abstract type AbsSignedFiniteMLFloat{Bits, SigBits}   <: AbsSignedMLFloat{Bits, SigBits} end
abstract type AbsSignedExtendedMLFloat{Bits, SigBits} <: AbsSignedMLFloat{Bits, SigBits} end

abstract type AbsUnsignedFiniteMLFloat{Bits, SigBits}   <: AbsUnsignedMLFloat{Bits, SigBits} end
abstract type AbsUnsignedExtendedMLFloat{Bits, SigBits} <: AbsUnsignedMLFloat{Bits, SigBits} end

codes(x::A) where {A<:AbstractMLFloat} = x.codes
floats(x::A) where {A<:AbstractMLFloat} = x.floats

is_signed(@nospecialize(T::Type{<:AbsSignedMLFloat}))     = true
is_signed(@nospecialize(T::Type{<:AbsUnsignedMLFloat}))   = false

is_unsigned(@nospecialize(T::Type{<:AbsSignedMLFloat}))   = false
is_unsigned(@nospecialize(T::Type{<:AbsUnsignedMLFloat})) = true

is_finite(@nospecialize(T::Type{<:AbsSignedFiniteMLFloat}))     = true
is_finite(@nospecialize(T::Type{<:AbsUnsignedFiniteMLFloat}))   = true
is_finite(@nospecialize(T::Type{<:AbsSignedExtendedMLFloat}))   = false
is_finite(@nospecialize(T::Type{<:AbsUnsignedExtendedMLFloat})) = false

is_extended(@nospecialize(T::Type{<:AbsSignedFiniteMLFloat}))     = false
is_extended(@nospecialize(T::Type{<:AbsUnsignedFiniteMLFloat}))   = false
is_extended(@nospecialize(T::Type{<:AbsSignedExtendedMLFloat}))   = true
is_extended(@nospecialize(T::Type{<:AbsUnsignedExtendedMLFloat})) = true

bitwidth(::Type{<:AbstractMLFloat{Bitwidth, Precision}}) where {Bitwidth, Precision} = Bitwidth
precision(::Type{<:AbstractMLFloat{Bitwidth, Precision}}) where {Bitwidth, Precision} = Precision
