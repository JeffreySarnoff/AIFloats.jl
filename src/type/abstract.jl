
abstract type AbstractAIFloat{Bits, SigBits} <: AbstractFloat end

abstract type AbsSignedAIFloat{Bits, SigBits} <: AbstractAIFloat{Bits, SigBits} end
abstract type AbsUnsignedAIFloat{Bits, SigBits} <: AbstractAIFloat{Bits, SigBits} end

abstract type AbsSignedFiniteAIFloat{Bits, SigBits} <: AbsSignedAIFloat{Bits, SigBits} end
abstract type AbsSignedExtendedAIFloat{Bits, SigBits} <: AbsSignedAIFloat{Bits, SigBits} end

abstract type AbsUnsignedFiniteAIFloat{Bits, SigBits} <: AbsUnsignedAIFloat{Bits, SigBits} end
abstract type AbsUnsignedExtendedAIFloat{Bits, SigBits} <: AbsUnsignedAIFloat{Bits, SigBits} end

# predicates for abstract types

is_signed(@nospecialize(T::Type{<:AbsSignedAIFloat}))     = true
is_signed(@nospecialize(T::Type{<:AbsUnsignedAIFloat}))   = false

is_unsigned(@nospecialize(T::Type{<:AbsSignedAIFloat}))   = false
is_unsigned(@nospecialize(T::Type{<:AbsUnsignedAIFloat})) = true

is_finite(@nospecialize(T::Type{<:AbsSignedFiniteAIFloat}))     = true
is_finite(@nospecialize(T::Type{<:AbsUnsignedFiniteAIFloat}))   = true
is_finite(@nospecialize(T::Type{<:AbsSignedExtendedAIFloat}))   = false
is_finite(@nospecialize(T::Type{<:AbsUnsignedExtendedAIFloat})) = false

is_extended(@nospecialize(T::Type{<:AbsSignedFiniteAIFloat}))     = false
is_extended(@nospecialize(T::Type{<:AbsUnsignedFiniteAIFloat}))   = false
is_extended(@nospecialize(T::Type{<:AbsSignedExtendedAIFloat}))   = true
is_extended(@nospecialize(T::Type{<:AbsUnsignedExtendedAIFloat})) = true

# predicated counts for abstract types

nNaNs(@nospecialize(T::Type{<:AbstractAIFloat})) = 1
nZeros(@nospecialize(T::Type{<:AbstractAIFloat})) = 1

nInfs(@nospecialize(T::Type{<:AbsSignedFiniteAIFloat}))     = 0
nInfs(@nospecialize(T::Type{<:AbsUnsignedFiniteAIFloat}))   = 0
nInfs(@nospecialize(T::Type{<:AbsSignedExtendedAIFloat}))   = 2
nInfs(@nospecialize(T::Type{<:AbsUnsignedExtendedAIFloat})) = 1

nPosInfs(@nospecialize(T::Type{<:AbstractAIFloat})) = (nInfs(T) + 1) >> 1
nNegInfs(@nospecialize(T::Type{<:AbsSignedAIFloat})) = (nInfs(T) + 1) >> 1
nNegInfs(@nospecialize(T::Type{<:AbsUnsignedAIFloat})) = 0

# Julia Base primitive aspects

Base.precision(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = SigBits
Base.precision(x::T) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = SigBits

# primitive aspects computed over Type Abstractions

for F in (:nBits, :nSigBits, :nFracBits, :nValues, :nNumericValues, :nNonzeroNumericValues,
          :nFracMagnitudes, :nNonzeroFracMagnitudes)
    @eval $F(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = $F(Bits, SigBits)
end

for F in (:nSignBits, :nExpBits,:nMagnitudes, :nNonzeroMagnitudes,
          :nPositiveValues, :nNegativeValues, :nExpValues, :nNonzeroExpValues)
    @eval begin
       $F(::Type{T}) where {Bits, SigBits, T<:AbsUnsignedAIFloat{Bits, SigBits}} = $F(Bits, SigBits, IsUnsigned)
       $F(::Type{T}) where {Bits, SigBits, T<:AbsSignedAIFloat{Bits, SigBits}} = $F(Bits, SigBits, IsSigned)
    end
end

for F in (:nInfs, :nPosInfs, :nNegInfs,
          :nFiniteValues, :nNonzeroFiniteValues, :nPositiveFiniteValues, :nNegativeFiniteValues)
    @eval begin
       $F(::Type{T}) where {Bits, SigBits, T<:AbsUnsignedFiniteAIFloat{Bits, SigBits}} = $F(Bits, SigBits, IsUnsigned, IsFinite)
       $F(::Type{T}) where {Bits, SigBits, T<:AbsUnsignedExtendedAIFloat{Bits, SigBits}} = $F(Bits, SigBits, IsUnsigned, IsExtended)
       $F(::Type{T}) where {Bits, SigBits, T<:AbsSignedFiniteAIFloat{Bits, SigBits}} = $F(Bits, SigBits, IsSigned, IsFinite)
       $F(::Type{T}) where {Bits, SigBits, T<:AbsSignedExtendedAIFloat{Bits, SigBits}} = $F(Bits, SigBits, IsSigned, IsExtended)
    end
end

# primitive aspects computed over Types

for F in (:nZeros, :nNaNs)
    @eval $F(x::T) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = $F(T)
end

for F in (:nBits, :nSigBits, :nFracBits, :nValues, :nNumericValues, :nNonzeroNumericValues,
          :nFracMagnitudes, :nNonzeroFracMagnitudes)
    @eval $F(x::T) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = $F(T)
end

for F in (:nSignBits, :nExpBits, :nMagnitudes, :nNonzeroMagnitudes,
          :nPositiveValues, :nNegativeValues, :nExpValues, :nNonzeroExpValues)
    @eval begin
       $F(x::T) where {Bits, SigBits, T<:AbsUnsignedAIFloat{Bits, SigBits}} = $F(T)
       $F(x::T) where {Bits, SigBits, T<:AbsSignedAIFloat{Bits, SigBits}} = $F(T)
    end
end

for F in (:nInfs, :nPosInfs, :nNegInfs,
          :nFiniteValues, :nPositiveFiniteValues, :nNegativeFiniteValues)
    @eval begin
       $F(x::T) where {Bits, SigBits, T<:AbsUnsignedFiniteAIFloat{Bits, SigBits}} = $F(T)
       $F(x::T) where {Bits, SigBits, T<:AbsUnsignedExtendedAIFloat{Bits, SigBits}} = $F(T)
       $F(x::T) where {Bits, SigBits, T<:AbsSignedFiniteAIFloat{Bits, SigBits}} = $F(T)
       $F(x::T) where {Bits, SigBits, T<:AbsSignedExtendedAIFloat{Bits, SigBits}} = $F(T)
    end
end
