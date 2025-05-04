
abstract type AbstractAIFloat{Bits, SigBits} <: AbstractFloat end

abstract type AbsSignedAIFloat{Bits, SigBits} <: AbstractAIFloat{Bits, SigBits} end
abstract type AbsUnsignedAIFloat{Bits, SigBits} <: AbstractAIFloat{Bits, SigBits} end

abstract type AbsSignedFiniteAIFloat{Bits, SigBits} <: AbsSignedAIFloat{Bits, SigBits} end
abstract type AbsSignedExtendedAIFloat{Bits, SigBits} <: AbsSignedAIFloat{Bits, SigBits} end

abstract type AbsUnsignedFiniteAIFloat{Bits, SigBits} <: AbsUnsignedAIFloat{Bits, SigBits} end
abstract type AbsUnsignedExtendedAIFloat{Bits, SigBits} <: AbsUnsignedAIFloat{Bits, SigBits} end

# Julia Base primitive aspects

Base.precision(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = SigBits
Base.precision(x::T) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = SigBits

# primitive aspects computed over Type Abstractions

for F in (:nBits, :nSigBits, :nFracBits, :nValues, :nNumericValues)
    @eval $F(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = $F(Bits, SigBits)
end

for F in (:nSignBits, :nExpBits,:nMagnitudes)
    @eval begin
       $F(::Type{T}) where {Bits, SigBits, T<:AbsUnsignedAIFloat{Bits, SigBits}} = $F(Bits, SigBits, IsSigned)
       $F(::Type{T}) where {Bits, SigBits, T<:AbsSignedAIFloat{Bits, SigBits}} = $F(Bits, SigBits, IsUnsigned)
    end
end

# primitive aspects computed over Types

for F in (:nBits, :nSigBits, :nFracBits, :nValues, :nNumericValues)
    @eval $F(x::T) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = $F(T)
end

for F in (:nSignBits, :nExpBits,:nMagnitudes)
    @eval begin
       $F(x::T) where {Bits, SigBits, T<:AbsUnsignedAIFloat{Bits, SigBits}} = $F(T)
       $F(x::T) where {Bits, SigBits, T<:AbsSignedAIFloat{Bits, SigBits}} = $F(T)
    end
end

# primitive aspects

nBits(Bits, SigBits)= Bits
nSigBits(Bits, SigBits) = SigBits
nFracBits(Bits, SigBits) = SigBits - oftype(SigBits, 1)
nExpBits(Bits, SigBits, isSigned) = (Bits - SigBits) + (oftype(SigBits, 0) + !isSigned)
nSignBits(Bits, SigBits, isSigned) = oftype(SigBits, 0) + isSigned

nValues(Bits, SigBits) = 2^Bits
nNumericValues(Bits, SigBits) = nValues(Bits, SigBits) - 1 # remove NaN
nMagnitudes(Bits::I, SigBits::I, isSigned::Bool) = nNumericValues(Bits, SigBits) >> (oftype(SigBits, 0) + isSigned)


nFracMagnitudes(Bits, SigBits) = 2^nFracBits(Bits, SigBits)
nNonzeroFracMagnitudes(Bits, SigBits) = nFracMagnitudes(Bits, SigBits) - 1


