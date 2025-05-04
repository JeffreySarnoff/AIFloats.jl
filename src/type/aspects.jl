# computing over Type Parameters

nBits(Bits::I, SigBits::I) where {I<:Integer} = Bits
nSigBits(Bits::I, SigBits::I) where {I<:Integer} = SigBits
nFracBits(Bits::I, SigBits::I) where {I<:Integer} = SigBits - one(I)
nSignBits(Bits::I, SigBits::I, isSigned::Bool) where {I<:Integer} = zero(I) + isSigned
nExpBits(Bits::I, SigBits::I, isSigned::Bool) where {I<:Integer} = (Bits - SigBits) + !isSigned

nValues(Bits::I, SigBits::I) where {I<:Integer} = 2^Bits
nSigMagnitudes(Bits::I, SigBits::I) where {I<:Integer} = 2^nSigBits(Bits, SigBits)
nFracMagnitudes(Bits::I, SigBits::I) where {I<:Integer} = 2^nFracBits(Bits, SigBits)
nSignMagnitudes(Bits::I, SigBits::I, isSigned::Bool) where {I<:Integer} = (zero(I) + isSigned) << one(I)
nExpMagnitudes(Bits::I, SigBits::I, isSigned::Bool) where {I<:Integer} = 2^nExpBits(Bits, SigBits, isSigned)

# computing over Type Abstractions

nBits(::Type{<:AbstractAIFloat{Bits, SigBits}}) where {Bits, SigBits} = Bits
nSigBits(::Type{<:AbstractAIFloat{Bits, SigBits}}) where {Bits, SigBits} = SigBits
nFracBits(::Type{<:AbstractAIFloat{Bits, SigBits}}) where {Bits, SigBits} = SigBits - 1

nSignBits(::Type{<:AbsSignedFloatML{Bits, SigBits}}) where {Bits, SigBits} = 1
nSignBits(::Type{<:AbsUnsignedFloatML{Bits, SigBits}}) where {Bits, SigBits} = 0

nExpBits(::Type{<:AbsSignedFloatML{Bits, SigBits}}) where {Bits, SigBits} =
    (Bits - SigBits)
nExpBits(::Type{<:AbsUnsignedFloatML{Bits, SigBits}}) where {Bits, SigBits} =
    (Bits - SigBits) + 1

nExpMagnitudes(::Type{T}) where {T<:AbstractAIFloat} = 2^nExpBits(T)

nNonzeroExpMagnitudes(::Type{T}) where {T<:AbstractAIFloat} =
    nExpMagnitudes(T) - 1

nFracMagnitudes(::Type{T}) where {T<:AbstractAIFloat} =
    2^nFracBits(T)

nNonzeroFracMagnitudes(::Type{T}) where {T<:AbstractAIFloat} =
    nFracMagnitudes(T) - 1

# forms for use with AbstractAIFloat
nNaNs(::Type{T}) where {T<:AbstractAIFloat} = 1
nZeros(::Type{T}) where {T<:AbstractAIFloat} = 1

nInfs(::Type{T}) where {T<:AbstractAIFloat} = is_extended(T) * (is_signed(T) + is_extended(T))
nPosInfs(::Type{T}) where {T<:AbstractAIFloat} = zero(Int8) + is_extended(T)
nNegInfs(::Type{T}) where {T<:AbstractAIFloat} = zero(Int8) + (is_signed(T)  & is_extended(T))

nValues(::Type{T}) where {T<:AbstractAIFloat} = 2^nBits(T)

nNumericValues(::Type{T}) where {T<:AbstractAIFloat} = nValues(T) - 1 # remove NaN
nFiniteValues(::Type{T}) where {T<:AbstractAIFloat} = nNumericValues(T) - nInfs(T)

function nMagnitudes(::Type{T}) where {T<:AbsSignedFloatML}
    n = nNumericValues(T)
    (n + isodd(n)) >> 1 # protect Zero
end

nNonzeroMagnitudes(::Type{T}) where {T<:AbstractAIFloat} = nMagnitudes(T) - 1 # remove Zero
nFiniteMagnitudes(::Type{T}) where {T<:AbstractAIFloat} = nMagnitudes(T) - nPosInfs(T)
nNonzeroFiniteMagnitudes(::Type{T}) where {T<:AbstractAIFloat} = nFiniteMagnitudes(T) - 1

nPositiveValues(::Type{T}) where {T<:AbsSignedFloatML} = nMagnitudes(T) - 1    # remove Zero
nNegativeValues(::Type{T}) where {T<:AbsSignedFloatML} = nPositiveValues(T)

nPositiveFiniteValues(::Type{T}) where {T<:AbsUnsignedFloatML} = nPositiveValues(T) - nPosInfs(T)
nNegativeFiniteValues(::Type{T}) where {T<:AbsSignedFloatML} = nNegativeValues(T) - nNegInfs(T)

for F in (:nBits, :nSigBits, :nFracBits, :nSignBits, :nExpBits,
          :nPosInfs, :nNegInfs, :nInfs, :nZeros, :nNaNs,
          :nValues, :nNumericValues, :nFiniteValues,
          :nMagnitudes, :nFiniteMagnitudes, :nNonzeroMagnitudes, :nNonzeroFiniteMagnitudes,
          :nPositiveValues, :nNegativeValues, :nPositiveFiniteValues, :nNegativeFiniteValues,
          :nFracMagnitudes, :nExpMagnitudes)
    @eval $F(x::AbstractAIFloat) = $F(typeof(x))
end

# forms for use with FoundationalFloats

nBits(Bits, SigBits) = Bits
nSigBits(Bits, SigBits) = SigBits
nFracBits(Bits, SigBits) = SigBits - oftype(SigBits, 1)
nSignBits(Bits, SigBits, IsSigned) = oftype(SigBits, 0) + IsSigned

nFracMagnitudes(Bits, SigBits) = 2^nFracBits(Bits, SigBits)
nNonzeroFracMagnitudes(Bits, SigBits) = nFracMagnitudes(Bits, SigBits) - 1

# value counted aspects (characterizing aspects)

nSpecialValues(::Type{T}) where {T<:AbstractAIFloat} = nNaNs(T) + nZeros(T) + nInfs(T)
nSpecialNumbers(::Type{T}) where {T<:AbstractAIFloat} = nZeros(T) + nInfs(T)
nSpecialMagnitudes(::Type{T}) where {T<:AbstractAIFloat} = nZeros(T) + nPosInfs(T)

nOrdinaryValues(::Type{T}) where {T<:AbstractAIFloat} = nValues(T) - nSpecialValues(T)
nOrdinaryNumbers(::Type{T}) where {T<:AbstractAIFloat} = nOrdinaryValues(T)
nOrdinaryMagnitudes(::Type{T}) where {T<:AbstractAIFloat} = nMagnitudes(T) - nSpecialMagnitudes(T)

for F in (:nSpecialValues, :nSpecialNumbers, :nSpecialMagnitudes,
          :nOrdinaryValues, :nOrdinaryNumbers, :nOrdinaryMagnitudes)
    @eval $F(x::AbstractAIFloat) = $F(typeof(x))
end

# value counted aspects (derived aspects)

nNonNumericValues(::Type{T}) where {T<:AbstractAIFloat} = One # the unique NaN
nNonZeroNumericValues(::Type{T}) where {T<:AbstractAIFloat} = nNumericValues(T) - nZeros(T)

# finite values are numeric values by definition
nNonZeroFiniteValues(::Type{T}) where {T<:AbstractAIFloat} =  nFiniteValues(T) - nZeros(T)

# We have one zero, it is considered neither positive nor negative in these definitions.
# When a sign must be assigned to have a well-formed expression, positive is used.

nNonPositiveValues(::Type{T}) where {T<:AbstractAIFloat} = nNegativeValues(T) + nZeros(T)
nNonPositiveFiniteValues(::Type{T}) where {T<:AbstractAIFloat} = nNonPositiveValues(T) - nNegInfs(T)

for (F) in (:nNonPositiveValues, :nNonPositiveFiniteValues)
    @eval $F(x::AbstractAIFloat) = $F(typeof(x))
end

# Zero, PosInf, NegInf are neither subnormal nor normal values
# nSubnormalMagnitudes(AbstractAIFloat{Bits, 1}) == 0

nSubnormalMagnitudes(::Type{T}) where {T<:AbstractAIFloat} = nFracMagnitudes(T) - 1
nSubnormalValues(::Type{T}) where {T<:AbstractAIFloat} = nSubnormalMagnitudes(T) << is_signed(T)

nNormalMagnitudes(::Type{T}) where {T<:AbstractAIFloat} = nFiniteMagnitudes(T) - nSubnormalMagnitudes(T)
nNormalValues(::Type{T}) where {T<:AbstractAIFloat} = nNormalMagnitudes(T) << is_signed(T)

for (F) in (:nSubnormalValues, :nSubnormalMagnitudes, :nNormalValues, :nNormalMagnitudes)
    @eval $F(x::AbstractAIFloat) = $F(typeof(x))
end

# alternative interpretation
nFracCycles(bits, sigbits, isUnsigned) = 2^(bits - sigbits + isUnsigned)
nExpBits(bits, sigbits, isSigned) = bits - sigbits + isSigned
nExpCycles(bits, sigbits) = nFracMagnitudes(bits, sigbits)

nFracCycles(::Type{T}) where {T<:AbstractAIFloat} = nExpMagnitudes(T)
nExpCycles(::Type{T}) where {T<:AbstractAIFloat} = nFracMagnitudes(T)

for F in (:nFracCycles, :nExpCycles)
    @eval $F(x::AbstractAIFloat) = $F(typeof(x))
end
