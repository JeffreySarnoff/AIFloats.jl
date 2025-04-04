# computing over Type Abstractions

nBits(@nospecialize(T::Type{<:AbstractMLFloat{B,P}})) where {B,P} = B
nSigBits(@nospecialize(T::Type{<:AbstractMLFloat{B,P}})) where {B,P} = P
nFracBits(@nospecialize(T::Type{<:AbstractMLFloat{B,P}})) where {B,P} = P - 1

nSignBits(@nospecialize(T::Type{<:AbsUnsignedMLFloat{B,P}})) where {B,P} = 0
nSignBits(@nospecialize(T::Type{<:AbsSignedMLFloat{B,P}})) where {B,P} = 1
nExpBits(@nospecialize(T::Type{<:AbstractMLFloat{B,P}})) where {B,P} = (B - P) + (1 - nSignBits(T))

nExpMagnitudes(@nospecialize(T::Type{<:AbstractMLFloat{B,P}})) where {B,P} = 2^nExpBits(T)
nNonzeroExpMagnitudes(@nospecialize(T::Type{<:AbstractMLFloat{B,P}})) where {B,P} = nExpMagnitudes(T) - 1

nFracMagnitudes(@nospecialize(T::Type{<:AbstractMLFloat{B,P}})) where {B,P} = 2^nFracBits(T)
nNonzeroFracMagnitudes(@nospecialize(T::Type{<:AbstractMLFloat{B,P}})) where {B,P} = nFracMagnitudes(T) - 1

# forms for use with AbstractMLFloat

nNaNs(@nospecialize(T::Type{AbstractMLFloat})) = 1
nZeros(@nospecialize(T::Type{AbstractMLFloat})) = 1

nInfs(@nospecialize(T::Type{AbstractMLFloat})) = is_extended(T) * (is_signed(T) + is_extended(T))
nPosInfs(@nospecialize(T::Type{AbstractMLFloat})) = zero(Int8) + is_extended(T)
nNegInfs(@nospecialize(T::Type{AbstractMLFloat})) = zero(Int8) + (is_signed(T)  & is_extended(T))

nValues(@nospecialize(T::Type{AbstractMLFloat{B,K}})) where {B,K} = 2^B # all values
nNumericValues(@nospecialize(T::Type{AbstractMLFloat})) = nValues(T) - 1 # remove NaN
nFiniteValues(@nospecialize(T::Type{AbstractMLFloat})) = nNumericValues(T) - nInfs(T)

function nMagnitudes(@nospecialize(T::Type{AbsSignedMLFloat}))
    n = nNumericValues(T)
    (n + isodd(n)) >> 1 # protect Zero
end

nNonzeroMagnitudes(@nospecialize(T::Type{AbstractMLFloat})) = nMagnitudes(T) - 1 # remove Zero
nFiniteMagnitudes(@nospecialize(T::Type{AbstractMLFloat})) = nMagnitudes(T) - nPosInfs(T)
nNonzeroFiniteMagnitudes(@nospecialize(T::Type{AbstractMLFloat})) = nFiniteMagnitudes(T) - 1

nPositiveValues(@nospecialize(T::Type{AbsSignedMLFloat})) = nMagnitudes(T) - 1    # remove Zero
nNegativeValues(@nospecialize(T::Type{AbsSignedMLFloat})) = nPositiveValues(T)

nPositiveFiniteValues(@nospecialize(T::Type{AbsUnsignedMLFloat})) = nPositiveValues(T) - nPosInfs(T)
nNegativeFiniteValues(@nospecialize(T::Type{AbsSignedMLFloat})) = nNegativeValues(T) - nNegInfs(T)

for F in (:nBits, :nSigBits, :nFracBits, :nSignBits, :nExpBits,
          :nPosInfs, :nNegInfs, :nInfs, :nZeros, :nNaNs,
          :nValues, :nNumericValues, :nFiniteValues,
          :nMagnitudes, :nFiniteMagnitudes, :nNonzeroMagnitudes, :nNonzeroFiniteMagnitudes,
          :nPositiveValues, :nNegativeValues, :nPositiveFiniteValues, :nNegativeFiniteValues,
          :nFracMagnitudes, :nExpMagnitudes)
    @eval $F(x::AbstractMLFloat) = $F(typeof(x))
end

# forms for use with FoundationalFloats

nBits(Bits, SigBits) = Bits
nSigBits(Bits, SigBits) = SigBits
nFracBits(Bits, SigBits) = SigBits - oftype(SigBits, 1)
nSignBits(Bits, SigBits, IsSigned) = oftype(SigBits, 0) + IsSigned

nFracMagnitudes(Bits, SigBits) = 2^nFracBits(Bits, SigBits)
nNonzeroFracMagnitudes(Bits, SigBits) = nFracMagnitudes(Bits, SigBits) - 1

# value counted aspects (characterizing aspects)

nSpecialValues(::Type{T}) where {T<:AbstractMLFloat} = nNaNs(T) + nZeros(T) + nInfs(T)
nSpecialNumbers(::Type{T}) where {T<:AbstractMLFloat} = nZeros(T) + nInfs(T)
nSpecialMagnitudes(::Type{T}) where {T<:AbstractMLFloat} = nPosZeros(T) + nPosInfs(T)

nOrdinaryValues(::Type{T}) where {T<:AbstractMLFloat} = nValues(T) - nSpecialValues(T)
nOrdinaryNumbers(::Type{T}) where {T<:AbstractMLFloat} = nOrdinaryValues(T)
nOrdinaryMagnitudes(::Type{T}) where {T<:AbstractMLFloat} = nMagnitudes(T) - nSpecialMagnitudes(T)

for F in (:nSpecialValues, :nSpecialNumbers, :nSpecialMagnitudes,
          :nOrdinaryValues, :nOrdinaryNumbers, :nOrdinaryMagnitudes)
    @eval $F(x::AbstractMLFloat) = $F(typeof(x))
end

# value counted aspects (derived aspects)

nNonNumericValues(::Type{T}) where {T<:AbstractMLFloat} = One # the unique NaN
nNumericValues(::Type{T}) where {T<:AbstractMLFloat} = nValues(T) - nNonNumericValues(T)
nNonZeroNumericValues(::Type{T}) where {T<:AbstractMLFloat} = nNumericValues(T) - nZeroValues(T)

# finite values are numeric values by definition
nFiniteValues(::Type{T}) where {T<:AbstractMLFloat} = nNumericValues(T) - nInfValues(T)
nNonZeroFiniteValues(::Type{T}) where {T<:AbstractMLFloat} =  nFiniteValues(T) - nZeroValues(T)

# We have one zero, it is considered neither positive nor negative in these definitions.
# When a sign must be assigned to have a well-formed expression, positive is used.

nNonPositiveValues(::Type{T}) where {T<:AbstractMLFloat} = nNegativeValues(T) + nZeros(T)
nNonPositiveFiniteValues(::Type{T}) where {T<:AbstractMLFloat} = nNonPositiveValues(T) - nNegInfs(T)

for (F) in (:nNonPositiveValues, :nNonPositiveFiniteValues)
    @eval $F(x::AbstractMLFloat) = $F(typeof(x))
end

# Zero, PosInf, NegInf are neither subnormal nor normal values
# nSubnormalMagnitudes(AbstractMLFloat{Bits, 1}) == 0

nSubnormalMagnitudes(::Type{T}) where {T<:AbstractMLFloat} = nFracValues(T) - 1
nSubnormalValues(::Type{T}) where {T<:AbstractMLFloat} = nSubnormalMagnitudes(T) << is_signed(T)

nNormalMagnitudes(::Type{T}) where {T<:AbstractMLFloat} = nFiniteMagnitudes(T) - nSubnormalMagnitudes(T)
nNormalValues(::Type{T}) where {T<:AbstractMLFloat} = nNormaMagnitudes(T) << is_signed(T)

for (F) in (:nSubnormalValues, :nSubnormalMagnitudes, :nNormalValues, :nNormalMagnitudes)
    @eval $F(x::AbstractMLFloat) = $F(typeof(x))
end

# alternative interpretation


nFracValues(bits, sigbits) = 2^(sigbits - 1)
nFracCycles(bits, sigbits, isUnsigned) = 2^(bits - sigbits + isUnsigned)
nExpBits(bits, sigbits, isSigned) = bits - sigbits + isSigned
nExpCycles(bits, sigbits) = 2^(bits - sigbits)

nFracCycles(::Type{T}) where {T<:AbstractMLFloat} = nExpMagnitudes(T)
nExpCycles(::Type{T}) where {T<:AbstractMLFloat} = nFracMagnitudes(T)

for F in (:nFracCycles, :nExpCycles)
    @eval $F(x::AbstractMLFloat) = $F(typeof(x))
end
