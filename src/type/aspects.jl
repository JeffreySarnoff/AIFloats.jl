# forms for use with FoundationalFloats

nBits(Bits, SigBits) = Bits
nSigBits(Bits, SigBits) = SigBits
nFracBits(Bits, SigBits) = SigBits - oftype(SigBits, 1)
nSignBits(Bits, SigBits, IsSigned) = zero(Int8) + IsSigned
function nExpBits(Bits, SigBits, IsSigned)
    bits = Bits - SigBits + !IsSigned
    if bits > Bits
        bits = Bits - IsSigned
    end
    bits
end
nValues(Bits, SigBits) = 2^nBits(Bits, SigBits)
nFracValues(Bits, SigBits) = 
    if SigBits <= 0
        1 / 2^abs(nFracBits(Bits, SigBits))
    else
        2^nFracBits(Bits, SigBits)
    end
nExpValues(Bits, SigBits, IsSigned) = 2^nExpBits(Bits, SigBits, IsSigned)
nFracCycles(Bits, SigBits, IsSigned) = nExpValues(Bits, SigBits, IsSigned)
nExpCycles(Bits, SigBits) = nFracValues(Bits, SigBits)

# forms for use with AbstractAIFloat

nBits(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = Bits
nSigBits(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = SigBits
nFracBits(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = SigBits - oftype(SigBits, 1)
nExpBits(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = Bits - SigBits + is_unsigned(T)
nSignBits(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = zero(Int8) + is_signed(T)

nPosZeros(::Type{T}) where {T<:AbstractAIFloat} = one(Int8)
nNegZeros(::Type{T}) where {T<:AbstractAIFloat} = zero(Int8)
nZeros(::Type{T}) where {T<:AbstractAIFloat} = one(Int8)
nNaNs(::Type{T}) where {T<:AbstractAIFloat} = one(Int8)

nPosInfs(::Type{T}) where {T<:AbstractAIFloat} = zero(Int8) + is_extended(T)
nNegInfs(::Type{T}) where {T<:AbstractAIFloat} = zero(Int8) + (is_signed(T)  & is_extended(T))
nInfs(::Type{T}) where {T<:AbstractAIFloat} = is_extended(T) * (is_signed(T) + is_extended(T))

for F in (:nBits, :nSigBits, :nFracBits, :nSignBits,
          :nZeros, :nNaNs, :nPosInfs, :nNegInfs, :nInfs)
    @eval begin
        $F(x::T) where {T<:AbstractAIFloat} = $F(T)
    end
end

# value counted aspects (characterizing aspects)

nSpecialValues(::Type{T}) where {T<:AbstractAIFloat} = nNaNs(T) + nZeros(T) + nInfs(T)
nSpecialNumbers(::Type{T}) where {T<:AbstractAIFloat} = nZeros(T) + nInfs(T)
nSpecialMagnitudes(::Type{T}) where {T<:AbstractAIFloat} = nPosZeros(T) + nPosInfs(T)

nOrdinaryValues(::Type{T}) where {T<:AbstractAIFloat} = nValues(T) - nSpecialValues(T)
nOrdinaryNumbers(::Type{T}) where {T<:AbstractAIFloat} = nOrdinaryValues(T)
nOrdinaryMagnitudes(::Type{T}) where {T<:AbstractAIFloat} = nMagnitudes(T) - nSpecialMagnitudes(T)

for F in (:nSpecialValues, :nSpecialNumbers, :nSpecialMagnitudes, :nOrdinaryValues, :nOrdinaryNumbers, :nOrdinaryMagnitudes)
    @eval $F(x::T) where {T<:AbstractAIFloat} = $F(T)
end

# nFracValues == nFracMagnitudes
for (NBits,F) in ((:nBits, :nValues), (:nSigBits, :nSigValues), (:nFracBits, :nFracValues))
    @eval begin
        $F(::Type{T}) where {T<:AbstractAIFloat} = 2^$NBits(T)
        $F(x::T) where {T<:AbstractAIFloat} = $F(T)
    end
end  

for (NBits,F) in ((:nSignBits, :nSignValues),
              (:nZeros, :nZeroValues), (:nNaNs, :nNaNValues), (:nInfs, :nInfValues),
              (:nPosInfs, :nPosInfValues), (:nNegInfs, :nNegInfValues))
    @eval begin
        $F(::Type{T}) where {T<:AbstractAIFloat} = $NBits(T)
        $F(x::T) where {T<:AbstractAIFloat} = $F(T)
    end
end

# value counted aspects (derived aspects)

nNonNumericValues(::Type{T}) where {T<:AbstractAIFloat} = One # the unique NaN
nNumericValues(::Type{T}) where {T<:AbstractAIFloat} = nValues(T) - nNonNumericValues(T)
nNonZeroNumericValues(::Type{T}) where {T<:AbstractAIFloat} = nNumericValues(T) - nZeroValues(T)

# finite values are numeric values by definition
nFiniteValues(::Type{T}) where {T<:AbstractAIFloat} = nNumericValues(T) - nInfValues(T)
nNonZeroFiniteValues(::Type{T}) where {T<:AbstractAIFloat} =  nFiniteValues(T) - nZeroValues(T)

# We have one zero, it is considered neither positive nor negative in these definitions.
# When a sign must be assigned to have a well-formed expression, positive is used.

nIsUnsignedativeValues(::Type{T}) where {T<:AbstractAIFloat} = nNumericValues(T) >> is_signed(T)
nIsUnsignedativeFiniteValues(::Type{T}) where {T<:AbstractAIFloat} = nIsUnsignedativeValues(T) - nPosInfs(T)
nPositiveValues(::Type{T}) where {T<:AbstractAIFloat} = nIsUnsignedativeValues(T) - nZeroValues(T)
nPositiveFiniteValues(::Type{T}) where {T<:AbstractAIFloat} = nPositiveValues(T) - nPosInfs(T)

nNegativeValues(::Type{T}) where {T<:AbstractAIFloat} = is_signed(T) * nPositiveValues(T)
nNegativeFiniteValues(::Type{T}) where {T<:AbstractAIFloat} = nPositiveFiniteValues(T)
nNonPositiveValues(::Type{T}) where {T<:AbstractAIFloat} = nNegativeValues(T) + nZeros(T)
nNonPositiveFiniteValues(::Type{T}) where {T<:AbstractAIFloat} = nNonPositiveValues(T) - nNegInfs(T)

for (F) in (:nNumericValues, :nNonNumericValues, :nNonNumericZeroValues,
            :nFiniteValues, :nNonZeroFiniteValues,
            :nIsUnsignedativeValues, :nIsUnsignedativeFiniteValues,
            :nPositiveValues, :nPositiveFiniteValues,
            :nNonPositiveValues, :nNonPositiveFiniteValues,
            :nNegativeValues, :nNegativeFiniteValues)
    @eval $F(x::T) where {T<:AbstractAIFloat} = $F(T)
end

# value counted aspects (derived magnitudes)
# magnitudes count unique absolute [numeric] values

nMagnitudes(::Type{T}) where {T<:AbstractAIFloat} = nIsUnsignedativeValues(T)
nFiniteMagnitudes(::Type{T}) where {T<:AbstractAIFloat} = nIsUnsignedativeFiniteValues(T)
nNonZeroMagnitudes(::Type{T}) where {T<:AbstractAIFloat} = nPositiveValues(T)
nNonZeroFiniteMagnitudes(::Type{T}) where {T<:AbstractAIFloat} = nPositiveFiniteValues(T)

for (F) in (:nMagnitudes, :nFiniteMagnitudes,
            :nNonZeroMagnitudes, :nNonZeroFiniteMagnitudes)
    @eval $F(x::T) where {T<:AbstractAIFloat} = $F(T)
end

# value counted aspects (subnormal and normal values)

# Zero, PosInf, NegInf are neither subnormal nor normal values
# nSubnormalMagnitudes(AbstractAIFloat{Bits, 1}) == 0

nSubnormalMagnitudes(::Type{T}) where {T<:AbstractAIFloat} = nFracValues(T) - One
nSubnormalValues(::Type{T}) where {T<:AbstractAIFloat} = nSubnormalMagnitudes(T) << is_signed(T)

nNormalMagnitudes(::Type{T}) where {T<:AbstractAIFloat} = nFiniteMagnitudes(T) - nSubnormalMagnitudes(T)
nNormalValues(::Type{T}) where {T<:AbstractAIFloat} = nNormaMagnitudes(T) << is_signed(T)

for (F) in (:nSubnormalValues, :nSubnormalMagnitudes,
            :nNormalValues, :nNormalMagnitudes)
    @eval $F(x::T) where {T<:AbstractAIFloat} = $F(T)
end

# alternative interpretations

nFracCycles(::Type{T}) where {T<:AbstractAIFloat} = nExpValues(T)
nExpCycles(::Type{T}) where {T<:AbstractAIFloat} = nFracValues(T)

for F in (:nFracCycles, :nExpCycles)
    @eval $F(x::T) where {T<:AbstractAIFloat} = $F(T)
end

