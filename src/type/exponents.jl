
expBias(::Type{T}) where {Bits, SigBits, T<:AbsSignedFloat{Bits, SigBits}}   = 2^(Bits - SigBits - 1) # 1 << (Bits - SigBits - 1) 
expBias(::Type{T}) where {Bits, SigBits, T<:AbsUnsignedFloat{Bits, SigBits}} = 2^(Bits - SigBits )    # 1 << (Bits - SigBits)

# exponent field characterizations
expFieldMax(T::Type{<:AbstractAIFloat}) = nExpValues(T) - 1

expUnbiasedNormalMax(T::Type{<:AbstractAIFloat}) = expFieldMax(T) - expBias(T)
expUnbiasedNormalMin(T::Type{<:AbstractAIFloat}) = -expUnbiasedNormalMax(T)
expUnbiasedSubnormal(T::Type{<:AbstractAIFloat}) = expUnbiasedNormalMin(T)

expUnbiasedNormals(T::Type{<:AbstractAIFloat}) = collect(expUnbiasedNormalMin(T):expUnbiasedNormalMax(T))
expUnbiasedValues(T::Type{<:AbstractAIFloat}) = vcat(expUnbiasedSubnormal(T), expUnbiasedNormals(T))

expNormalValues(T::Type{<:AbstractAIFloat}) = two(T) .^ (expUnbiasedNormalMin(T):expUnbiasedNormalMax(T))
expSubnormalValue(T::Type{<:AbstractAIFloat}) = two(T)^(expUnbiasedSubnormal(T))
expValues(T::Type{<:AbstractAIFloat}) = [expSubnormalValue(T), expNormalValues(T)...]

expMin(T::Type{<:AbstractAIFloat}) = expUnbiasedNormalMin(T)
expMax(T::Type{<:AbstractAIFloat}) = expUnbiasedNormalMax(T)

expMinValue(T::Type{<:AbstractAIFloat}) = two(T)^expMin(T)
expMaxValue(T::Type{<:AbstractAIFloat}) = two(T)^expMax(T)

# cover instantiations

expBias(x::T) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = expBias(T)

for F in (:expFieldMax, :expMin, :expMax, :expMinValue, :expMaxValue, :expValues,
          :expUnbiasedNormalMax, :expUnbiasedNormalMin, :expUnbiasedSubnormal, 
          :expUnbiasedNormalValues, :expUnbiasedValues, :expSubnormalValue)
    @eval $F(x::T) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = $F(T)
end

