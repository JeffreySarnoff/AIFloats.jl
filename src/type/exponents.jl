
expBias(::Type{T}) where {Bits, SigBits, T<:AbsSignedFloat{Bits, SigBits}}   = 2^(Bits - SigBits - 1) # 1 << (Bits - SigBits - 1) 
expBias(::Type{T}) where {Bits, SigBits, T<:AbsUnsignedFloat{Bits, SigBits}} = 2^(Bits - SigBits )    # 1 << (Bits - SigBits)

# exponent field characterizations

expFieldMax(::Type{T}) where {T<:AbstractAIFloat} = nExpValues(T) - 1

expUnbiasedNormalMax(::Type{T}) where {T<:AbstractAIFloat} = expFieldMax(T) - expBias(T)
expUnbiasedNormalMin(::Type{T}) where {T<:AbstractAIFloat} = -expUnbiasedNormalMax(T)
expUnbiasedSubnormal(::Type{T}) where {T<:AbstractAIFloat} = expUnbiasedNormalMin(T)

expUnbiasedNormalValues(::Type{T}) where {T<:AbstractAIFloat} = collect(expUnbiasedNormalMin(T):expUnbiasedNormalMax(T))
expUnbiasedValues(::Type{T}) where {T<:AbstractAIFloat} = vcat(expUnbiasedSubnormal(T), expUnbiasedNormalValues(T))

expNormalValues(::Type{T}) where {T<:AbstractAIFloat} = two(T) .^ (expUnbiasedNormalMin(T):expUnbiasedNormalMax(T))
expSubnormalValue(::Type{T}) where {T<:AbstractAIFloat} = two(T)^(expUnbiasedSubnormal(T))
expValues(::Type{T}) where {T<:AbstractAIFloat} = [expSubnormalValue(T), expNormalValues(T)...]

expMin(::Type{T}) where {T<:AbstractAIFloat} = expUnbiasedNormalMin(T)
expMax(::Type{T}) where {T<:AbstractAIFloat} = expUnbiasedNormalMax(T)

expMinValue(::Type{T}) where {T<:AbstractAIFloat} = two(T)^expMin(T)
expMaxValue(::Type{T}) where {T<:AbstractAIFloat} = two(T)^expMax(T)

# cover instantiations

expBias(x::T) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = expBias(T)

for F in (:expFieldMax, :expMin, :expMax, :expMinValue, :expMaxValue, :expValues,
          :expUnbiasedNormalMax, :expUnbiasedNormalMin, :expUnbiasedSubnormal, 
          :expUnbiasedNormalValues, :expUnbiasedValues, :expSubnormalValue)
    @eval $F(x::T) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = $F(T)
end

