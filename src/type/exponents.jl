
# exponent field characterizations

expBiasedMin(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = 0
expBiasedMax(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = nExpValues(T) - 1
expBiasedValues(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = collect(expBiasedMin(T):expBiasedMax(T))

expUnbiasedMin(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = expBiasedMin(T) - expBias(T)
expUnbiasedMax(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = expBiasedMax(T) - expBias(T)
expUnbiasedValues(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = collect(expUnbiasedMin(T):expUnbiasedMax(T))[2:end]

expMaxValue(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = 2.0^(expUnbiasedMax(T))
expMinValue(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = 2.0^(expUnbiasedMin(T))
expValues(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = map(two_pow, expUnbiasedValues(T))

expBias(::Type{T}) where {Bits, SigBits, T<:AbsSignedFloat{Bits, SigBits}}   = 1 << (Bits - SigBits - 1) # floor(2^(Bits - SigBits - 1))
expBias(::Type{T}) where {Bits, SigBits, T<:AbsUnsignedFloat{Bits, SigBits}} = 1 << (Bits - SigBits)     # floor(2^(Bits - SigBits))

# cover instantiations

for F in (:expBias, :expMaxValue, :expMinValue, :expValues,
          :expUnbiasedMax, :expUnbiasedMin, :expUnbiasedValues)
    @eval $F(x::T) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = $F(T)
end

