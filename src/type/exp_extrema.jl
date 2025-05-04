Base.exponent_bias(::Type{<:AbsSignedFloatML{Bits, SigBits}}) where {Bits, SigBits} =
   floor(2^(nExpBits(T) - 1) - 1)
Base.exponent_bias(::Type{<:AbsUnsignedFloatML{Bits, SigBits}}) where {Bits, SigBits} =
   floor(2^(nExpBits(T)))

biased_exponent_max(::Type{T}) where {T<:AbstractAIFloat} =  exponent_bias(T)
biased_exponent_min(::Type{T}) where {T<:AbstractAIFloat} = -biased_exponent_max(T) + isone(nSigBits(T))

exponent_max(::Type{T}) where {T<:AbstractAIFloat} = 2.0^(biased_exponent_max(T))
exponent_min(::Type{T}) where {T<:AbstractAIFloat} = 2.0^(biased_exponent_min(T))

subnormal_min(::Type{T}) where {T<:AbstractAIFloat} =
    exponent_min(T) * ( 1// nFracMagnitudes(T) )
subnormal_max(::Type{T}) where {T<:AbstractAIFloat} =
    exponent_min(T) * ( ( nFracMagnitudes(T) - 1)// nFracMagnitudes(T) )

normal_min(::Type{T}) where {T<:AbstractAIFloat} = exponent_min(T) * (1//1)
normal_max(::Type{T}) where {T<:AbstractAIFloat} = exponent_max(T) * (( nFracMagnitudes(T) - 1)// nFracMagnitudes(T))

for F in (:exponent_max, :exponent_min, :subnormal_max, :subnormal_min, :normal_max, :normal_min)
    @eval $F(x::T) where {T<:AbstractAIFloat} = $F(T)
end
