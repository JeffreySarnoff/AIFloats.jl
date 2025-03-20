biased_exponent_max(::Type{T}) where {T<:AbstractAIFloat} = 2^(nExpBits(T)) - 1
biased_exponent_min(::Type{T}) where {T<:AbstractAIFloat} = 1 - 2^(nExpBits(T) - 1)
Base.exponent_bias(::Type{T}) where {T<:AbstractAIFloat} = 2^(nExpBits(T) - 1) - 1

exponent_max(::Type{T}) where {T<:AbstractAIFloat} = 2.0^(biased_exponent_max(T))
exponent_min(::Type{T}) where {T<:AbstractAIFloat} = 2.0^(biased_exponent_min(T))

subnormal_max(::Type{T}) where {T<:AbstractAIFloat} = exponent_min(T) * (1//nFracValues(x))
subnormal_min(::Type{T}) where {T<:AbstractAIFloat} = exponent_min(T) * ((nFracValues(T) - 1)//nFracValues(T))

normal_max(::Type{T}) where {T<:AbstractAIFloat} = exponent_max(T) * ((nFracValues(T) - 1)//nFracValues(T))
normal_min(::Type{T}) where {T<:AbstractAIFloat} = exponent_min(T) * (1//1)

for F in (:exponent_max, :exponent_min, :subnormal_max, :subnormal_min, :normal_max, :normal_min)
    @eval $F(x::T) where {T<:AbstractAIFloat} = $F(T)
end
