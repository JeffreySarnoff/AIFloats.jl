exponent_bias(::Type{T}) where {T<:AbstractMLFloat}       = 2^(nExpBits(T) - 1) - 1
biased_exponent_max(::Type{T}) where {T<:AbstractMLFloat} =  exponent_bias(T)
biased_exponent_min(::Type{T}) where {T<:AbstractMLFloat} = -biased_exponent_max(T)

exponent_max(::Type{T}) where {T<:AbstractMLFloat} = 2.0^(biased_exponent_max(T))
exponent_min(::Type{T}) where {T<:AbstractMLFloat} = 2.0^(biased_exponent_min(T))

subnormal_min(::Type{T}) where {T<:AbstractMLFloat} =
    exponent_min(T) * ( 1//nFracValues(T) )
subnormal_max(::Type{T}) where {T<:AbstractMLFloat} =
    exponent_min(T) * ( (nFracValues(T) - 1)//nFracValues(T) )

normal_min(::Type{T}) where {T<:AbstractMLFloat} = exponent_min(T) * (1//1)
normal_max(::Type{T}) where {T<:AbstractMLFloat} = exponent_max(T) * ((nFracValues(T) - 1)//nFracValues(T))

for F in (:exponent_max, :exponent_min, :subnormal_max, :subnormal_min, :normal_max, :normal_min)
    @eval $F(x::T) where {T<:AbstractMLFloat} = $F(T)
end
