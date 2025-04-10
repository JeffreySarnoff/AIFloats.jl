Base.exponent_bias(::Type{T}) where {T<:AbstractFloatML}  = 2^(nExpBits(T) - 1) - 1
biased_exponent_max(::Type{T}) where {T<:AbstractFloatML} =  exponent_bias(T)
biased_exponent_min(::Type{T}) where {T<:AbstractFloatML} = -biased_exponent_max(T)

exponent_max(::Type{T}) where {T<:AbstractFloatML} = 2.0^(biased_exponent_max(T))
exponent_min(::Type{T}) where {T<:AbstractFloatML} = 2.0^(biased_exponent_min(T))

subnormal_min(::Type{T}) where {T<:AbstractFloatML} =
    exponent_min(T) * ( 1// nFracMagnitudes(T) )
subnormal_max(::Type{T}) where {T<:AbstractFloatML} =
    exponent_min(T) * ( ( nFracMagnitudes(T) - 1)// nFracMagnitudes(T) )

normal_min(::Type{T}) where {T<:AbstractFloatML} = exponent_min(T) * (1//1)
normal_max(::Type{T}) where {T<:AbstractFloatML} = exponent_max(T) * (( nFracMagnitudes(T) - 1)// nFracMagnitudes(T))

for F in (:exponent_max, :exponent_min, :subnormal_max, :subnormal_min, :normal_max, :normal_min)
    @eval $F(x::T) where {T<:AbstractFloatML} = $F(T)
end
