
exp_bias(::Type{T}) where {Bits, SigBits, T<:AbstractSigned{Bits, SigBits}}   = two(T)^(Bits - SigBits - 1) # 1 << (Bits - SigBits - 1) 
exp_bias(::Type{T}) where {Bits, SigBits, T<:AbstractUnsigned{Bits, SigBits}} = two(T)^(Bits - SigBits )    # 1 << (Bits - SigBits)

# exponent field characterizations
exp_field_min(T::Type{<:AbstractAIFloat}) = 0
exp_field_max(T::Type{<:AbstractAIFloat}) = nvalues_exp(T) - 1

exp_unbiased_normal_max(T::Type{<:AbstractAIFloat}) = exp_field_max(T) - exp_bias(T)
exp_unbiased_normal_min(T::Type{<:AbstractAIFloat}) = -exp_unbiased_normal_max(T)
exp_unbiased_subnormal(T::Type{<:AbstractAIFloat}) = exp_unbiased_normal_min(T)

exp_subnormal_value(T::Type{<:AbstractAIFloat}) = BigFloat(2)^(exp_unbiased_subnormal(T))

exp_unbiased_normal_seq(T::Type{<:AbstractAIFloat}) = collect(exp_unbiased_normal_min(T):exp_unbiased_normal_max(T))
exp_unbiased_seq(T::Type{<:AbstractAIFloat}) = [exp_unbiased_subnormal(T), exp_unbiased_normal_seq(T)...]

# exp_normal_value_seq(T::Type{<:AbstractAIFloat}) = two(T) .^ (exp_unbiased_normal_min(T):exp_unbiased_normal_max(T))
# exp_value_seq(T::Type{<:AbstractAIFloat}) = [exp_subnormal_value(T), exp_normal_value_seq(T)...]

exp_normal_value_seq(T::Type{<:AbstractAIFloat}) = two(T) .^ (exp_unbiased_normal_min(T):exp_unbiased_normal_max(T))
exp_value_seq(T::Type{<:AbstractAIFloat}) = [exp_subnormal_value(T), exp_normal_value_seq(T)...]

exp_unbiased_min(T::Type{<:AbstractAIFloat}) = exp_unbiased_normal_min(T)
exp_unbiased_max(T::Type{<:AbstractAIFloat}) = exp_unbiased_normal_max(T)

exp_value_min(T::Type{<:AbstractAIFloat}) = two(T)^exp_unbiased_min(T)
exp_value_max(T::Type{<:AbstractAIFloat}) = two(T)^exp_unbiased_max(T)

# cover instantiations

exp_bias(x::T) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = exp_bias(T)

for F in (:exp_field_min, :exp_field_max, :exp_unbiased_min, :exp_unbiased_max, :exp_unbiased_seq,
          :exp_value_min, :exp_value_max, :exp_value_seq, :exp_normal_value_seq,
          :exp_unbiased_normal_max, :exp_unbiased_normal_min, :exp_unbiased_subnormal,
          :exp_unbiased_normal_seq, :exp_subnormal_value)
    @eval $F(x::T) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = $F(T)
end

