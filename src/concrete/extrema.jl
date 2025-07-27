first_nonzero_prenormal(T::Type{<:AbstractAIFloat}) = 1 / n_prenormal_mags(T)
last_prenormal(T::Type{<:AbstractAIFloat}) = (n_prenormal_mags(T) - 1) / n_prenormal_mags(T)

prenormal_mag_min(T::Type{<:AbstractAIFloat}) = 0.0
prenormal_mag_max(T::Type{<:AbstractAIFloat}) = has_subnormals(T) ? last_prenormal(T) * exp_subnormal_value(T) : nothing

subnormal_mag_min(T::Type{<:AbstractAIFloat}) = has_subnormals(T) ? first_nonzero_prenormal(T) * exp_subnormal_value(T) : nothing
subnormal_mag_max(T::Type{<:AbstractAIFloat}) = has_subnormals(T) ? last_prenormal(T) * exp_subnormal_value(T) : nothing

normal_mag_min(T::Type{<:AbstractUnsigned}) = exp_value_min(T)
normal_mag_min(T::Type{<:AbstractSigned}) = exp_value_min(T)

normal_mag_max(T::Type{<:AbstractUnsigned}) = exp_value_max(T) * (1 + ((n_prenormal_mags(T) - 1) - 1 - is_extended(T)) / n_prenormal_mags(T))
normal_mag_max(T::Type{<:AbstractSigned}) = exp_value_max(T) * (1 + ((n_prenormal_mags(T) - 1) - is_extended(T)) / n_prenormal_mags(T))

# cover instantiations
for F in (:prenormal_mag_min, :prenormal_mag_max, :subnormal_mag_min, :subnormal_mag_max, 
          :normal_mag_min, :normal_mag_max)
    @eval $F(x::T) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = $F(T)
end
