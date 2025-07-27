firstNonzeroPrenormalMagnitude(T::Type{<:AbstractAIFloat}) = 1 / n_prenormal_mags(T)
lastPrenormalMagnitude(T::Type{<:AbstractAIFloat}) = (n_prenormal_mags(T) - 1) / n_prenormal_mags(T)

mag_subnormal_min(T::Type{<:AbstractAIFloat}) = has_subnormals(T) ? firstNonzeroPrenormalMagnitude(T) * exp_subnormal_value(T) : nothing
mag_subnormal_max(T::Type{<:AbstractAIFloat}) = has_subnormals(T) ? lastPrenormalMagnitude(T) * exp_subnormal_value(T) : nothing

mag_normal_min(T::Type{<:AbstractUnsigned}) = exp_value_min(T)
mag_normal_min(T::Type{<:AbstractSigned}) = exp_value_min(T)

mag_normal_max(T::Type{<:AbstractUnsigned}) = exp_value_max(T) * (1 + ((n_prenormal_mags(T) - 1) - 1 - is_extended(T)) / n_prenormal_mags(T))
mag_normal_max(T::Type{<:AbstractSigned}) = exp_value_max(T) * (1 + ((n_prenormal_mags(T) - 1) - is_extended(T)) / n_prenormal_mags(T))

# cover instantiations
for F in (:mag_subnormal_min, :mag_subnormal_max, :mag_normal_min, :mag_normal_max)
    @eval $F(x::T) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = $F(T)
end
