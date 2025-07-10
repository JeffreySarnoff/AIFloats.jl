firstNonzeroPrenormalMagnitude(T::Type{<:AbstractAIFloat}) = 1 / nmagnitudes_prenormal(T)
lastPrenormalMagnitude(T::Type{<:AbstractAIFloat}) = (nmagnitudes_prenormal(T) - 1) / nmagnitudes_prenormal(T)

magnitude_subnormal_min(T::Type{<:AbstractAIFloat}) = has_subnormals(T) ? firstNonzeroPrenormalMagnitude(T) * exp_subnormal_value(T) : nothing
magnitude_subnormal_max(T::Type{<:AbstractAIFloat}) = has_subnormals(T) ? lastPrenormalMagnitude(T) * exp_subnormal_value(T) : nothing

magnitude_normal_min(T::Type{<:AbstractUnsigned}) = exp_value_min(T)
magnitude_normal_min(T::Type{<:AbstractSigned}) = exp_value_min(T)

magnitude_normal_max(T::Type{<:AbstractUnsigned}) = exp_value_max(T) * (1 + ((nmagnitudes_prenormal(T) - 1) - 1 - is_extended(T)) / nmagnitudes_prenormal(T))
magnitude_normal_max(T::Type{<:AbstractSigned}) = exp_value_max(T) * (1 + ((nmagnitudes_prenormal(T) - 1) - is_extended(T)) / nmagnitudes_prenormal(T))

# cover instantiations
for F in (:magnitude_subnormal_min, :magnitude_subnormal_max, :magnitude_normal_min, :magnitude_normal_max)
    @eval $F(x::T) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = $F(T)
end
