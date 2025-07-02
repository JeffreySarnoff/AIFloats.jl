firstNonzeroPrenormalMagnitude(T::Type{<:AbstractAIFloat}) = 1 / nPrenormalMagnitudes(T)
lastPrenormalMagnitude(T::Type{<:AbstractAIFloat}) = (nPrenormalMagnitudes(T) - 1) / nPrenormalMagnitudes(T)

subnormalMagnitudeMin(T::Type{<:AbstractAIFloat}) = has_subnormals(T) ? firstNonzeroPrenormalMagnitude(T) * expSubnormalValue(T) : nothing
subnormalMagnitudeMax(T::Type{<:AbstractAIFloat}) = has_subnormals(T) ? lastPrenormalMagnitude(T) * expSubnormalValue(T) : nothing

normalMagnitudeMin(T::Type{<:AbsUnsignedFloat}) = expMinValue(T)
normalMagnitudeMin(T::Type{<:AbsSignedFloat}) = expMinValue(T)

normalMagnitudeMax(T::Type{<:AbsUnsignedFloat}) = expMaxValue(T) * (1 + ((nPrenormalMagnitudes(T) - 1) - 1 - is_extended(T)) / nPrenormalMagnitudes(T))
normalMagnitudeMax(T::Type{<:AbsSignedFloat}) = expMaxValue(T) * (1 + ((nPrenormalMagnitudes(T) - 1) - is_extended(T)) / nPrenormalMagnitudes(T))

# cover instantiations
for F in (:subnormalMagnitudeMin, :subnormalMagnitudeMax, :normalMagnitudeMin, :normalMagnitudeMax)
    @eval $F(x::T) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = $F(T)
end
