#=

export  AbstractAIFloat, AbsSignedFloat, AbsUnsignedFloat,
        AbsSignedFiniteFloat, AbsSignedExtendedFloat,
        AbsUnsignedFiniteFloat, AbsUnsignedExtendedFloat,
        nBits, nSigBits, nFracBits, nValues, nNumericValues, nNonzeroNumericValues,
        nSigMagnitudes, nNonzeroSigMagnitudes, nFracMagnitudes, nNonzeroFracMagnitudes,
        nExpBits, nExpValues, nNonzeroExpValues, nMagnitudes, nNonzeroMagnitudes,
        nFiniteValues, nNonzeroFiniteValues, nFiniteMagnitudes, nNonzeroFiniteMagnitudes,
        nNonnegValues, nPositiveValues, nNegativeValues,
        nFiniteNonnegValues, nFinitePositiveValues, nFiniteNegativeValues,
        nPrenormalMagnitudes, nSubnormalMagnitudes, nPrenormalValues, nSubnormalValues,
        nNormalMagnitudes, nNormalValues, nExtendedNormalMagnitudes, nExtendedNormalValues,
        expUnbiasedMax, expUnbiasedMin, expUnbiasedValues, expBias,
        is_extended, is_finite, is_signed, is_unsigned,
        nNaNs, nZeros, nInfs, nPosInfs, nNegInfs,
        normal_magnitude_steps, prenormal_magnitude_steps,
        normal_exp_stride, foundation_extremal_exps, foundation_exps,
        exp_unbiased_magnitude_strides, pow2_foundation_exps,
        prenormal_magnitude_steps, normal_magnitude_steps, normal_exp_stride,
        foundation_extremal_exps, foundation_exps, exp_unbiased_magnitude_strides, pow2_foundation_exps,
        foundation_magnitudes, foundation_values, value_sequence)

=#

abstract type AbstractAIFloat{Bits, SigBits, IsSigned} <: AbstractFloat end

abstract type AbsSignedFloat{Bits, SigBits} <: AbstractAIFloat{Bits, SigBits, true} end
abstract type AbsUnsignedFloat{Bits, SigBits} <: AbstractAIFloat{Bits, SigBits, false} end

abstract type AbsSignedFiniteFloat{Bits, SigBits} <: AbsSignedFloat{Bits, SigBits} end
abstract type AbsSignedExtendedFloat{Bits, SigBits} <: AbsSignedFloat{Bits, SigBits} end

abstract type AbsUnsignedFiniteFloat{Bits, SigBits} <: AbsUnsignedFloat{Bits, SigBits} end
abstract type AbsUnsignedExtendedFloat{Bits, SigBits} <: AbsUnsignedFloat{Bits, SigBits} end

# predicates for abstract types

is_aifloat(@nospecialize(T::Type{<:AbstractFloat})) = false
is_aifloat(@nospecialize(T::Type{<:AbstractAIFloat})) = true

is_signed(@nospecialize(T::Type{<:AbsSignedFloat}))     = true
is_signed(@nospecialize(T::Type{<:AbsUnsignedFloat}))   = false

is_unsigned(@nospecialize(T::Type{<:AbsSignedFloat}))   = false
is_unsigned(@nospecialize(T::Type{<:AbsUnsignedFloat})) = true

is_finite(@nospecialize(T::Type{<:AbsSignedFiniteFloat}))     = true
is_finite(@nospecialize(T::Type{<:AbsUnsignedFiniteFloat}))   = true
is_finite(@nospecialize(T::Type{<:AbsSignedExtendedFloat}))   = false
is_finite(@nospecialize(T::Type{<:AbsUnsignedExtendedFloat})) = false

is_extended(@nospecialize(T::Type{<:AbsSignedFiniteFloat}))     = false
is_extended(@nospecialize(T::Type{<:AbsUnsignedFiniteFloat}))   = false
is_extended(@nospecialize(T::Type{<:AbsSignedExtendedFloat}))   = true
is_extended(@nospecialize(T::Type{<:AbsUnsignedExtendedFloat})) = true

# cover instantiations
is_aifloat(@nospecialize(x::T)) where {T<:AbstractFloat} = false
is_aifloat(@nospecialize(x::T)) where {T<:AbstractAIFloat} = true

for F in (:is_extended, :is_finite, :is_signed, :is_unsigned) 
    @eval $F(x::T) where {T<:AbstractAIFloat} = $F(T)
end

