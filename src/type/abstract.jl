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
