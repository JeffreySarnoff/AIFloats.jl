using Test
using AIFloats, Quadmath, Static

using AIFloats:
    AIFloat, AbstractAIFloat, AbstractSigned, AbstractUnsigned,
    AkoSignedExtended, AkoSignedFinite, AkoUnsignedExtended, AkoUnsignedFinite, BitsLargeMax,
    BitsLargeMin, BitsSmallMax, BitsSmallMin, BitsTop, CODE, CODE_TYPES, ConstructAIFloat, FLOAT,
    FLOAT_TYPES, SignedExtended, SignedFinite, UnsignedExtended, UnsignedFinite, code_nan,
    code_neginf, code_negone, code_one, code_posinf, code_to_index, code_to_value, code_zero, codes,
    encoding_seq, exp_bias, exp_field_max, exp_field_min, exp_normal_value_seq,
    exp_subnormal_value, exp_unbiased_mag_strides, exp_unbiased_max, exp_unbiased_min,
    exp_unbiased_normal_max, exp_unbiased_normal_min, exp_unbiased_normal_seq, exp_unbiased_seq,
    exp_unbiased_subnormal, exp_value_max, exp_value_min, exp_value_seq, firstNonzeroPrenormalMagnitude,
    floats, foundation_exps, foundation_extremal_exps, foundation_values, has_subnormals,
    index_nan, index_neginf, index_negone, index_one, index_posinf, index_to_code,
    index_to_value, index_zero, is_aifloat, is_extended, is_finite, is_signed, is_unsigned, iscode_inf,
    iscode_nan, iscode_neginf, iscode_negone, iscode_one, iscode_posinf, iscode_zero, isindex_inf,
    isindex_nan, isindex_neginf, isindex_negone, isindex_one, isindex_posinf, isindex_zero,
    lastPrenormalMagnitude, mag_foundation_seq, mag_normal_max, mag_normal_min,
    mag_subnormal_max, mag_subnormal_min, nInfs, nNaNs, nNegInfs, nPosInfs, nZeros,
    nbits, nbits_exp, nbits_frac, nbits_sig, nbits_sign, nmags, nmags_finite,
    nmags_finite_nonzero, nmags_frac, nmags_frac_nonzero, nmags_nonzero,
    nmags_normal, nmags_normal_extended, nmags_prenormal, nmags_sig,
    nmags_sig_nonzero, nmags_subnormal, normal_exp_stride, normal_mag_steps, nvalues,
    nvalues_exp, nvalues_exp_nonzero, nvalues_finite, nvalues_finite_negative,
    nvalues_finite_nonneg, nvalues_finite_nonzero, nvalues_finite_positive, nvalues_negative,
    nvalues_nonneg, nvalues_normal, nvalues_normal_extended, nvalues_numeric,
    nvalues_numeric_nonzero, nvalues_positive, nvalues_prenormal, nvalues_subnormal, pow2_foundation_exps,
    prenormal_mag_steps, significand_mags, two, two_pow, typeforcode, typeforfloat,
    unsafe_code_to_index, unsafe_code_to_value, unsafe_index_to_code, unsafe_index_to_value,
    unsafe_value_to_code, unsafe_value_to_index, validate_code, validate_index, value_seq, value_to_code,
    value_to_index, value_to_indexgte, value_to_indices

include("essential_tests.jl")

