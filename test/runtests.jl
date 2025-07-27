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
    exp_unbiased_subnormal, exp_value_max, exp_value_min, exp_value_seq, first_nonzero_prenormal,
    floats, foundation_exps, foundation_extremal_exps, foundation_vals, has_subnormals,
    index_nan, index_neginf, index_negone, index_one, index_posinf, index_to_code,
    index_to_value, index_zero, is_aifloat, is_extended, is_finite, is_signed, is_unsigned, iscode_inf,
    iscode_nan, iscode_neginf, iscode_negone, iscode_one, iscode_posinf, iscode_zero, isindex_inf,
    isindex_nan, isindex_neginf, isindex_negone, isindex_one, isindex_posinf, isindex_zero,
    last_prenormal, mag_foundation_seq, normal_mag_max, normal_mag_min,
    subnormal_mag_max, subnormal_mag_min, n_infs, n_nans, n_neg_infs, n_pos_infs, n_zeros,
    n_bits, n_exp_bits, n_frac_bits, n_sig_bits, n_sign_bits, n_mags, n_finite_mags,
    n_finite_nonzero_mags, n_frac_mags, n_frac_mags_nonzero, n_nonzero_mags,
    n_normal_mags, n_extended_normal_mags, n_prenormal_mags, n_sig_mags,
    n_sig_mags_nonzero, n_subnormal_mags, normal_exp_stride, normal_mag_steps, n_vals,
    n_exp_nums, n_nonzero_exp_nums, n_finite_nums, n_neg_finite_vals,
    n_poz_finite_vals, n_finite_nonzero_nums, n_pos_finite_vals, n_neg_vals,
    n_poz_vals, n_normal_vals, n_extended_normal_vals, n_nums,
    n_nonzero_nums, n_pos_vals, n_prenormal_vals, n_subnormal_vals, pow2_foundation_exps,
    prenormal_mag_steps, significand_mags, two, two_pow, typeforcode, typeforfloat,
    unsafe_code_to_index, unsafe_code_to_value, unsafe_index_to_code, unsafe_index_to_value,
    unsafe_value_to_code, unsafe_value_to_index, validate_code, validate_index, value_seq, value_to_code,
    value_to_index, value_to_indexgte, value_to_indices

include("essential_tests.jl")

