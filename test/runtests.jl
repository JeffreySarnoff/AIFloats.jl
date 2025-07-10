using Test
using AIFloats, AlignedAllocs, Quadmath, Static

using AIFloats: AbstractAIFloat, AbstractUnsigned, AbstractUnsigned,
    AkoUnsignedExtended, AkoUnsignedFinite, 
    AkoSignedExtended, AkoSignedFinite, 
    AIFloat, ConstructAIFloat, floats, codes,
    UnsignedExtended, UnsignedFinite, 
    SignedExtended, SignedFinite,
    typeforcode, typeforfloat,
    CODE, CODE_TYPES, FLOAT, FLOAT_TYPES,
    two, two_pow, 
    BitsLargeMax, BitsLargeMin, BitsSmallMax, BitsSmallMin, BitsTop, 
    RoundStochastic, RoundToOdd, 
    encoding_seq, exp_bias,
    exp_field_max, expMax, exp_value_max, expMin, exp_value_min, exp_normal_value_seq,
    expSubnormal, exp_subnormal_value, exp_unbiased_normal_max, exp_unbiased_normal_min,
    exp_unbiased_normal_seq, exp_unbiased_normal_seq, exp_unbiased_subnormal, expUnbiased,
    exp_value_seq, exp_unbiased_magnitude_strides, firstNonzeroPrenormalMagnitude,
    foundation_exps, foundation_extremal_exps, magnitude_foundation_seq,
    foundation_values, has_subnormals, idx_inf, idx_nan, idx_neginf, idx_negone, idx_one,
    include, index_one, index_to_code, index_to_offset, index_to_value,
    is_aifloat, is_extended, is_finite, is_idxnan, is_ofsnan, is_signed, is_unsigned, isfinite,
    isinf, isnan, isone, iszero, lastPrenormalMagnitude, 
    nbits, nbits_sign, nbits_exp, nbits_sig,
    nvalues_exp, nmagnitudes_normal_extended, nvalues_normal_extended,
    nmagnitudes_finite, nvalues_finite_negative, nvalues_finite_nonneg, nvalues_finite_positive,
    nvalues_finite, nbits_frac, nmagnitudes_frac, nInfs, nmagnitudes, nNaNs, nNegInfs,
    nvalues_negative, nvalues_nonneg, nvalues_exp_nonzero, nmagnitudes_finite_nonzero,
    nvalues_finite_nonzero, nmagnitudes_frac_nonzero, nmagnitudes_nonzero, nvalues_numeric_nonzero,
    nmagnitudes_sig_nonzero, nmagnitudes_normal, nvalues_normal, nvalues_numeric, nPosInfs,
    nvalues_positive, nmagnitudes_prenormal, nvalues_prenormal, nmagnitudes_sig,
    nmagnitudes_subnormal, nvalues_subnormal, nvalues, nZeros,
    magnitude_normal_max, magnitude_normal_min, normal_exp_stride, normal_magnitude_steps,
    offset_to_index, offset_to_value, ofs_inf, ofs_nan, ofs_neginf, ofs_one,
    pow2_foundation_exps, prenormal_magnitude_steps, 
    round_down, round_fromzero, round_tozero, round_up, 
    round_nearestaway, round_nearesteven, round_nearestfromzero, round_nearestodd,
    round_nearesttozero,
    significand_magnitudes,
    magnitude_subnormal_max, magnitude_subnormal_min, 
    value_seq, value_to_index, value_to_indexgte, value_to_indices,
    value_to_offset, x_or_T

# Test organization following Julia best practices
@testset "AIFloats.jl Tests" begin
    # Code quality tests
    @testset "Code Quality" begin
#        Aqua.test_all(AIFloats)
    end
    # Create some test types for predicate testing
    struct TestSignedFinite{Bits, SigBits} <: AkoSignedFinite{Bits, SigBits} end
    struct TestSignedExtended{Bits, SigBits} <: AkoSignedExtended{Bits, SigBits} end
    struct TestUnsignedFinite{Bits, SigBits} <: AkoUnsignedFinite{Bits, SigBits} end
    struct TestUnsignedExtended{Bits, SigBits} <: AkoUnsignedExtended{Bits, SigBits} end

    # Include all test files
    include("test_constants.jl")        # ok
    include("test_abstract.jl")         # ok
    include("test_predicates.jl")       # ok
    include("test_counts.jl")           # ok
    include("test_exponents.jl")        # ok
    include("test_significands.jl")     # ok
    include("test_encodings.jl")        # ok
    include("test_extrema.jl")          # ok
    include("test_foundation.jl")       # ok
    include("test_unsigned.jl")         # ok
    include("test_signed.jl")           # ok
    include("test_indices.jl")          # ok
    include("test_rounding.jl")         # ok
    include("test_aifloats_main.jl")    # ok
end

