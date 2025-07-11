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
    encoding_sequence, expBias,
    expFieldMax, expMax, expMaxValue, expMin, expMinValue, expNormalValues,
    expSubnormal, expSubnormalValue, expUnbiasedNormalMax, expUnbiasedNormalMin,
    expUnbiasedNormalValues, expUnbiasedNormals, expUnbiasedSubnormal, expUnbiasedValues,
    expValues, exp_unbiased_magnitude_strides, firstNonzeroPrenormalMagnitude,
    foundation_exps, foundation_extremal_exps, foundation_magnitudes,
    foundation_values, has_subnormals, idxinf, idxnan, idxneginf, idxnegone, idxone,
    include, index1, index_to_code, index_to_offset, index_to_value,
    is_aifloat, is_extended, is_finite, is_idxnan, is_ofsnan, is_signed, is_unsigned, isfinite,
    isinf, isnan, isone, iszero, lastPrenormalMagnitude, 
    nbits, nSignBits, nbits_exp, nbits_sig,
    nExpValues, nExtendedNormalMagnitudes, nExtendedNormalValues,
    nFiniteMagnitudes, nFiniteNegativeValues, nFiniteNonnegValues, nFinitePositiveValues,
    nFiniteValues, nFracBits, nFracMagnitudes, nInfs, nmagnitudes, nNaNs, nNegInfs,
    nNegativeValues, nNonnegValues, nNonzeroExpValues, nNonzeroFiniteMagnitudes,
    nNonzeroFiniteValues, nNonzeroFracMagnitudes, nNonzeroMagnitudes, nNonzeroNumericValues,
    nNonzeroSigMagnitudes, nNormalMagnitudes, nNormalValues, nNumericValues, nPosInfs,
    nPositiveValues, nPrenormalMagnitudes, nPrenormalValues, nSigMagnitudes,
    nSubnormalMagnitudes, nSubnormalValues, nvalues, nZeros,
    normalMagnitudeMax, normalMagnitudeMin, normal_exp_stride, normal_magnitude_steps,
    offset_to_index, offset_to_value, ofsinf, ofsnan, ofsneginf, ofsone,
    pow2_foundation_exps, prenormal_magnitude_steps, 
    round_down, round_fromzero, round_tozero, round_up, 
    round_nearestaway, round_nearesteven, round_nearestfromzero, round_nearestodd,
    round_nearesttozero,
    significand_magnitudes,
    subnormalMagnitudeMax, subnormalMagnitudeMin, 
    value_sequence, value_to_index, value_to_indexgte, value_to_indices,
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

