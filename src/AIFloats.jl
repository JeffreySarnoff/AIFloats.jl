module AIFloats

export AbstractAIFloat,
         AbsUnsignedFloat,
           AbsUnsignedFiniteFloat, AbsUnsignedExtendedFloat,
         AbsSignedFloat,
           AbsSignedFiniteFloat, AbsSignedExtendedFloat,
        # concrete types
        floats, codes,
        # generalized constructor
        AIFloat, 
        UnsignedFiniteFloats, UnsignedExtendedFloats,
        SignedFiniteFloats, SignedExtendedFloats,
        # typed predicates
        is_aifloat, is_unsigned, is_signed, is_finite, is_extended,
        # functions over types
        encoding_sequence, value_sequence,
        magnitude_sequence, foundation_magnitudes,
        # counts predicated on abstract [sub]type
        nBits, nSigBits, nFracBits, nSignBits, nExpBits,
        nNaNs, nZeros, nInfs, nPosInfs, nNegInfs,
        nPrenormalMagnitudes, nSubnormalMagnitudes, nNormalMagnitudes, nMagnitudes,
        nValues, nNumericValues, nNonzeroNumericValues,
        nMagnitudes, nNonzeroMagnitudes,
        nExpValues, nNonzeroExpValues,
        nFiniteValues, nNonzeroFiniteValues,
        # julia support
        index1, indexneg1, floatleast
        # counts predicated on type defining parameters and type specifying qualities
        # parameters: (bits, sigbits, exponent bias)
        # qualities: (signedness [signed / unsigned], finiteness [finite / extended (has Inf[s])])

using AlignedAllocs: memalign_clear, alignment
using Static: static, StaticInt, StaticBool, False, True

include("type/constants.jl")
include("type/abstract.jl")

include("support/indices.jl")

include("concrete/encodings.jl")
include("concrete/foundation.jl")
include("concrete/unsigned.jl")
include("concrete/signed.jl")

include("support/julialang.jl")


function AIFloat(bits::Int, sigbits::Int; signed::Bool, extended::Bool)
    if signed
        if extended
            SignedExtendedFloats(bits, sigbits)
        else # finite
            SignedFiniteFloats(bits, sigbits)
        end
    else # unsigned
        if extended
            UnsignedExtendedFloats(bits, sigbits)
        else # finite
            UnsignedFiniteFloats(bits, sigbits)
        end
    end
end

#=
export AbstractAIFloat,
C         # concrete collective types
         SignedExtendedFloat, SignedFiniteFloat,
         UnsignedExtendedFloat, UnsignedFiniteFloat,
       AIFloat, # constructor for concrete AIFloat types
       CODE, FLOAT,
       IsSigned, IsUnsigned, IsExtended, IsFinite,
       is_signed, is_unsigned, is_finite, is_extended,
       codes, floats, nonneg_codes, nonneg_floats, symbol,
       typeforcode, typeforfloat,
       bitwidth, precision,
       exponent_min, exponent_max, exponent_bias,
       subnormal_min, subnormal_max, normal_min, normal_max,
       nZeros, nNaNs, nBits, nSigBits, nFracBits, nSignBits, nExpBits,
       nValues, nNumericValues, nNonzeroNumericValues,
       nPositiveValues, nNegativeValues,
       nMagnitudes, nNonzeroMagnitudes, nExpValues, nNonzeroExpValues,
       nInfs, nPosInfs, nNegInfs,
       nFiniteValues, nNonzeroFiniteValues,
       nPositiveFiniteValues, nNegativeFiniteValues,
       nFracMagnitudes, nNonzeroFracMagnitudes,
       nFracCycles, nExpCycles,
       index_to_code, index_to_offset, offset_to_index,
       compacttype,
       Signed_dict, Unsigned_dict,
       UF_dict, UE_dict, SF_dict, SE_dict

import Base: convert, oftype, precision, exponent_bias

using Static
using AlignedAllocs: memalign_clear, alignment
using SmallCollections, Dictionaries
=#
end  # AIFloats
