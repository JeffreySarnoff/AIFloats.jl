module AIFloats

export AbstractAIFloat,
       # abstract types
       AbsUnsignedFloat, AbsUnsignedFiniteFloat, AbsUnsignedExtendedFloat,
       AbsSignedFloat, AbsSignedFiniteFloat, AbsSignedExtendedFloat,
       # concrete types
       UnsignedFiniteFloat, UnsignedExtendedFloat,
       SignedFiniteFloat, SignedExtendedFloat,
       # field retrieval 
       floats, codes,
       # generalized constructor, keyword consts
       AIFloat, UnsignedFloat, SignedFloat, FiniteFloat, ExtendedFloat,
       # concrete constructive types
       UnsignedFiniteFloat, UnsignedExtendedFloat,
       SignedFiniteFloat, SignedExtendedFloat,
       # type characterization predicates
       is_aifloat, is_unsigned, is_signed, is_finite, is_extended,
       # subtype characterization predicate
        has_subnormals,
        # counts by fiat
        nNaNs, nZeros,
        # counts by format definitions 
        nInfs, nPosInfs, nNegInfs,
        # counts predicated on abstract [sub]type
        nBits, nSigBits, nFracBits, nSignBits, nExpBits,  
        nMagnitudes, nNonzeroMagnitudes, nFiniteMagnitudes, nNonzeroFiniteMagnitudes,
        nPrenormalMagnitudes, nSubnormalMagnitudes, nNormalMagnitudes,
        nValues, nNumericValues, nNonzeroNumericValues, nFiniteValues, nNonzeroFiniteValues,
        nPrenormalValues, nSubnormalValues, nNormalValues,
        nExpValues, nNonzeroExpValues,
        # exponent
        expBias, expMin, expMax, expMinValue, expMaxValue, expValues,
        expSubnormal, expSubnormalValue, expUnbiasedValues,
        # extrema
        subnormalMagnitudeMin, subnormalMagnitudeMax,
        normalMagnitudeMin, normalMagnitudeMax,
        # functions over types
        encoding_sequence, value_sequence,
         foundation_magnitudes,
        # indices and offsets
        index_to_offset, offset_to_index,
        index1,  
        value_to_index, index_to_value, value_to_offset, offset_to_value,
        is_idxnan, is_ofsnan 
        # counts predicated on type defining parameters and type specifying qualities
        # parameters: (bits, sigbits, exponent bias)
        # qualities: (signedness [signed / unsigned], finiteness [finite / extended (has Inf[s])])

using AlignedAllocs: memalign_clear, alignment
using Static: static, dynamic, StaticInt, StaticBool
using Quadmath: Float128

include("type/abstract.jl")
include("type/constants.jl")

include("type/predicates.jl")
include("type/counts.jl")
include("type/exponents.jl")
include("type/significands.jl")

include("projection/rounding.jl")
# include("projection/saturation.jl")
# include("projection/stochastic.jl")

include("concrete/encodings.jl")
include("concrete/extrema.jl")
include("concrete/foundation.jl")
include("concrete/unsigned.jl")
include("concrete/signed.jl")

include("support/indices.jl")
# include("support/julialang.jl")
include("support/aqua.jl")
  
const UnsignedFloat = true
const SignedFloat   = true
const FiniteFloat   = true
const ExtendedFloat = true

function AIFloat(bitwidth::Int, sigbits::Int;
                 SignedFloat::Bool=false, UnsignedFloat::Bool=false,
                 FiniteFloat::Bool=false, ExtendedFloat::Bool=false)
     
    # are the keyword arguments consistent?
    if !xor(SignedFloat, UnsignedFloat)
        error("AIFloats: specify one of `SignedFloat` or `UnsignedFloat`.")
    elseif !xor(FiniteFloat, ExtendedFloat)
        error("AIFloats: specify one of `FiniteFloat` or `ExtendedFloat`.")
    end

    # keywords are initialized
    # are these arguments conformant?
    params_ok = (sigbits >= 1) && 
                (SignedFloat ? bitwidth > sigbits : bitwidth >= sigbits)
    
    if !params_ok
        ifelse(UnsignedFloat, 
            error("AIFloats: Unsigned formats require `(1 <= precision <= bitwidth <= 15).`\n
                   AIFloat was called using (bitwidth = $bitwidth, precision = $sigbits)."),
            error("AIFloats: Signed formats require `(1 <= precision < bitwidth <= 15).\n
                   AIFloat was called using (bitwidth = $bitwidth, precision = $sigbits)."))
    end

    ConstructAIFloat(bitwidth, sigbits; SignedFloat, ExtendedFloat)
end

function ConstructAIFloat(bitwidth::Int, sigbits::Int; 
                          SignedFloat::Bool, ExtendedFloat::Bool)
    if SignedFloat
        if ExtendedFloat
            SignedExtendedFloat(bitwidth, sigbits)
        else # FiniteFloat
            SignedFiniteFloat(bitwidth, sigbits)
        end
    else # UnsignedFloat
        if ExtendedFloat
            UnsignedExtendedFloat(bitwidth, sigbits)
        else # FiniteFloat
            UnsignedFiniteFloat(bitwidth, sigbits)
        end
    end
end

function AIFloat(T::Type{<:AbstractAIFloat})
    ConstructAIFloat(nBits(T), nSigBits(T); SignedFloat=is_signed(T), ExtendedFloat=is_extended(T)) 
end

end  # AIFloats
