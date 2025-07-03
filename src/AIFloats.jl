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
        UnsignedFloat, SignedFloat,
        FiniteFloat, ExtendedFloat,
        # concrete constructors        
        UnsignedFiniteFloats, UnsignedExtendedFloats,
        SignedFiniteFloats, SignedExtendedFloats,
        # typed predicates
        is_aifloat, is_unsigned, is_signed, is_finite, is_extended,
        has_subnormals,
        # counts predicated on abstract [sub]type
        nBits, nSigBits, nFracBits, nSignBits, nExpBits,  
        nNaNs, nZeros, nInfs, nPosInfs, nNegInfs,
        nPrenormalMagnitudes, nSubnormalMagnitudes, nNormalMagnitudes, nMagnitudes,
        nPrenormalValues, nSubnormalValues, nNormalValues,
        nValues, nNumericValues, nNonzeroNumericValues,
        nMagnitudes, nNonzeroMagnitudes,
        nExpValues, nNonzeroExpValues,
        nFiniteValues, nNonzeroFiniteValues,
        # exponent
        expBias, expMin, expMax, expMinValue, expMaxValue, expValues,
        expSubnormal, expSubnormalValue, expUnbiasedValues,
        # extrema
        subnormalMagnitudeMin, subnormalMagnitudeMax,
        normalMagnitudeMin, normalMagnitudeMax,
        # functions over types
        encoding_sequence, value_sequence,
        magnitude_sequence, foundation_magnitudes,
        # julia support
        index_to_offset, offset_to_index,
        is_idxnan, is_ofsnan,   
        index1, indexneg1, valuetoindex, indextovalue, floatleast,
        ulp_distance
        # counts predicated on type defining parameters and type specifying qualities
        # parameters: (bits, sigbits, exponent bias)
        # qualities: (signedness [signed / unsigned], finiteness [finite / extended (has Inf[s])])

using AlignedAllocs: memalign_clear, alignment
using Static: static, dynamic, StaticInt, StaticBool
using Quadmath: Float128


include("type/constants.jl")

include("type/abstract.jl")
include("type/predicates.jl")
include("type/counts.jl")
include("type/exponents.jl")
include("type/significands.jl")

typeforfloat(::Type{T}) where {T<:AbstractAIFloat} = typeforfloat(nBits(T))
typeforcode(::Type{T}) where {T<:AbstractAIFloat} = typeforcode(nBits(T))

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
            SignedExtendedFloats(bitwidth, sigbits)
        else # FiniteFloats
            SignedFiniteFloats(bitwidth, sigbits)
        end
    else # UnsignedFloat
        if ExtendedFloat
            UnsignedExtendedFloats(bitwidth, sigbits)
        else # FiniteFloat
            UnsignedFiniteFloats(bitwidth, sigbits)
        end
    end
end

function AIFloat(T::Type{<:AbstractAIFloat})
    ConstructAIFloat(nBits(T), nSigBits(T); SignedFloat=is_signed(T), ExtendedFloat=is_extended(T)) 
end

end  # AIFloats
