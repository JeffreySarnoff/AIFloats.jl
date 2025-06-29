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
        # exponent
        expBias, expUnbiasedValues, expMinValue, expMaxValue, expValues,
        # julia support
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

include("support/indices.jl")

include("concrete/encodings.jl")
include("concrete/foundation.jl")
include("concrete/unsigned.jl")
include("concrete/signed.jl")

include("support/julialang.jl")

const MaybeBool = Union{Nothing, Bool}

function AIFloat(bitwidth::Int, precision::Int;
                 signed::MaybeBool=nothing, unsigned::MaybeBool=nothing,
                 finite::MaybeBool=nothing, extended::MaybeBool=nothing)
    
    # are the keyword arguments consistent?
    if !differ(signed, unsigned)
        error("AIFloats: keyword args `signed` and `unsigned` must differ (one true, one false).")
    elseif !differ(finite, extended)
        error("AIFloats: keyword args `finite` and `extended` must differ (one true, one false).")
    end

    # are these arguments conformant?
    #                                signed                 unsigned
    params_ok = (precision >= 1) && ifelse(signed, bitwidth > precision, bitwidth >= precision)
    if !params_ok
        ifelse(unsigned, 
            error("AIFloats: Unsigned formats require `(1 <= precision <= bitwidth <= 15).`\n
                   AIFloat was called using (bitwidth = $bitwidth, precision = $precision)."),
            error("AIFloats: Signed formats require `(1 <= precision < bitwidth <= 15).\n
                   AIFloat was called using (bitwidth = $bitwidth, precision = $precision)."))
    end

    ConstructAIFloat(bitwidth, precision; signed, extended)
end

function ConstructAIFloat(bitwidth::Int, precision::Int; signed::Bool, extended::Bool)
    if signed
        if extended
            SignedExtendedFloats(bitwidth, precision)
        else # finite
            SignedFiniteFloats(bitwidth, precision)
        end
    else # unsigned
        if extended
            UnsignedExtendedFloats(bitwidth, precision)
        else # finite
            UnsignedFiniteFloats(bitwidth, precision)
        end
    end
end

differ(x::Bool, y::Bool)       = xor(x, y)

differ(x::Bool, y::Nothing)    = true
differ(x::Nothing, y::Bool)    = true
differ(x::Nothing, y::Nothing) = true  # intentional (this relation is necessary)

end  # AIFloats
