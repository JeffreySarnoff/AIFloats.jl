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

function AIFloat(bitwidth::Int, sigbits::Int;
                 is_signed::MaybeBool=nothing, is_unsigned::MaybeBool=nothing,
                 is_finite::MaybeBool=nothing, is_extended::MaybeBool=nothing)
    
    # are the keyword arguments consistent?
    if !differ(is_signed, is_unsigned)
        error("AIFloats: keyword args `is_signed` and `is_unsigned` must differ (one true, one false).")
    elseif !differ(is_finite, is_extended)
        error("AIFloats: keyword args `is_finite` and `is_extended` must differ (one true, one false).")
    end

    # complete the keyword initializing

    is_signed = isnothing(is_signed) ? ~is_unsigned : is_signed
    is_unsigned = isnothing(is_signed) ? ~is_signed : is_unsigned
    
    is_extended = isnothing(is_extended) ? ~is_finite : is_extended
    is_finite = isnothing(is_finite) ? ~is_extended : is_finite

    # are these arguments conformant?
    params_ok = (sigbits >= 1) && 
                (is_signed ? bitwidth > sigbits : bitwidth >= sigbits)
    
    if !params_ok
        ifelse(is_unsigned, 
            error("AIFloats: Unsigned formats require `(1 <= precision <= bitwidth <= 15).`\n
                   AIFloat was called using (bitwidth = $bitwidth, precision = $sigbits)."),
            error("AIFloats: Signed formats require `(1 <= precision < bitwidth <= 15).\n
                   AIFloat was called using (bitwidth = $bitwidth, precision = $sigbits)."))
    end

    ConstructAIFloat(bitwidth, sigbits; is_signed, is_extended)
end

function ConstructAIFloat(bitwidth::Int, sigbits::Int; is_signed::Bool, is_extended::Bool)
    if is_signed
        if is_extended
            SignedExtendedFloats(bitwidth, sigbits)
        else # finite
            SignedFiniteFloats(bitwidth, sigbits)
        end
    else # unsigned
        if is_extended
            UnsignedExtendedFloats(bitwidth, sigbits)
        else # finite
            UnsignedFiniteFloats(bitwidth, sigbits)
        end
    end
end

differ(x::Bool, y::Bool)       = xor(x, y)

differ(x::Bool, y::Nothing)    = true
differ(x::Nothing, y::Bool)    = true
differ(x::Nothing, y::Nothing) = true               # this relation is necessary

Base.convert(::Type{Bool}, x::Nothing) = false      # this conversion is necessary

end  # AIFloats
