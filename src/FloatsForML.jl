module FloatsForML

export AbstractFloatML,
         AbsSignedFloatML,
           AbsSExtendedFloatML, AbsSFiniteFloatML,
              SExtendedFloatsML,        SFiniteFloatsML,
         AbsUnsignedFloatML,
           AbsUExtendedFloatML, AbsUFiniteFloatML,
              UExtendedFloatsML,          UFiniteFloatsML,
       MLFloats,
       CODE, FLOAT,
       IsSigned, IsUnsigned, IsExtended, IsFinite,
       is_signed, is_unsigned, is_finite, is_extended,
       codes, floats, nonneg_codes, nonneg_floats,
       typeforcode, typeforfloat,
       bitwidth, precision,
       exponent_min, exponent_max, exponent_bias,
       subnormal_min, subnormal_max, normal_min, normal_max,
       nBits, nSigBits, nFracBits, nSignBits, nExpBits,
       nPosInfs, nNegInfs, nInfs, nZeros, nNaNs,
       nValues,
       nMagnitudes, nFiniteMagnitudes, nNumericValues, nFiniteValues,
       nSubnormalMagnitudes, nNormalMagnitudes, nSubnormalValues, nNormalValues,
       index_to_code, index_to_offset, offset_to_index

import Base: convert, oftype, precision, exponent_bias

using Static, AlignedAllocs

include("constants.jl")

include("type/abstract.jl")
include("type/collective.jl")

include("type/aspects.jl")
include("type/exp_extrema.jl")
include("type/predicates.jl")

include("concrete/indices.jl")
include("concrete/foundation.jl")
include("concrete/unsigned.jl")
include("concrete/signed.jl")

"""
    MLFloats

examples

```
    UF42   = MLFloats( 4,  2, IsUnsigned, IsFinite)
    UE64   = MLFloats( 6,  4, IsUnsigned, IsExtended)
    SE84   = MLFloats( 8,  4, IsSigned,   IsExtended)
    SE1512 = MLFloats(15, 12, IsSigned,   IsExtended)

    seBinary84_encodings = codes(SE84)
    seBinary84_valuation = floats(SE84)

````
""" MLFloats



function MLFloats(bits::Int, sigbits::Int, signed::Bool, extended::Bool)
    if signed
        if extended
            SExtendedFloats(bits, sigbits)
        else # finite
            SFiniteFloats(bits, sigbits)
        end
    else
        if extended
            UExtendedFloats(bits, sigbits)
        else # finite
            UFiniteFloats(bits, sigbits)
        end
    end
end

#=
function MLFloats(bits::Int, sigbits::Int, signed::Bool, extended::Bool)
    if signed
        if extended
            SExtendedFloatsML(bits, sigbits)
        else # finite
            SFiniteFloatsML(bits, sigbits)
        end
    else
        if extended
            UExtendedFloatsML(bits, sigbits)
        else # finite
            UFiniteFloatsML(bits, sigbits)
        end
    end
end
=#

end  # FloatsForML
