module FloatsForML

export AbstractFloatML,
         AbsSignedFloatML,
           AbsSignedExtendedFloatML, AbsSignedFiniteFloatML,
              SExtendedFloatsML,        SFiniteFloatsML,
         AbsUnsignedFloatML,
           AbsUnsignedExtendedFloatML, AbsUnsignedFiniteFloatML,
              UExtendedFloatsML,          UFiniteFloatsML,
       MLFLOATS, IsSigned, IsUnsigned, IsExtended, IsFinite, 
       bitwidth, precision,
       is_signed, is_unsigned, is_finite, is_extended,
       codes, floats, typeforcode, typeforfloat,
       exponent_min, exponent_max, exponent_bias,
       subnormal_min, subnormal_max, normal_min, normal_max,
       nBits, nSigBits, nFracBits, nSignBits, nExpBits,
       nPosInfs, nNegInfs, nInfs, nZeros, nNaNs,
       nValues,
       nMagnitudes, nFiniteMagnitudes, nNumericValues, nFiniteValues,
       nSubnormalMagnitudes, nNormalMagnitudes, nSubnormalValues, nNormalValues

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
    MLFLOATS

examples

```
    UF42   = MLFLOATS( 4,  2, IsUnsigned, IsFinite)
    UE64   = MLFLOATS( 6,  4, IsUnsigned, IsExtended)
    SE84   = MLFLOATS( 8,  4, IsSigned,   IsExtended)
    SE1512 = MLFLOATS(15, 12, IsSigned,   IsExtended)

    seBinary84_encodings = codes(SE84)
    seBinary84_valuation = floats(SE84)

````
"""
function MLFLOATS(bits::Int, sigbits::Int, signed::Bool, extended::Bool)
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

end  # FloatsForML
