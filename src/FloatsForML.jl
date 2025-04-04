module FloatsForML

export AbstractMLFloat,
         AbsSignedMLFloat,
           AbsSignedExtendedMLFloat, AbsSignedFiniteMLFloat,
              SExtendedMLFloats,        SFiniteMLFloats,
         AbsUnsignedMLFloat,
           AbsUnsignedExtendedMLFloat, AbsUnsignedFiniteMLFloat,
              UExtendedMLFloats,          UFiniteMLFloats,
       #
       codes, floats,
       is_signed, is_unsigned, is_finite, is_extended,
       #
       bitwidth, precision,
       nBits, nSigBits, nFracBits, nSignBits, nExpBits,
       nValues, nFracValues, nExpValues,
       nNumericValues, nFiniteValues,
       nMagnitudes, nFiniteMagnitudes, nNonzeroMagnitudes, nNonzeroFiniteMagnitudes,
       nPosInfs, nNegInfs, nInfs, nZeros, nNaNs,
       nPositiveValues, nNegativeValues, nPositiveFiniteValues, nNegativeFiniteValues,
       nSubnormalValues, nSubnormalMagnitudes, nNormalValues, nNormalMagnitudes,
       #
       exponent_min, exponent_max, exponent_bias,
       subnormal_min, subnormal_max, normal_min, normal_max,
       #
       typeforcode, typeforfloat, CODE, FLOAT

import Base: convert, oftype, precision

using Static, AlignedAllocs

include("constants.jl")

include("type/abstract.jl")
include("type/collective.jl")

include("type/aspects.jl")
include("type/extrema.jl")
include("type/predicates.jl")

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
"""
function MLFloats(bits::Int, sigbits::Int, signed::Bool, extended::Bool)
    if signed
        if extended
            SExtendedMLFloats(bits, sigbits)
        else # finite
            SFiniteMLFloats(bits, sigbits)
        end
    else
        if extended
            UExtendedMLFloats(bits, sigbits)
        else # finite
            UFiniteMLFloats(bits, sigbits)
        end
    end
end

end  # FloatsForML
