module FloatsForML

export AbstractMLFloat,
         AbsSignedMLFloat,
           AbsSignedExtendedMLFloat, AbsSignedFiniteMLFloat,
              SExtendedMLFloats,        SFiniteMLFloats,
         AbsUnsignedMLFloat,
           AbsUnsignedExtendedMLFloat, AbsUnsignedFiniteMLFloat,
              UExtendedMLFloats,          UFiniteMLFloats,
       #
       MLFloats, IsSigned, IsUnsigned, IsExtended, IsFinite, 
       #
       bitwidth, precision,
       is_signed, is_unsigned, is_finite, is_extended,
       codes, floats, typeforcode, typeforfloat,
       #
       exponent_min, exponent_max, exponent_bias,
       subnormal_min, subnormal_max, normal_min, normal_max

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

export nBits, nSigBits, nFracBits, nSignBits, nExpBits,
       nPosInfs, nNegInfs, nInfs, nZeros, nNaNs,
       nValues, nFracValues, nExpValues,
       nNumericValues, nFiniteValues,
       nPositiveValues, nNegativeValues, nPositiveFiniteValues, nNegativeFiniteValues,
       nSubnormalValues, nSubnormalMagnitudes, nNormalValues, nNormalMagnitudes,
       nMagnitudes, nFiniteMagnitudes, nNonzeroMagnitudes, nNonzeroFiniteMagnitudes

end  # FloatsForML
