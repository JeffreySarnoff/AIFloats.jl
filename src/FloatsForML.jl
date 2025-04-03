module FloatsForML

export AbstractAIFloat, MLFloats,
       UFiniteMLFloats, UExtendedMLFloats, SFiniteMLFloats, SExtendedMLFloats,
       UFiniteAIValues, UExtendedAIValues, SFiniteAIValues, SExtendedAIValues,
       UFiniteAICodes, UExtendedAICodes, SFiniteAICodes, SExtendedAICodes,
       NTupleOrVec, CODE, FLOAT, typeforcode, typeforfloat,
       IsSigned, IsUnsigned, IsFinite, IsExtended,
       codes, floats,
       nBits, nSigBits, nFracBits, nExpBits,
       nValues, nFracValues, nExpValues, nFracCycles, nExpCycles,
       nSubnormalValues, nSubnormalMagnitudes, nNormalValues, nNormalMagnitudes,
       nInfs, nNaNs, nZeros,
       exponent_min, exponent_max, exponent_bias,
       subnormal_min, subnormal_max, normal_min, normal_max,
       is_signed, is_unsigned, if_finite, is_extended,
       isaligned

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

end  # FloatsForML
