module FloatsForML

export AbstractAIFloat,
         AbsSignedAIFloat,
           AbsSignedExtendedAIFloat, AbsSignedFiniteAIFloat,
              SExtendedFloats,        SFiniteFloats,
         AbsUnsignedAIFloat,
           AbsUnsignedExtendedAIFloat, AbsUnsignedFiniteAIFloat,
              UExtendedFloats,          UFiniteFloats,
       MLFloats,
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
       nFracMagnitudes, nNonzeroFracMagnitudes,
       nMagnitudes, nNonzeroMagnitudes, nExpValues, nNonzeroExpValues,
       nInfs, nPosInfs, nNegInfs,
       nFiniteValues, nPositiveFiniteValues, nNegativeFiniteValues,
       index_to_code, index_to_offset, offset_to_index,
       compacttype,
       Signed_dict, Unsigned_dict,
       UF_dict, UE_dict, SF_dict, SE_dict

import Base: convert, oftype, precision, exponent_bias

using Static
using AlignedAllocs: memalign_clear, alignment
using Dictionaries


include("constants.jl")

include("type/primitive_aspects.jl")

include("type/abstract.jl")
include("type/collective.jl")
include("type/compact.jl")

#include("type/aspects.jl")
include("type/exp_extrema.jl")
include("type/predicates.jl")

include("concrete/indices.jl")
include("concrete/foundation.jl")
include("concrete/unsigned.jl")
include("concrete/signed.jl")

Unsigned_dict = Dictionary{Symbol, AbstractAIFloat}()
Signed_dict = Dictionary{Symbol, AbstractAIFloat}()

UF_dict = Dictionary{Symbol, AbstractAIFloat}()
UE_dict = Dictionary{Symbol, AbstractAIFloat}()
SF_dict = Dictionary{Symbol, AbstractAIFloat}()
SE_dict = Dictionary{Symbol, AbstractAIFloat}()

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
            valueseq = SExtendedFloats(bits, sigbits)
            if !haskey(SE_dict, symbol(valueseq))
                insert!(SE_dict, symbol(valueseq), valueseq)
            end
            if !haskey(Signed_dict, symbol(valueseq))
                insert!(Signed_dict, symbol(valueseq), valueseq)
            end
        else # finite
            valueseq = SFiniteFloats(bits, sigbits)
            if !haskey(SF_dict, symbol(valueseq))
                insert!(SF_dict, symbol(valueseq), valueseq)
            end
            if !haskey(Signed_dict, symbol(valueseq))
                insert!(Signed_dict, symbol(valueseq), valueseq)
            end
        end
    else
        if extended
            valueseq = UExtendedFloats(bits, sigbits)
            if !haskey(UE_dict, symbol(valueseq))
                insert!(UE_dict, symbol(valueseq), valueseq)
            end
            if !haskey(Unsigned_dict, symbol(valueseq))
                insert!(Unsigned_dict, symbol(valueseq), valueseq)
            end
        else # finite
            valueseq = UFiniteFloats(bits, sigbits)
            if !haskey(UF_dict, symbol(valueseq))
                insert!(UF_dict, symbol(valueseq), valueseq)
            end
            if !haskey(Unsigned_dict, symbol(valueseq))
                insert!(Unsigned_dict, symbol(valueseq), valueseq)
            end
        end
    end
    valueseq
end

#=
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
=#

end  # FloatsForML
