module FloatsForML

export AbstractFloatML,
         AbsSignedFloatML,
           AbsSExtendedFloatML, AbsSFiniteFloatML,
              SExtendedFloats,        SFiniteFloats,
         AbsUnsignedFloatML,
           AbsUExtendedFloatML, AbsUFiniteFloatML,
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
       nBits, nSigBits, nFracBits, nSignBits, nExpBits,
       nPosInfs, nNegInfs, nInfs, nZeros, nNaNs,
       nValues,
       nMagnitudes, nFiniteMagnitudes, nNumericValues, nFiniteValues,
       nSubnormalMagnitudes, nNormalMagnitudes, nSubnormalValues, nNormalValues,
       index_to_code, index_to_offset, offset_to_index,
       compacttype,
       SignedDict, UnsignedDict,
       UFdict, UEdict, SFdict, SEdict 

import Base: convert, oftype, precision, exponent_bias

using Static
using AlignedAllocs: memalign_clear, alignment
using Dictionaries


include("constants.jl")

include("type/abstract.jl")
include("type/collective.jl")
include("type/compact.jl")

include("type/aspects.jl")
include("type/exp_extrema.jl")
include("type/predicates.jl")

include("concrete/indices.jl")
include("concrete/foundation.jl")
include("concrete/unsigned.jl")
include("concrete/signed.jl")

UnsignedDict = Dictionary{Symbol, AbstractFloatML}()
SignedDict = Dictionary{Symbol, AbstractFloatML}()

UFdict = Dictionary{Symbol, AbstractFloatML}()
UEdict = Dictionary{Symbol, AbstractFloatML}()
SFdict = Dictionary{Symbol, AbstractFloatML}()
SEdict = Dictionary{Symbol, AbstractFloatML}()

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
            insert!(SEdict, symbol(valueseq), valueseq)
        else # finite
            valueseq = SFiniteFloats(bits, sigbits)
            insert!(SFdict, symbol(valueseq), valueseq)
        end
    else
        if extended
            valueseq = UExtendedFloats(bits, sigbits)
            insert!(UEdict, symbol(valueseq), valueseq)
            insert!(Udict, symbol(valueseq), valueseq)
        else # finite
            valueseq = UFiniteFloats(bits, sigbits)
            insert!(UFdict, symbol(valueseq), valueseq)
            insert!(Udict, symbol(valueseq), valueseq)
        end
    end
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
