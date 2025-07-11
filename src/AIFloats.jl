module AIFloats

export AbstractAIFloat,
    # abstract types
    AbstractUnsigned, AkoUnsignedFinite, AkoUnsignedExtended,
    AbstractSigned, AkoSignedFinite, AkoSignedExtended,
    # concrete constructive types
    UnsignedFinite, UnsignedExtended,
    SignedFinite, SignedExtended,
    # field retrieval 
    floats, codes,
    # generalized constructor, keyword consts
    AIFloat,
    # type characterization predicates
    is_aifloat, is_unsigned, is_signed, is_finite, is_extended,
    # subtype characterization predicate
    has_subnormals,
    # counts by fiat
    nNaNs, nZeros,
    # counts by format definitions 
    nInfs, nPosInfs, nNegInfs,
    # counts predicated on abstract [sub]type
    nbits, nbits_sig, nFracBits, nSignBits, nbits_exp,  
    nmagnitudes, nNonzeroMagnitudes, nFiniteMagnitudes, nNonzeroFiniteMagnitudes,
    nPrenormalMagnitudes, nSubnormalMagnitudes, nNormalMagnitudes,
    nvalues, nNumericValues, nNonzeroNumericValues, nFiniteValues, nNonzeroFiniteValues,
    nPrenormalValues, nSubnormalValues, nNormalValues,
    nExpValues, nNonzeroExpValues,
    # exponent
    expBias, expMin, expMax, expMinValue, expMaxValue, expValues,
    expSubnormal, expSubnormalValue, expUnbiasedValues,
    # extrema
    subnormalMagnitudeMin, subnormalMagnitudeMax,
    normalMagnitudeMin, normalMagnitudeMax,
    # functions over types
    encoding_sequence, value_sequence, foundation_magnitudes,
    # indices and offsets
    index_to_offset, offset_to_index,
    index1,  
    value_to_index, index_to_value, value_to_offset, offset_to_value,
    is_idxnan, is_ofsnan 
    # counts predicated on type defining parameters and type specifying qualities
    # parameters: (bits, sigbits, exponent bias)
    # qualities: (signedness [signed / unsigned], finiteness [finite / extended (has Inf[s])])

using AlignedAllocs: memalign_clear, alignment
using Static: static, dynamic, StaticInt, StaticBool
using Quadmath: Float128

include("type/abstract.jl")
include("type/constants.jl")

include("type/predicates.jl")
include("type/counts.jl")
include("type/exponents.jl")
include("type/significands.jl")

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
include("support/aqua.jl")

"""    
    AIFloat(<:AbstractAIFloat)

    AIFloat(bitwidth, precision, `<signedness>`, `<domain`)

- bitwidth is the total number of bits in the floating-point representation
- precision is the number of bits in the significand (implicit bit + fractional bits)

-  `<signedness>` is one of {:signed, :unsigned} 
-  `<domain>`     is one of {:finite, :extended} 

generates a corresponding concrete AI floating-point type

see [`floats`](@ref), [`codes`](@ref)
""" AIFloat

"""
    floats(x_or_T)

the canonical value sequence for the given type.

see [`AIFloat`](@ref), [`codes`](@ref), [`x_or_T`](@ref)
""" floats

"""
    codes(x_or_T)

the canonical encoding sequence for the given type.

see [`AIFloat`](@ref), [`floats`](@ref), [`x_or_T`](@ref)
""" codes

"""
    x_or_T

`func(x_or_T)` means `func` works with abstract and concrete arguments
- the concrete x::T 
- the abstract T::Type
""" x_or_T

x_or_T() = true  # placeholder for x_or_T so docs work

function AIFloat(bitwidth::Int, sigbits::Int, kinds...)
    plusminus, nonnegative, extended, finite = 
        map(kw->kw in kinds, (:signed, :unsigned, :extended, :finite))
     
    # are the keyword arguments consistent?
    if !xor(plusminus, nonnegative)
        error("AIFloats: specify one of `:signed` or `:unsigned`.")
    elseif !xor(extended, finite)
        error("AIFloats: specify one of `:extended` or `:finite`.")
    end

    # are these arg values conformant?
    params_ok = (sigbits >= 1) && 
                (plusminus ? bitwidth > sigbits : bitwidth >= sigbits)
    
    if !params_ok
        ifelse(nonnegative, 
            error("AIFloats: Unsigned formats require `(1 <= precision <= bitwidth <= 15).`\n
                   AIFloat was called using (bitwidth = $bitwidth, precision = $sigbits)."),
            error("AIFloats: Signed formats require `(1 <= precision < bitwidth <= 15).\n
                   AIFloat was called using (bitwidth = $bitwidth, precision = $sigbits)."))
    end

    ConstructAIFloat(bitwidth, sigbits; plusminus, extended)
end

function ConstructAIFloat(bitwidth::Int, sigbits::Int; 
                          plusminus::Bool, extended::Bool)
    if plusminus
        if extended
            SignedExtended(bitwidth, sigbits)
        else # finite
            SignedFinite(bitwidth, sigbits)
        end
    else # nonnegative
        if extended
            UnsignedExtended(bitwidth, sigbits)
        else # finite
            UnsignedFinite(bitwidth, sigbits)
        end
    end
end

function AIFloat(T::Type{<:AbstractAIFloat})
    ConstructAIFloat(nbits(T), nbits_sig(T); plusminus=is_signed(T), extended=is_extended(T)) 
end

end  # AIFloats
