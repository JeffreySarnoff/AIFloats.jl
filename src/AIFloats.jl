module AIFloats

export AbstractAIFloat,
    # abstract supertypes
    AbstractUnsigned, AbstractSigned, 
    # Ako_ for fully qualified abstractions
    AkoUnsignedFinite, AkoUnsignedExtended,
    AkoSignedFinite, AkoSignedExtended,
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
    nbits, nbits_sig, nbits_frac, nbits_sign, nbits_exp,  
    nmagnitudes, nmagnitudes_nonzero, nmagnitudes_finite, nmagnitudes_finite_nonzero,
    nmagnitudes_prenormal, nmagnitudes_subnormal, nmagnitudes_normal,
    nvalues, nvalues_numeric, nvalues_numeric_nonzero, nvalues_finite, nvalues_finite_nonzero,
    nvalues_prenormal, nvalues_subnormal, nvalues_normal,
    nvalues_exp, nvalues_exp_nonzero,
    # exponent
    exp_bias,
    exp_unbiased_min, exp_unbiased_max, exp_unbiased_seq,
    exp_value_min, exp_value_max, exp_value_seq, 
    exp_subnormal_value, exp_normal_value_seq,
    exp_unbiased_subnormal, exp_unbiased_normal_max, exp_unbiased_normal_min, exp_unbiased_normal_seq,
    # extrema
    magnitude_subnormal_min, magnitude_subnormal_max,
    magnitude_normal_min, magnitude_normal_max,
    # functions over types
    encoding_seq, value_seq, magnitude_foundation_seq,
    # code <-> index  
    validate_code, validate_index,
    code_to_index, index_to_code,
    code_to_value, value_to_code,
    # code symmetries
    code_zero, code_one, code_negone,
    code_nan, code_posinf, code_neginf,
    # index symmetries
    index_zero, index_one, index_negone,
    index_nan, index_posinf, index_neginf,
    # code invariants      
    iscode_zero, iscode_one, iscode_negone,
    iscode_nan, iscode_inf, iscode_posinf, iscode_neginf,
    # index invariants      
    isindex_zero, isindex_one, isindex_negone,
    isindex_nan, isindex_inf, isindex_posinf, isindex_neginf    

setprecision(BigFloat, 768)
using ArbNumerics
import ArbNumerics: ArbReal

setworkingprecision(ArbReal, 768)

using Quadmath: Float128

ArbReal128(x) = ArbReal{128}(BigFloat(x))

function ArbNumerics.ArbReal{128}(x::Float128)
    ArbReal{128}(BigFloat(x))
end

function ArbNumerics.ArbReal(x::Float128)
    ArbReal(string(x))
end

function memalign_clear(T, n)
    zeros(T, n)
end

include("type/abstract.jl")
include("type/constants.jl")

include("type/predicates.jl")
include("type/counts.jl")
include("type/exponents.jl")
include("type/significands.jl")

# include("projection/rounding.jl")
# include("projection/saturation.jl")
# include("projection/stochastic.jl")

include("concrete/encodings.jl")
include("concrete/extrema.jl")
include("concrete/foundation.jl")
include("concrete/unsigned.jl")
include("concrete/signed.jl")

include("support/indices.jl")
include("support/julialang.jl")
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
