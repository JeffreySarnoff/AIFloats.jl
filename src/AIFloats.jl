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
    n_nans, n_zeros,
    # counts by format definitions 
    n_inf, n_pos_inf, n_neg_inf,
    # counts predicated on abstract [sub]type
    nbits, n_sig_bits, n_frac_bits, n_sign_bits, n_exp_bits,  
    nmags, n_nonzero_mags, n_finite_mags, n_nonzero_finite_mags,
    n_prenormal_mags, n_subnormal_mags, n_normal_mags,
    n_values, n_nums, n_nonzero_nums, n_finite_nums, n_nonzero_finite_nums,
    n_prenormal_nums, n_subnormal_nums, n_normal_nums,
    n_exp_nums, n_nonzero_exp_nums,
    # exponent
    exp_bias,
    exp_unbiased_min, exp_unbiased_max, exp_unbiased_seq,
    exp_value_min, exp_value_max, exp_value_seq, 
    exp_subnormal_value, exp_normal_value_seq,
    exp_unbiased_subnormal, exp_unbiased_normal_max, exp_unbiased_normal_min, exp_unbiased_normal_seq,
    # extrema
    mag_subnormal_min, mag_subnormal_max,
    mag_normal_min, mag_normal_max,
    # functions over types
    encoding_seq, value_seq, mag_foundation_seq,
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

setprecision(BigFloat, 128)

function memalign_clear(T, n)
    zeros(T, n)
end


# a broader view of appropriate float types
# UnsignedFinite{bits, sigbits, T<:AbstractFP, S<:Unsigned} <: AkoUnsignedFinite{bits, sigbits}
# 
using Quadmath, ArbNumerics

abstract type AbstractAIFloat{Bits, SigBits} <: AbstractFloat end
const AbstractFP = Union{AbstractFloat, AbstractAIFloat}

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
include("support/convert.jl")
include("support/parts.jl")
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
    ConstructAIFloat(n_bits(T), n_sig_bits(T); plusminus=is_signed(T), extended=is_extended(T)) 
end

end  # AIFloats
