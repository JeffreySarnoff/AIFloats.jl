module AIFloats

export AbstractAIFloat,
         AbsUnsignedFloat,
           AbsUnsignedFiniteFloat, AbsUnsignedExtendedFloat,
         AbsSignedFloat,
           AbsSignedFiniteFloat, AbsSignedExtendedFloat,
        # concrete types
        floats, codes,
        # generalized constructor
        AIFloat, 
        UnsignedFiniteFloat, UnsignedExtendedFloat,
        SignedFiniteFloat, SignedExtendedFloat,
        # typed predicates
        is_aifloat, is_unsigned, is_signed, is_finite, is_extended,
        # functions over types
        encoding_sequence, value_sequence,
        magnitude_sequence, foundation_magnitudes,
        # counts predicated on abstract [sub]type
        nBits, nSigBits, nFracBits, nSignBits, nExpBits,
        nNaNs, nZeros, nInfs, nPosInfs, nNegInfs,
        nPrenormalMagnitudes, nSubnormalMagnitudes, nNormalMagnitudes, nMagnitudes,
        nValues, nNumericValues, nNonzeroNumericValues,
        nMagnitudes, nNonzeroMagnitudes,
        nExpValues, nNonzeroExpValues,
        nFiniteValues, nNonzeroFiniteValues,
        # exponent
        expBias, expUnbiasedValues, expMinValue, expMaxValue, expValues,
        # julia support
        index1, indexneg1, value_to_index, index_to_value, floatleast,
        ulp_distance
        # counts predicated on type defining parameters and type specifying qualities
        # parameters: (bits, sigbits, exponent bias)
        # qualities: (signedness [signed / unsigned], finiteness [finite / extended (has Inf[s])])

using AlignedAllocs: memalign_clear, alignment
using Static: static, dynamic, StaticInt, StaticBool
using Quadmath: Float128


include("type/constants.jl")

include("type/abstract.jl")
include("type/counts.jl")
include("type/exponents.jl")

include("projection/rounding.jl")
# include("projection/saturation.jl")
# include("projection/stochastic.jl")

include("concrete/encodings.jl")
include("concrete/foundation.jl")
include("concrete/unsigned.jl")
include("concrete/signed.jl")

include("support/indices.jl")
# include("support/julialang.jl")
include("support/maybe_bool.jl")


differ(x::Bool, y::Bool)       = xor(x, y)

differ(x::Bool, y::Nothing)    = true
differ(x::Nothing, y::Bool)    = true
differ(x::Nothing, y::Nothing) = true               # this relation is necessary

Base.convert(::Type{Bool}, x::Nothing) = false      # the conversion logic promulgates consistency
Base.convert(::Type{Nothing}, x::Bool) = nothing    # 

differ(x::Bool, y::Missing)    = true
differ(x::Missing, y::Bool)    = true
differ(x::Missing) = true               # this relation is necessary

"""
      MaybeBool

A type that can be `Bool`, `Missing`, or `Union{Missing, Bool}`.

used to type keyword arguments: 
-  contributing to clean, clear, generalized construction 

specializes on signedness and finiteness:
- with either of the two signedness symbols
    -  `SignedFloat`, `UnsignedFloat`
- with either of the two finiteness symbols
    - `FiniteFloat`, `ExtendedFloat`

""" MaybeBool, UnsignedFloat, SignedFloat, FiniteFloat, ExtendedFloat

const MaybeBool = Union{Bool, Missing}

const UnsignedFloat = true
const SignedFloat   = true
const FiniteFloat   = true
const ExtendedFloat = true

function AIFloat(bitwidth::Int, sigbits::Int;
                 SignedFloat::MaybeBool=nothing, UnsignedFloat::MaybeBool=nothing,
                 FiniteFloat::MaybeBool=nothing, ExtendedFloat::MaybeBool=nothing)
    
    # are the keyword arguments consistent?
    if !differ(SignedFloat, UnsignedFloat)
        error("AIFloats: keyword args `SignedFloats` and `UnsignedFloats` must differ (one true, one false).")
    elseif !differ(FiniteFloat, ExtendedFloat)
        error("AIFloats: keyword args `FiniteFloat` and `ExtendedFloat` must differ (one true, one false).")
    end

    # complete the keyword initializing

    SignedFloat    = isnothing(SignedFloat)   ? ~UnsignedFloat  :  SignedFloat
    UnsignedFloat  = isnothing(SignedFloat)   ? ~SignedFloat    :  UnsignedFloat
    
    ExtendedFloat  = isnothing(ExtendedFloat) ? ~FiniteFloat   : ExtendedFloat
    FiniteFloat    = isnothing(FiniteFloat)   ? ~ExtendedFloat : FiniteFloat

    # are these arguments conformant?
    params_ok = (sigbits >= 1) && 
                (SignedFloat ? bitwidth > sigbits : bitwidth >= sigbits)
    
    if !params_ok
        ifelse(UnsignedFloat, 
            error("AIFloats: Unsigned formats require `(1 <= precision <= bitwidth <= 15).`\n
                   AIFloat was called using (bitwidth = $bitwidth, precision = $sigbits)."),
            error("AIFloats: Signed formats require `(1 <= precision < bitwidth <= 15).\n
                   AIFloat was called using (bitwidth = $bitwidth, precision = $sigbits)."))
    end

    ConstructAIFloat(bitwidth, sigbits; SignedFloat, UnsignedFloat)
end

function ConstructAIFloat(bitwidth::Int, sigbits::Int; 
                          SignedFloat::Bool, ExtendedFloat::Bool)
    if SignedFloats
        if ExtendedFloat
            SignedExtendedFloat(bitwidth, sigbits)
        else # FiniteFloat
            SignedFiniteFloat(bitwidth, sigbits)
        end
    else # UnsignedFloats
        if ExtendedFloat
            UnsignedExtendedFloat(bitwidth, sigbits)
        else # FiniteFloat
            UnsignedFiniteFloat(bitwidth, sigbits)
        end
    end
end

end  # AIFloats
