
Base.convert(::Type{Bool}, x::Missing) = false      # the conversion logic promulgates consistency
Base.convert(::Type{Missing}, x::Bool) = missing    # 

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
        error("AIFloats: keyword args `FiniteFloats` and `ExtendedFloats` must differ (one true, one false).")
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

    ConstructsAIFloat(bitwidth, sigbits; SignedFloat, UnsignedFloat)
end



function ConstructsAIFloat(bitwidth::Int, sigbits::Int; 
                          SignedFloat::Bool, ExtendedFloat::Bool)
    if SignedFloats
        if ExtendedFloats
            SignedExtendedFloats(bitwidth, sigbits)
        else # FiniteFloats
            SignedFiniteFloats(bitwidth, sigbits)
        end
    else # UnsignedFloats
        if ExtendedFloats
            UnsignedExtendedFloats(bitwidth, sigbits)
        else # FiniteFloats
            UnsignedFiniteFloats(bitwidth, sigbits)
        end
    end
end

