
# substructural counts

n_bits(x::T) where {Bitwidth, Precision,T<:AbstractBinaryFloat{Bitwidth, Precision}} = Bitwidth
n_sig_bits(x::T) where {Bitwidth, Precision,T<:AbstractBinaryFloat{Bitwidth, Precision}} = Precision
n_fraction_bits(x::T) where {Bitwidth, Precision,T<:AbstractBinaryFloat{Bitwidth, Precision}} = Precision - 1

n_sign_bits(x::T) where {Bitwidth, Precision,T<:AbstractUnsignedFloat{Bitwidth, Precision}} = 0
n_sign_bits(x::T) where {Bitwidth, Precision,T<:AbstractSignedFloat{Bitwidth, Precision}} = 1

n_exponent_bits(x::T) where {Bitwidth, Precision,T<:AbstractUnsignedFloat{Bitwidth, Precision}} = Bitwidth - Precision + 1
n_exponent_bits(x::T) where {Bitwidth, Precision,T<:AbstractSignedFloat{Bitwidth, Precision}} = Bitwidth - Precision

n_values(x::T) where {Bitwidth, Precision,T<:AbstractBinaryFloat{Bitwidth, Precision}} = 2^n_bits(x)
n_sig_values(x::T) where {Bitwidth, Precision,T<:AbstractBinaryFloat{Bitwidth, Precision}} = 2^n_sig_bits(x)
n_fraction_values(x::T) where {Bitwidth, Precision,T<:AbstractBinaryFloat{Bitwidth, Precision}} = 2^n_fraction_bits(x)
n_exponent_values(x::T) where {Bitwidth, Precision,T<:AbstractBinaryFloat{Bitwidth, Precision}} = 2^n_exponent_bits(x)

n_fraction_cycles(x::T) where {Bitwidth, Precision,T<:AbstractBinaryFloat{Bitwidth, Precision}} = n_exponent_values(x)
n_exponent_cycles(x::T) where {Bitwidth, Precision,T<:AbstractBinaryFloat{Bitwidth, Precision}} = n_fraction_values(x)

#

n_numeric_values(x::T) where {Bitwidth, Precision,T<:AbstractBinaryFloat{Bitwidth, Precision}} = n_values(x) - 1
n_finite_values(x::T) where {Bitwidth, Precision,T<:AbstractBinaryFloat{Bitwidth, Precision}} =
    n_numeric_values(x) - n_infinite_values(x)

@inline function n_infinite_values(x::T) where {Bitwidth, Precision,T<:AbstractBinaryFloat{Bitwidth, Precision}}
    if is_finite(x)
        0
    elseif is_signed(x)
        2
    else
        1
    end 
end

n_subnormal_values(x::T) where {Bitwidth, Precision,T<:AbstractBinaryFloat{Bitwidth, Precision}} = n_fraction_values(x) - 1
n_normal_values(x::T) where {Bitwidth, Precision,T<:AbstractBinaryFloat{Bitwidth, Precision}} = 
     n_finite_values(x) - n_subnormal_values(x)
 
# extrema

log2_exponent_min(x::T) where {Bitwidth, Precision,T<:AbstractBinaryFloat{Bitwidth, Precision}} = 1 - 2^(n_exponent_bits(x) - 1) 
log2_exponent_max(x::T) where {Bitwidth, Precision,T<:AbstractBinaryFloat{Bitwidth, Precision}} = 2^(n_exponent_bits(x) - 1) - 1
exponent_bias(x::T) where {Bitwidth, Precision,T<:AbstractBinaryFloat{Bitwidth, Precision}} = 2^(n_exponent_bits(x) - 1)

exponent_min(x::T) where {Bitwidth, Precision,T<:AbstractBinaryFloat{Bitwidth, Precision}} = 2.0^log2_exponent_min(x)
exponent_max(x::T) where {Bitwidth, Precision,T<:AbstractBinaryFloat{Bitwidth, Precision}} = 2.0^log2_exponent_max(x)

function subnormal_min(x::T) where {Bitwidth, Precision,T<:AbstractBinaryFloat{Bitwidth, Precision}}
    n_sig_bits(x) == 1 && return NaN
    exponent_min(x) * (1 // n_fraction_values(x))
end

function subnormal_max(x::T) where {Bitwidth, Precision,T<:AbstractBinaryFloat{Bitwidth, Precision}}
    n_sig_bits(x) == 1 && return NaN
    exponent_min(x) * ((n_fraction_values(x) - 1) // n_fraction_values(x))
end

function normal_min(x::T) where {Bitwidth, Precision,T<:AbstractBinaryFloat{Bitwidth, Precision}}
    exponent_min(x) * (1 // 1)
end

function normal_max(x::T) where {Bitwidth, Precision,T<:AbstractBinaryFloat{Bitwidth, Precision}}
    emax = exponent_max(x)
    frac = 1 + ((n_fraction_values(x) - 1 - is_finite(x)) // n_fraction_values(x))
    iszero(frac) && return emax * (1 // 1)
    emax * frac
end
