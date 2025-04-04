abstract type FloatMLConfig{Bits, Precision, IsSigned} end

Base.@kwdef struct FloatMLconfig{Bits, Precision, IsSigned, IsExtended} <: FloatMLConfig{Bits, Precision, IsSigned}
    bits::Int = Bits
    precision::Int = Precision
    signed::Bool = IsSigned
    extended::Bool = IsExtended

    n_nans::Int = 1
    n_zeros::Int = 1
    n_infs::Int = IsExtended ? (IsSigned ? 2 : 1) : 0

    n_bits::Int = Bits
    n_significant_bits::Int = Precision
    n_fracbits::Int = Precision - 1            # trailing (explicit) significand bits
    n_exponent_bits::Int = Bits - Precision + !IsSigned
    n_sign_bits::Int = 0 + IsSigned

    # n_<>_values counts the number of signed occurrences 
    # n_<>_values counting includes zero

    n_values::Int = 2^n_bits
    n_extended_values::Int = n_values - n_nans                  # without NaN
    n_finite_values::Int = n_extended_values - n_infs           # without NaN and Infinity 
    n_nonzero_finite_values::Int = n_finite_values - n_zeros
    # n_<>_magnitudes counts the number of non-negative occurrences 
    
    n_magnitudes::Int = IsSigned ? n_nonzero_finite_values >> 1 : n_nonzero_finite_values

    n_fraction_magnitudes::Int = 2^(n_fracbits) - 1    # includes zero
    n_nonzero_fraction_magnitudes::Int = n_fraction_magnitudes - 1

    n_fraction_values::Int = 2 * n_fraction_magnitudes - 1   # includes zero once
    n_nonzero_fraction_values::Int = 2 * n_fraction_magnitudes - 2 # removes zero once

    # n_fraction_values::Int = 2^n_fracbits * (1 + IsSigned)
    n_exponent_values::Int = 2^n_exponent_bits

    n_subnormal_values::Int = (n_significant_bits > 1) ? n_fraction_values - (1 + IsSigned) : 0
    n_normal_values::Int = n_finite_values - n_subnormal_values # (n_values - n_nans - n_infs) - ()
    
    n_subnormal_magnitudes::Int = IsSigned ? n_subnormal_values >> 1 : n_subnormal_values
    n_normal_magnitudes::Int = IsSigned ? n_normal_values >> 1 : n_normal_values

    # n_fraction_cycles1::Int = div(n_values, n_fraction_values)
    n_fraction_cycles::Int = div(n_magnitudes, n_fraction_values)

    n_exponent_cycles::Int = div(n_magnitudes, n_exponent_values)
    # n_exponent_cycles::Int = div(n_magnitudes, n_exponent_values)

    # n_fraction_cycles::Int = n_exponent_values      # structural, generative
    # n_exponent_cycles1::Int = n_fraction_values      # structural, generative

    exp_bias::Int = 2^(n_exponent_bits - 1) - 1

    unbiased_exponent_min::Int = (n_significant_bits > 1) ? -exp_bias : -exp_bias + 1
    unbiased_exponent_max::Int = exp_bias

    exponent_min::Float64 = 2.0^unbiased_exponent_min
    exponent_max::Float64 = 2.0^unbiased_exponent_max
    
    subnormal_min::Float64 = exponent_min * (1//n_fraction_magnitudes)
    subnormal_max::Float64 = exponent_min * ((n_fraction_magnitudes - 1)//n_fraction_magnitudes)

    normal_min::Float64 = exponent_min * (1//1)
    normal_finite_max::Float64 = exponent_max * ((n_fraction_magnitudes - 1)//n_fraction_magnitudes)
    normal_extended_max::Float64 = exponent_max * ((n_fraction_magnitudes - 2)//n_fraction_magnitudes)
end

const ConfigFloatMLnames = fieldnames(FloatMLconfig)
const ConfigFloatMLtypes = Tuple{fieldtypes(FloatMLconfig)...}
const ConfigFloatMLentries = Val(length(ConfigFloatMLnames))
const ConfigFloatML = NamedTuple{ConfigFloatMLnames, ConfigFloatMLtypes}

function config_floatml(bits, precision, is_signed, is_extended)
    specs = FloatMLconfig{bits, precision, is_signed, is_extended}()
    ConfigFloatML(ntuple(i->getfield(specs, i), ConfigFloatMLentries))
end
