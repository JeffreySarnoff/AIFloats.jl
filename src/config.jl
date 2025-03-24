abstract type FloatMLConfig{Bitwidth, Precision, IsSigned} end

Base.@kwdef struct FloatMLconfig{Bitwidth, Precision, IsSigned, IsExtended} <: FloatMLConfig{Bitwidth, Precision, IsSigned}
    bitwidth::Int = Bitwidth
    precision::Int = Precision
    signed::Bool = IsSigned
    extended::Bool = IsExtended

    n_nans::Int = 1
    n_zeros::Int = 1
    n_infs::Int = IsExtended ? (IsSigned ? 2 : 1) : 0

    n_bits::Int = Bitwidth
    n_significant_bits::Int = Precision
    n_fraction_bits::Int = Precision - 1            # trailing (explict) significand bits
    n_exponent_bits::Int = Bitwidth - Precision 
    n_sign_bits::Int = 0 + IsSigned

    # n_<>_values counts the number of signed occurrences 
    # n_<>_values counting includes zero

    n_values::Int = 2^n_bits
    n_extended_values::Int = n_values - n_nans                  # without NaN
    n_finite_values::Int = n_extended_values - n_infs           # without NaN and Infinity 
    n_nonzero_finite_values::Int = n_finite_values - n_zeros
    # n_<>_magnitudes counts the number of non-negative occurrences 
    
    n_magnitudes::Int = IsSigned ? n_nonzero_finite_values >> 1 : n_nonzero_finite_values

    n_fraction_magnitudes::Int = 2^(n_fraction_bits) - 1    # includes zero
    n_nonzero_fraction_magnitudes::Int = n_fraction_magnitudes - 1

    n_fraction_values::Int = 2 * n_fraction_magnitudes - 1   # includes zero once
    n_nonzero_fraction_values::Int = 2 * n_fraction_magnitudes - 2 # removes zero once

    # n_fraction_values::Int = 2^n_fraction_bits * (1 + IsSigned)
    n_exponent_values::Int = 2^n_exponent_bits

    n_subnormal_values::Int = (n_significant_bits > 1) ? n_fraction_values - (1 + IsSigned) : 0
    n_normal_values::Int = n_finite_values - n_subnormal_values
    
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
end

const ConfigFloatMLnames = fieldnames(FloatMLconfig)
const ConfigFloatMLtypes = Tuple{fieldtypes(FloatMLconfig)...}
const ConfigFloatMLentries = Val(length(ConfigFloatMLnames))
const ConfigFloatML = NamedTuple{ConfigFloatMLnames, ConfigFloatMLtypes}

function config_floatml(bitwidth, precision, is_signed, is_extended)
    specs = FloatMLconfig{bitwidth, precision, is_signed, is_extended}()
    ConfigFloatML(ntuple(i->getfield(specs, i), ConfigFloatMLentries))
end

#=
   map(z->$(z[1])::$(z[2]), collect(zip( ConfigFloatMLnames, ConfigFloatMLtypes.parameters)))

 bitwidth::Int64
 precision::Int64
 signed::Bool
 extended::Bool
 n_nans::Int64
 n_zeros::Int64
 n_infs::Int64
 n_bits::Int64
 n_significant_bits::Int64
 n_fraction_bits::Int64
 n_exponent_bits::Int64
 n_sign_bits::Int64
 n_values::Int64
 n_extended_values::Int64
 n_finite_values::Int64
 n_nonzero_finite_values::Int64
 n_fraction_values::Int64
 n_exponent_values::Int64
 n_subnormal_values::Int64
 n_normal_values::Int64
 n_magnitudes::Int64
 n_subnormal_magnitudes::Int64
 n_normal_magnitudes::Int64
 n_fraction_cycles::Int64
 n_exponent_cycles::Int64
 exp_bias::Int64
 unbiased_exponent_min::Int64
 unbiased_exponent_max::Int64
 exponent_min::Float64
 exponent_max::Float64

 perm = sortperm(string.([ConfigFloatMLnames...]));
 ConfigFloatMLnamesSorted = ConfigFloatMLnames[perm];
 ConfigFloatMLtypesSorted = [ConfigFloatMLtypes.parameters...][perm]
 map(z->$(z[1])::$(z[2]), collect(zip( ConfigFloatMLnamesSorted, ConfigFloatMLtypesSorted.parameters)))

 bitwidth::Int64
 exp_bias::Int64
 exponent_max::Float64
 exponent_min::Float64
 extended::Bool
 n_bits::Int64
 n_exponent_bits::Int64
 n_exponent_cycles::Int64
 n_exponent_values::Int64
 n_extended_values::Int64
 n_finite_values::Int64
 n_fraction_bits::Int64
 n_fraction_cycles::Int64
 n_fraction_values::Int64
 n_infs::Int64
 n_magnitudes::Int64
 n_nans::Int64
 n_nonzero_finite_values::Int64
 n_normal_magnitudes::Int64
 n_normal_values::Int64
 n_sign_bits::Int64
 n_significant_bits::Int64
 n_subnormal_magnitudes::Int64
 n_subnormal_values::Int64
 n_values::Int64
 n_zeros::Int64
 precision::Int64
 signed::Bool
 unbiased_exponent_max::Int64
 unbiased_exponent_min::Int64

=#
