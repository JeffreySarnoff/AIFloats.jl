abstract type FloatMLConfig{Bitwidth, Precision, IsSigned} end

Base.@kwdef struct FloatMLconfig{Bitwidth, Precision, IsSigned} <: FloatMLConfig{Bitwidth, Precision, IsSigned}
    n_nans::Int = 1
    n_zeros::Int = 1

    n_bits::Int = Bitwidth
    n_significant_bits::Int = Precision
    n_fraction_bits::Int = Precision - 1            # trailing (explict) significand bits
    n_exponent_bits::Int = Bitwidth - Precision 
    n_sign_bits::Int = 0 + IsSigned

    n_values::Int = 2^n_bits
    n_fraction_values::Int = 2^n_fraction_bits
    n_exponent_values::Int = 2^n_exponent_bits

    n_fraction_cycles::Int = n_exponent_values      # structural, generative
    n_exponent_cycles::Int = n_fraction_values      # structural, generative

    exp_bias::Int = 2^(n_exponent_bits - 1) - 1

    unbiased_exponent_min::Int = 0 - exp_bias
    unbiased_exponent_max::Int = (n_exponent_values - 1) - exp_bias

    exponent_min::Float64 = 2.0^unbiased_exponent_min
    exponent_max::Float64 = 2.0^unbiased_exponent_max
end

const ConfigFloatMLnames = fieldnames(FloatMLconfig)
const ConfigFloatMLtypes = Tuple{fieldtypes(FloatMLconfig)...}
const ConfigFloatML = NamedTuple{ConfigFloatMLnames, ConfigFloatMLtypes}

function config_floatml(bitwidth, precision, issigned)
    specs = FloatMLconfig{bitwidth, precision, issigned}()

    # biased_exponents = collect( (0:n_exponents-1) .- bias )
    # exponent for subnormals equals the minimum exponent for normals
    # biased_exponents[1] = biased_exponents[2]
    ConfigFloatML((getfield(specs, i) for i in 1:nfields(specs)))
end






UnsignedConfig(Bits, Precision) = Config{0, Bits, Precision}()
SignedConfig(Bits, Precision) = Config{1, Bits, Precision}()

function Base.show(io::IO, ::MIME"text/plain", x::Config)
    nt = ConfigNT((getfield(sc,i) for i in 1:nfields(x)))
    print(io, nt)
end

