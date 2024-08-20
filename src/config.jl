abstract type MicroFloatConfig end

Base.@kwdef struct Config{SignBits, Bits, Precision} <: MicroFloatConfig
    n_bits::Int = Bits
    n_significant_bits::Int = Precision
    n_fraction_bits::Int = Precision - 1
    n_exponent_bits = Bits - Precision + iszero(SignBits)
    n_sign_bits::Int = SignBits

    n_values::Int = 2^n_bits
    n_fractions::Int = 2^n_fraction_bits
    n_exponents::Int = 2^n_exponent_bits
    n_normal_exponents::Int = n_exponents - 1

    n_fraction_cycles::Int = n_exponents
    n_exponent_cycles::Int = n_fractions

    exponent_max::Int = 2^(Bits-Precision) - 1
    exponent_min::Int = 1 - 2^(Bits-Precision) 
    exponent_bias::Int = 2^(Bits-Precision)
end

const ConfigFields = fieldnames(Config)
const ConfigTypes  = NTuple{length(ConfigFields), Int}
const ConfigNT = NamedTuple{ConfigFields, ConfigTypes}

UnsignedConfig(Bits, Precision) = Config{0, Bits, Precision}()
SignedConfig(Bits, Precision) = Config{1, Bits, Precision}()

function Base.show(io::IO, ::MIME"text/plain", x::Config)
    nt = ConfigNT((getfield(sc,i) for i in 1:nfields(x)))
    print(io, nt)
end

