encoding(cfg::FloatMLconfig) = encoding(cfg.bitwidth)
valuation(cfg::FloatMLconfig) = valuation(cfg.bitwidth, cfg.precision, 
                                          cfg.n_fraction_magnitudes, cfg.n_fraction_cycles,
                                          cfg.n_exponent_magnitudes, cfg.n_exponent_cycles)

function encoding(bitwidth)
    n = 2^bitwidth
    typ = typeforcode(bitwidth)
    codes = memalign_clear(typ, n)
    codes[:] = collect(map(typ, 0:(n-1)))
    codes
end

function valuation(bitwidth, precision; n_exponents, n_exponent_cycles)
    n = 2^bitwidth
    typ = typeforfloat(bitwidth)
    vals = memalign_clear(typ, n)

    n_exponent_cycles = n_fractions = 2^(precision - 1) # 2^fraction_bits
    n_exponents = n_fraction_cycles = div(n_values, n_fractions)
    map(T, significand_series(n_fractions, n_fraction_cycles) .* exponent_series(n_exponents, n_exponent_cycles))
    vals[:] = collect(map(typ, 0:(n-1)))
    vals
end



function valuation(bitwidth, precision) # provide simple value sequence
    T = typeforfloat(bitwidth)
    n_values = 2^bitwidth
    n_exponent_cycles = n_fractions = 2^(precision - 1) # 2^fraction_bits
    n_exponents = n_fraction_cycles = div(n_values, n_fractions)
    map(T, significand_series(n_fractions, n_fraction_cycles) .* exponent_series(n_exponents, n_exponent_cycles))
end

function significand_series(n_fractions, n_fraction_cycles)
    fraction_sequence = (0:n_fractions-1) .// n_fractions
    normal_sequence = 1 .+ fraction_sequence
    append!(fraction_sequence, repeat(normal_sequence, n_fraction_cycles - 1))
end

exponent_bias(n_exponent_values::Integer) = n_exponent_values >> 1

function exponent_series(n_exponents, n_exponent_cycles)
    biased_exponents = biasedexponent_series(n_exponents, n_exponent_cycles)
    map(x->2.0^x, biased_exponents)
end

function biasedexponent_series(n_exponents, n_exponent_cycles) 
    bias = exponent_bias(n_exponents)
    biased_exponents = collect( (0:n_exponents-1) .- bias )
    # exponent for subnormals equals the minimum exponent for normals
    biased_exponents[1] = biased_exponents[2]
    collect(Iterators.flatten(map(x->fill(x, n_exponent_cycles), biased_exponents)))
end
