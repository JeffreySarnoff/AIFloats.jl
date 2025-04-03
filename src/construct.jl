encoding(cfg::FloatMLconfig) = encoding(cfg.bits)
valuation(cfg::FloatMLconfig) = valuation(cfg.bits, cfg.precision, 
                                          cfg.n_fraction_magnitudes, cfg.n_fraction_cycles,
                                          cfg.n_exponent_magnitudes, cfg.n_exponent_cycles)

function encoding(bits)
    n = 2^bits
    typ = typeforcode(bits)
    codes = memalign_clear(typ, n)
    codes[:] = collect(map(typ, 0:(n-1)))
    codes
end

function valuation(bits, precision, n_fractions, n_fraction_cycles, n_exponents, n_exponent_cycles)
    n = 2^bits
    typ = typeforfloat(bits)
    vals = memalign_clear(typ, n)

    n_exponents = n_fraction_cycles = div(n_values, n_fractions)
    map(T, significand_series(n_fractions, n_fraction_cycles) .* exponent_series(n_exponents, n_exponent_cycles))
    vals[:] = collect(map(typ, 0:(n-1)))
    vals
end



function valuation(bits, precision) # provide simple value sequence
    T = typeforfloat(bits)
    n_values = 2^bits
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
    unbiased_exponents = unbiasedexponent_series(n_exponents, n_exponent_cycles)
    map(x->2.0^x, unbiased_exponents)
end

function unbiasedexponent_series(n_exponents, n_exponent_cycles) 
    bias = exponent_bias(n_exponents)
    unbiased_exponents = collect( (0:n_exponents-1) .- bias )
    # exponent for subnormals equals the minimum exponent for normals
    unbiased_exponents[1] = unbiased_exponents[2]
    collect(Iterators.flatten(map(x->fill(x, n_exponent_cycles), unbiased_exponents)))
end
