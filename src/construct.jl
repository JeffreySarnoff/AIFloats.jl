function encoding(bitwidth, sigbits) # provide encoding sequence
    T = bitwidth <= 8 ? UInt8 : UInt16
    n_values = 2^bitwidth
    v = Vector{T}(undef, n_values)
    v .= T(0):T(n_values-1) # the value of the last line in a function is returned
end

function Base.values(bitwidth, sigbits) # provide simple value sequence
    T = bitwidth <= 8 ? Float32 : Float64
    n_values = 2^bitwidth
    n_exponent_cycles = n_fractions = 2^(sigbits - 1) # 2^fraction_bits
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
