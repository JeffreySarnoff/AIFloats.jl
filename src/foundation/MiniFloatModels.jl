
# foundation sequence

function foundation_float_seq(n_bits, n_sigbits, isSigned)
    half = (1 << (n_bits-1))
    sigs = foundation_sigs(n_bits, n_sigbits)[1:end>>isSigned]
    exps = foundation_exps(n_bits, n_sigbits, isSigned)
    seq = exps .* sigs
    if (n_bits <= 7) || (n_bits == 8 && n_sigbits > 1)
        seq = map(Float32, seq)
    end
    seq
end

function foundation_sigs(n_bits, n_sigbits)
    foundation_sigs_seq(nFracValues(n_bits, n_sigbits), nFracCycles(n_bits, n_sigbits, false))
end

function foundation_sigs_seq(n_fractions, n_fraction_cycles)
    fraction_sequence = (0:n_fractions-1) .// n_fractions
    normal_sequence = 1 .+ fraction_sequence
    append!(fraction_sequence, repeat(normal_sequence, n_fraction_cycles - 1))
end


function foundation_exps(n_bits, n_sigbits, isSigned)
   foundation_exps_seq(nExpBits(n_bits, n_sigbits, isSigned), nExpCycles(n_bits, n_sigbits))
end

@inline function foundation_exps_seq(n_expbits, n_exponent_cycles)
    twopow = n_expbits - 1
    bias = twopow >= 0 ? 2^twopow : 1/2^abs(twopow)
    n_exponents = 2^n_expbits

    biased_exponents = collect( (0:n_exponents-1) .- bias )
    # exponent for subnormals equals the minimum exponent for normals
    if length(biased_exponents) > 1
        biased_exponents[1] = biased_exponents[2]
    end
    biased = collect(Iterators.flatten(map(x->fill(x, n_exponent_cycles), biased_exponents)))
    map(x->2.0^x, biased)
end

