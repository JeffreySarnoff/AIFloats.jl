function encodings(bits)
    n = 2^bits
    typ = typeforcode(bits)
    codes = memalign_clear(typ, n)
    codes[:] = collect(map(typ, 0:(n-1)))
    codes
end

function foundation_floats(bits::Integer, sigbits::Integer)
    sigs = foundation_sigs(bits, sigbits)
    exps = foundation_exps(bits, sigbits)
    seq = exps .* sigs
    seq
end

function foundation_sigs(bits, sigbits)
    foundation_sigs_seq(nFracMagnitudes(bits, sigbits), nFracCycles(bits, sigbits, IsUnsigned))
end

function foundation_sigs_seq(n_fractions, n_fraction_cycles)
    fraction_sequence = (0:n_fractions-1) .// n_fractions
    normal_sequence = 1 .+ fraction_sequence
    append!(fraction_sequence, repeat(normal_sequence, n_fraction_cycles - 1))
end

function foundation_exps(bits, sigbits)
   foundation_exps_seq(nExpBits(bits, sigbits, false), nExpCycles(bits, sigbits))
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
