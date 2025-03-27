function encodings(bits)
    n = 2^bits
    typ = typeforcode(bits)
    codes = memalign_clear(typ, n)
    codes[:] = collect(map(typ, 0:(n-1)))
    codes
end

function magnitude_seq(bits, sigbits)
    significand_seq(bits, sigbits) .* exponent_seq(bits, sigbits)
end

function significand_seq(bits, sigbits)
    significands = []
    push!(significands, fraction_seq(sigbits))
    n_mixed = n_mixed_fractions(bits, sigbits)
    mixed_seq  = mixed_fraction_seq(sigbits)
    for i in 1:n_mixed
        push!(significands, mixed_seq)
    end
    TupleTools.flatten(Tuple(significands))
end

n_fractions(sigbits) = 2^(sigbits - 1)

function fraction_seq(sigbits)
    denom = 2^(sigbits - 1)
    numers = ntuple(i->i-1, denom)
    numers ./ denom
end

n_mixed_fractions(bits, sigbits) = 2^(bits - sigbits) - 1
# n_mixed_fracs(bits, sigbits) = 2^(1 + bits - sigbits) - 1

function mixed_fraction_seq(sigbits)
    1 .+ fraction_seq(sigbits)
end

function exponent_seq(bits, sigbits)
    n_values = 2^bits
    n_fracs = n_fractions(sigbits)
    exponents = []
    emn, emx = exp_mnmx(bits, sigbits)
    # first step is subnormal
    for i in 1:n_fracs
        push!(exponents, 2.0^emn)
    end
    for estep in emn:emx
        expon = 2.0^estep
        for i in 1:n_fracs
            push!(exponents, expon)
        end
    end
    Tuple(exponents)
end

exp_bias(bits, sigbits) = 2^(bits - sigbits - 1) - 1

function exp_mnmx(bits, sigbits)
    bias = exp_bias(bits, sigbits)
    emin = (sigbits > 1) ? -bias : (-bias + 1)
    emax = bias
    (emin, emax)
end

function exp_minmax(bits, sigbits)
    bias = exp_bias(bits, sigbits)
    emin = 2.0^((sigbits > 1) ? -bias : -bias + 1)
    emax = 2.0^bias
    (emin, emax)
end




    n_fraction_cycles = 2^(bits - sigbits + IsUnsigned)
    fraction_sequence = (0:n_fractions-1) .// n_fractions
    normal_sequence = 1 .+ fraction_sequence
    append!(fraction_sequence, repeat(normal_sequence, n_fraction_cycles - 1))
end
function foundation_floats(bits::Integer, sigbits::Integer)
    sigs = foundation_sigs(bits, sigbits)
    exps = foundation_exps(bits, sigbits)
    seq = exps .* sigs
    seq
end

nFracValues(bits, sigbits) = 2^(sigbits - 1)
nFracCycles(bits, sigbits, IsUnsigned) = 2^(bits - sigbits + IsUnsigned)
nExpBits(bits, sigbits, IsSigned) = bits - sigbits + IsSigned
nExpCycles(bits, sigbits) = 2^(bits - sigbits)

function foundation_sigs(bits, sigbits)
    foundation_sigs_seq(nFracValues(bits, sigbits), nFracCycles(bits, sigbits, IsUnsigned))
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
    
    println((; n_exponent_cycles, biased_exponents))

    biased = collect(Iterators.flatten(map(x->fill(x, n_exponent_cycles), biased_exponents)))
    map(x->2.0^x, biased)
end
