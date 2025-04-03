function encoding(bits)
    n = 2^bits
    T = typeforcode(bits)
    codes = memalign_clear(T, n)
    codes[:] = collect(map(T, 0:(n-1)))
    codes
end

magnitude_encoding(bits) = encoding(bits - 1)

# the magnitude portion of the signed Binary<bits>P<sigbits>
# alternatively the unsigned Binary<bits-1>P<sigbits?>
function magnitude_sequence(bits, sigbits)
    T = typeforfloat(bits)
    floats = memalign_clear(T, 2^(bits - 1)) 
    seq = map(T, significand_seq(bits, sigbits) .* exponent_seq(bits, sigbits))
    floats[:] .= seq
    floats
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


nFracValues(bits, sigbits) = 2^(sigbits - 1)
nFracCycles(bits, sigbits, IsUnsigned) = 2^(bits - sigbits + IsUnsigned)
nExpBits(bits, sigbits, IsSigned) = bits - sigbits + IsSigned
nExpCycles(bits, sigbits) = 2^(bits - sigbits)
