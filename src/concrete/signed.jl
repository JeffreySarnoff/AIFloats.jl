struct SignedFiniteFloats{bits, sigbits, T, S} <: AbsSignedFiniteFloat{bits, sigbits}
    floats::Vector{T} # memory for the floats
    codes::Vector{S} # memory for the codes
end

floats(x::SignedFiniteFloats) = x.floats
codes(x::SignedFiniteFloats) = x.codes

struct SignedExtendedFloats{bits, sigbits, T, S} <: AbsSignedExtendedFloat{bits, sigbits}
    floats::Vector{T} # memory for the floats
    codes::Vector{S} # memory for the codes
end

floats(x::SignedExtendedFloats) = x.floats
codes(x::SignedExtendedFloats) = x.codes

function SignedFiniteFloats(T::Type{<:AbsSignedFloat})
    bits = nBits(T)
    sigbits = nSigBits(T)
    SignedFiniteFloats(bits, sigbits)
end

function SignedFiniteFloats(bits, sigbits)
    T = typeforfloat(bits)
    S = typeforcode(bits)
    codes = encoding_sequence(S, bits)
    magnitudes = foundation_magnitudes(AbsSignedFiniteFloat{bits, sigbits})
    negmagnitudes = -1 .* magnitudes
    negmagnitudes[1] = convert(T, NaN)
    append!(magnitudes, negmagnitudes)
    floats = memalign_clear(T, length(magnitudes))
    floats[:] = magnitudes
    SignedFiniteFloats{bits, sigbits, T, S}(floats, codes)
end

function SignedExtendedFloats(T::Type{<:AbsSignedFloat})
    bits = nBits(T)
    sigbits = nSigBits(T)
    SignedExtendedFloats(bits, sigbits)
end

function SignedExtendedFloats(bits, sigbits)
    T = typeforfloat(bits)
    S = typeforcode(bits)
    codes = encoding_sequence(S, bits)
    magnitudes = foundation_magnitudes(AbsSignedFiniteFloat{bits, sigbits})
    magnitudes[end] = convert(T, Inf) # replace last value with NaN
    negmagnitudes = -1 .* magnitudes
    negmagnitudes[1] = convert(T, NaN)
    append!(magnitudes, negmagnitudes)
    floats = memalign_clear(T, length(magnitudes))
    floats[:] = magnitudes
    SignedExtendedFloats{bits, sigbits, T, S}(floats, codes)
end

