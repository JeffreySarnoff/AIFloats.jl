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
    floats = value_sequence(AbsSignedFiniteFloat{bits, sigbits})
    SignedFiniteFloats{bits, sigbits, T, S}(floats, codes)
end

function value_sequence(T::Type{<:AbsSignedFiniteFloat})
    bits = nBits(T)
    sigbits = nSigBits(T)
    F = typeforfloat(bits)
    nonnegmagnitudes = foundation_magnitudes(AbsSignedFiniteFloat{bits, sigbits})
    negmagnitudes = -1 .* nonnegmagnitudes
    negmagnitudes[1] = convert(F, NaN)
    magnitudes = vcat(nonnegmagnitudes, negmagnitudes)
    floats = memalign_clear(F, length(magnitudes))
    floats[:] = magnitudes
    floats
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
    floats = value_sequence(AbsSignedExtendedFloat{bits, sigbits})
    SignedExtendedFloats{bits, sigbits, T, S}(floats, codes)
end
function value_sequence(T::Type{<:AbsSignedExtendedFloat})
    bits = nBits(T)
    sigbits = nSigBits(T)
    F = typeforfloat(bits)
    
    nonnegmagnitudes = foundation_magnitudes(AbsSignedExtendedFloat{bits, sigbits})
    nonnegmagnitudes[end] = convert(F, Inf)  # last value is Inf
    negmagnitudes = -1 .* nonnegmagnitudes
    negmagnitudes[1] = convert(F, NaN)
    magnitudes = vcat(nonnegmagnitudes, negmagnitudes)

    floats = memalign_clear(F, length(magnitudes))
    floats[:] = magnitudes
    floats
end
