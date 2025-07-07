struct SignedFinite{bits, sigbits, T<:AbstractFloat, S<:Unsigned} <: AbstractSignedFinite{bits, sigbits}
    floats::Vector{T} # memory for the floats
    codes::Vector{S} # memory for the codes
end

floats(x::SignedFinite) = x.floats
codes(x::SignedFinite) = x.codes

struct SignedExtended{bits, sigbits, T<:AbstractFloat, S<:Unsigned} <: AbstractSignedExtended{bits, sigbits}
    floats::Vector{T} # memory for the floats
    codes::Vector{S} # memory for the codes
end

floats(x::SignedExtended) = x.floats
codes(x::SignedExtended) = x.codes

function SignedFinite(T::Type{<:AbstractSigned})
    bits = nBits(T)
    sigbits = nSigBits(T)
    SignedFinite(bits, sigbits)
end

# use types to eliminate an ambiguity
function SignedFinite(bits::Int, sigbits::Int)
    T = typeforfloat(bits)
    S = typeforcode(bits)
    codes = encoding_sequence(S, bits)
    floats = value_sequence(AbstractSignedFinite{bits, sigbits})
    SignedFinite{bits, sigbits, T, S}(floats, codes)
end

function value_sequence(T::Type{<:AbstractSignedFinite})
    bits = nBits(T)
    sigbits = nSigBits(T)
    F = typeforfloat(bits)
    nonnegmagnitudes = foundation_magnitudes(AbstractSignedFinite{bits, sigbits})
    negmagnitudes = -1 .* nonnegmagnitudes
    negmagnitudes[1] = convert(F, NaN)
    magnitudes = vcat(nonnegmagnitudes, negmagnitudes)
    floats = memalign_clear(F, length(magnitudes))
    floats[:] = magnitudes
    floats
end

function SignedExtended(T::Type{<:AbstractSigned})
    bits = nBits(T)
    sigbits = nSigBits(T)
    SignedExtended(bits, sigbits)
end

# use types to eliminate an ambiguity
function SignedExtended(bits::Int, sigbits::Int)
    T = typeforfloat(bits)
    S = typeforcode(bits)
    codes = encoding_sequence(S, bits)
    floats = value_sequence(AbstractSignedExtended{bits, sigbits})
    SignedExtended{bits, sigbits, T, S}(floats, codes)
end

function value_sequence(T::Type{<:AbstractSignedExtended})
    bits = nBits(T)
    sigbits = nSigBits(T)
    F = typeforfloat(bits)
    
    nonnegmagnitudes = foundation_magnitudes(AbstractSignedExtended{bits, sigbits})
    nonnegmagnitudes[end] = convert(F, Inf)  # last value is Inf
    negmagnitudes = -1 .* nonnegmagnitudes
    negmagnitudes[1] = convert(F, NaN)
    magnitudes = vcat(nonnegmagnitudes, negmagnitudes)

    floats = memalign_clear(F, length(magnitudes))
    floats[:] = magnitudes
    floats
end
