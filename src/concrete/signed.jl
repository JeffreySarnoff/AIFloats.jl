struct SignedFinite{bits, sigbits, T<:AbstractFloat, S<:Unsigned} <: AkoSignedFinite{bits, sigbits}
    floats::Vector{T} # memory for the floats
    codes::Vector{S} # memory for the codes
end

floats(x::SignedFinite) = x.floats
codes(x::SignedFinite) = x.codes

struct SignedExtended{bits, sigbits, T<:AbstractFloat, S<:Unsigned} <: AkoSignedExtended{bits, sigbits}
    floats::Vector{T} # memory for the floats
    codes::Vector{S} # memory for the codes
end

floats(x::SignedExtended) = x.floats
codes(x::SignedExtended) = x.codes

function SignedFinite(T::Type{<:AbstractSigned})
    bits = nbits(T)
    sigbits = nbits_sig(T)
    SignedFinite(bits, sigbits)
end

# use types to eliminate an ambiguity
function SignedFinite(bits::Int, sigbits::Int)
    T = typeforfloat(bits)
    S = typeforcode(bits)
    codes = encoding_sequence(S, bits)
    floats = value_sequence(AkoSignedFinite{bits, sigbits})
    SignedFinite{bits, sigbits, T, S}(floats, codes)
end

function value_sequence(T::Type{<:AkoSignedFinite})
    bits = nbits(T)
    sigbits = nbits_sig(T)
    F = typeforfloat(bits)
    nonnegmagnitudes = foundation_magnitudes(AkoSignedFinite{bits, sigbits})
    negmagnitudes = -1 .* nonnegmagnitudes
    negmagnitudes[1] = convert(F, NaN)
    magnitudes = vcat(nonnegmagnitudes, negmagnitudes)
    floats = memalign_clear(F, length(magnitudes))
    floats[:] = magnitudes
    floats
end

function SignedExtended(T::Type{<:AbstractSigned})
    bits = nbits(T)
    sigbits = nbits_sig(T)
    SignedExtended(bits, sigbits)
end

# use types to eliminate an ambiguity
function SignedExtended(bits::Int, sigbits::Int)
    T = typeforfloat(bits)
    S = typeforcode(bits)
    codes = encoding_sequence(S, bits)
    floats = value_sequence(AkoSignedExtended{bits, sigbits})
    SignedExtended{bits, sigbits, T, S}(floats, codes)
end

function value_sequence(T::Type{<:AkoSignedExtended})
    bits = nbits(T)
    sigbits = nbits_sig(T)
    F = typeforfloat(bits)
    
    nonnegmagnitudes = foundation_magnitudes(AkoSignedExtended{bits, sigbits})
    nonnegmagnitudes[end] = convert(F, Inf)  # last value is Inf
    negmagnitudes = -1 .* nonnegmagnitudes
    negmagnitudes[1] = convert(F, NaN)
    magnitudes = vcat(nonnegmagnitudes, negmagnitudes)

    floats = memalign_clear(F, length(magnitudes))
    floats[:] = magnitudes
    floats
end
