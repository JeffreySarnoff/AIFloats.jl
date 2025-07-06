struct SignedFiniteFloat{bits, sigbits, T<:AbstractFloat, S<:Unsigned} <: AbstractSignedFinite{bits, sigbits}
    floats::Vector{T} # memory for the floats
    codes::Vector{S} # memory for the codes
end

floats(x::SignedFiniteFloat) = x.floats
codes(x::SignedFiniteFloat) = x.codes

struct SignedExtendedFloat{bits, sigbits, T<:AbstractFloat, S<:Unsigned} <: AbstractSignedExtended{bits, sigbits}
    floats::Vector{T} # memory for the floats
    codes::Vector{S} # memory for the codes
end

floats(x::SignedExtendedFloat) = x.floats
codes(x::SignedExtendedFloat) = x.codes

function SignedFiniteFloat(T::Type{<:AbstractSignedFloat})
    bits = nBits(T)
    sigbits = nSigBits(T)
    SignedFiniteFloat(bits, sigbits)
end

# use types to eliminate an ambiguity
function SignedFiniteFloat(bits::Int, sigbits::Int)
    T = typeforfloat(bits)
    S = typeforcode(bits)
    codes = encoding_sequence(S, bits)
    floats = value_sequence(AbstractSignedFinite{bits, sigbits})
    SignedFiniteFloat{bits, sigbits, T, S}(floats, codes)
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

function SignedExtendedFloat(T::Type{<:AbstractSignedFloat})
    bits = nBits(T)
    sigbits = nSigBits(T)
    SignedExtendedFloat(bits, sigbits)
end

# use types to eliminate an ambiguity
function SignedExtendedFloat(bits::Int, sigbits::Int)
    T = typeforfloat(bits)
    S = typeforcode(bits)
    codes = encoding_sequence(S, bits)
    floats = value_sequence(AbstractSignedExtended{bits, sigbits})
    SignedExtendedFloat{bits, sigbits, T, S}(floats, codes)
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
