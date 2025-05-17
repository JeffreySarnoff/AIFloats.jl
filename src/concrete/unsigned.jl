struct UnsignedFiniteFloats{bits, sigbits, T, S} <: AbsUnsignedFiniteFloat{bits, sigbits}
    floats::Vector{T} # memory for the floats
    codes::Vector{S} # memory for the codes
end

floats(x::UnsignedFiniteFloats) = x.floats
codes(x::UnsignedFiniteFloats) = x.codes

struct UnsignedExtendedFloats{bits, sigbits, T, S} <: AbsUnsignedExtendedFloat{bits, sigbits}
    floats::Vector{T} # memory for the floats
    codes::Vector{S} # memory for the codes
end

floats(x::UnsignedExtendedFloats) = x.floats
codes(x::UnsignedExtendedFloats) = x.codes

function UnsignedFiniteFloats(T::Type{<:AbsUnsignedFloat})
    bits = nBits(T)
    sigbits = nSigBits(T)
    UnsignedFiniteFloats(bits, sigbits)
end

function UnsignedFiniteFloats(bits, sigbits)
   T = typeforfloat(bits)
   S = typeforcode(bits)
   codes = encoding_sequence(S, bits)
   floats = foundation_magnitudes(AbsUnsignedFiniteFloat{bits, sigbits})
   floats[end] = eltype(floats)(NaN)
   UnsignedFiniteFloats{bits, sigbits, T, S}(floats, codes)
end

function UnsignedExtendedFloats(T::Type{<:AbsUnsignedFloat})
    bits = nBits(T)
    sigbits = nSigBits(T)
    UnsignedExtendedFloats(bits, sigbits)
end

function UnsignedExtendedFloats(bits, sigbits)
   T = typeforfloat(bits)
   S = typeforcode(bits)
   codes = encoding_sequence(S, bits)
   floats = foundation_magnitudes(AbsUnsignedFiniteFloat{bits, sigbits})
   floats[end-1] = eltype(floats)(Inf)
   floats[end] = eltype(floats)(NaN)
   UnsignedExtendedFloats{bits, sigbits, T, S}(floats, codes)
end

