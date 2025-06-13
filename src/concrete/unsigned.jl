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
   floats = value_sequence(AbsUnsignedFiniteFloat{bits, sigbits})
   UnsignedFiniteFloats{bits, sigbits, T, S}(floats, codes)
end

function value_sequence(T::Type{<:AbsUnsignedFiniteFloat})
   bits = nBits(T)
   sigbits = nSigBits(T)
   F = typeforfloat(bits)
   floats = foundation_magnitudes(AbsUnsignedFiniteFloat{bits, sigbits})
   floats[end] = (F)(NaN)
   floats
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
   floats = value_sequence(AbsUnsignedExtendedFloat{bits, sigbits})
   UnsignedExtendedFloats{bits, sigbits, T, S}(floats, codes)
end

function value_sequence(T::Type{<:AbsUnsignedExtendedFloat})
   bits = nBits(T)
   sigbits = nSigBits(T)
   F = typeforfloat(bits)
   floats = foundation_magnitudes(AbsUnsignedExtendedFloat{bits, sigbits})
   floats[end-1] = eltype(floats)(Inf)
   floats[end] = eltype(floats)(NaN)
   floats
end
