struct UnsignedFiniteFloat{bits, sigbits, T, S} <: AbsUnsignedFiniteFloat{bits, sigbits}
    floats::Vector{T} # memory for the floats
    codes::Vector{S} # memory for the codes
end

floats(x::UnsignedFiniteFloat) = x.floats
codes(x::UnsignedFiniteFloat) = x.codes

struct UnsignedExtendedFloat{bits, sigbits, T, S} <: AbsUnsignedExtendedFloat{bits, sigbits}
    floats::Vector{T} # memory for the floats
    codes::Vector{S} # memory for the codes
end

floats(x::UnsignedExtendedFloat) = x.floats
codes(x::UnsignedExtendedFloat) = x.codes

function UnsignedFiniteFloat(T::Type{<:AbsUnsignedFloat})
    bits = nBits(T)
    sigbits = nSigBits(T)
    UnsignedFiniteFloat(bits, sigbits)
end

# use types to eliminate an ambiguity
function UnsignedFiniteFloat(bits:Int, sigbits::Int)
   T = typeforfloat(bits)
   S = typeforcode(bits)
   codes = encoding_sequence(S, bits)
   floats = value_sequence(AbsUnsignedFiniteFloat{bits, sigbits})
   UnsignedFiniteFloat{bits, sigbits, T, S}(floats, codes)
end

function value_sequence(T::Type{<:AbsUnsignedFiniteFloat})
   bits = nBits(T)
   sigbits = nSigBits(T)
   F = typeforfloat(bits)
   floats = foundation_magnitudes(AbsUnsignedFiniteFloat{bits, sigbits})
   floats[end] = (F)(NaN)
   floats
end
  
function UnsignedExtendedFloat(T::Type{<:AbsUnsignedFloat})
    bits = nBits(T)
    sigbits = nSigBits(T)
    UnsignedExtendedFloat(bits, sigbits)
end

# use types to eliminate an ambiguity
function UnsignedExtendedFloat(bits:Int, sigbits::Int)
   T = typeforfloat(bits)
   S = typeforcode(bits)
   codes = encoding_sequence(S, bits)
   floats = value_sequence(AbsUnsignedExtendedFloat{bits, sigbits})
   UnsignedExtendedFloat{bits, sigbits, T, S}(floats, codes)
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
