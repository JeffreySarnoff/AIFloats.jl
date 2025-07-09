struct UnsignedFinite{bits, sigbits, T<:AbstractFloat, S<:Unsigned} <: AkoUnsignedFinite{bits, sigbits}
    floats::Vector{T} # memory for the floats
    codes::Vector{S} # memory for the codes
end

floats(x::UnsignedFinite) = x.floats
codes(x::UnsignedFinite) = x.codes

struct UnsignedExtended{bits, sigbits, T<:AbstractFloat, S<:Unsigned} <: AkoUnsignedExtended{bits, sigbits}
    floats::Vector{T} # memory for the floats
    codes::Vector{S} # memory for the codes
end

floats(x::UnsignedExtended) = x.floats
codes(x::UnsignedExtended) = x.codes

function UnsignedFinite(T::Type{<:AbstractUnsigned})
    bits = nBits(T)
    sigbits = nSigBits(T)
    UnsignedFinite(bits, sigbits)
end

# use types to eliminate an ambiguity
function UnsignedFinite(bits::Int, sigbits::Int)
   T = typeforfloat(bits)
   S = typeforcode(bits)
   codes = encoding_sequence(S, bits)
   floats = value_sequence(AkoUnsignedFinite{bits, sigbits})
   UnsignedFinite{bits, sigbits, T, S}(floats, codes)
end

function value_sequence(T::Type{<:AkoUnsignedFinite})
   bits = nBits(T)
   sigbits = nSigBits(T)
   F = typeforfloat(bits)
   floats = foundation_magnitudes(AkoUnsignedFinite{bits, sigbits})
   floats[end] = (F)(NaN)
   floats
end
  
function UnsignedExtended(T::Type{<:AbstractUnsigned})
    bits = nBits(T)
    sigbits = nSigBits(T)
    UnsignedExtended(bits, sigbits)
end

# use types to eliminate an ambiguity
function UnsignedExtended(bits::Int, sigbits::Int)
   T = typeforfloat(bits)
   S = typeforcode(bits)
   codes = encoding_sequence(S, bits)
   floats = value_sequence(AkoUnsignedExtended{bits, sigbits})
   UnsignedExtended{bits, sigbits, T, S}(floats, codes)
end

function value_sequence(T::Type{<:AkoUnsignedExtended})
   bits = nBits(T)
   sigbits = nSigBits(T)
   F = typeforfloat(bits)
   floats = foundation_magnitudes(AkoUnsignedExtended{bits, sigbits})
   floats[end-1] = eltype(floats)(Inf)
   floats[end] = eltype(floats)(NaN)
   floats
end
