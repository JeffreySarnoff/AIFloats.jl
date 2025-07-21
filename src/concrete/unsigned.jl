struct UnsignedFinite{bits, sigbits, T<:AbstractFP, S<:Unsigned} <: AkoUnsignedFinite{bits, sigbits}
    floats::Vector{T} # memory for the floats
    codes::Vector{S} # memory for the codes
end

floats(x::UnsignedFinite) = x.floats
codes(x::UnsignedFinite) = x.codes

struct UnsignedExtended{bits, sigbits, T<:AbstractFP, S<:Unsigned} <: AkoUnsignedExtended{bits, sigbits}
    floats::Vector{T} # memory for the floats
    codes::Vector{S} # memory for the codes
end

floats(x::UnsignedExtended) = x.floats
codes(x::UnsignedExtended) = x.codes

function UnsignedFinite(T::Type{<:AbstractUnsigned})
    bits = nbits(T)
    sigbits = nbits_sig(T)
    UnsignedFinite(bits, sigbits)
end

# use types to eliminate an ambiguity
function UnsignedFinite(bits::Int, sigbits::Int)
   T = typeforfloat(bits)
   S = typeforcode(bits)
   codes = encoding_seq(S, bits)
   values = value_seq(AkoUnsignedFinite{bits, sigbits})
   UnsignedFinite{bits, sigbits, T, S}(values, codes)
end

function value_seq(T::Type{<:AkoUnsignedFinite})
   bits = nbits(T)
   sigbits = nbits_sig(T)
   F = typeforfloat(bits)
   values = mag_foundation_seq(AkoUnsignedFinite{bits, sigbits})
   values[end] = (F)(NaN)
   values
end
  
function UnsignedExtended(T::Type{<:AbstractUnsigned})
    bits = nbits(T)
    sigbits = nbits_sig(T)
    UnsignedExtended(bits, sigbits)
end

# use types to eliminate an ambiguity
function UnsignedExtended(bits::Int, sigbits::Int)
   T = typeforfloat(bits)
   S = typeforcode(bits)
   codes = encoding_seq(S, bits)
   values = value_seq(AkoUnsignedExtended{bits, sigbits})
   UnsignedExtended{bits, sigbits, T, S}(values, codes)
end

function value_seq(T::Type{<:AkoUnsignedExtended})
   bits = nbits(T)
   sigbits = nbits_sig(T)
   F = typeforfloat(bits)
   values = mag_foundation_seq(AkoUnsignedExtended{bits, sigbits})
   values[end-1] = eltype(values)(Inf)
   values[end] = eltype(values)(NaN)
   values
end
