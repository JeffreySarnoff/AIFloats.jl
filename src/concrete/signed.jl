struct SignedFinite{bits, sigbits, T<:AbstractFP, S<:Unsigned} <: AkoSignedFinite{bits, sigbits}
    floats::Vector{T} # memory for the floats
    codes::Vector{S} # memory for the codes
end

floats(x::SignedFinite) = x.floats
codes(x::SignedFinite) = x.codes

struct SignedExtended{bits, sigbits, T<:AbstractFP, S<:Unsigned} <: AkoSignedExtended{bits, sigbits}
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
    codes = encoding_seq(S, bits)
    floats = value_seq(AkoSignedFinite{bits, sigbits})
    SignedFinite{bits, sigbits, T, S}(floats, codes)
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
    codes = encoding_seq(S, bits)
    floats = value_seq(AkoSignedExtended{bits, sigbits})
    SignedExtended{bits, sigbits, T, S}(floats, codes)
end

function value_seq(T::Type{<:AkoSignedFinite})
   bits = nbits(T)
   sigbits = nbits_sig(T)
   F = typeforfloat(bits)
   values = magnitude_foundation_seq(AkoSignedFinite{bits, sigbits})
   values[end] = (F)(NaN)
   values
end

function value_seq(T::Type{<:AkoSignedExtended})
   bits = nbits(T)
   sigbits = nbits_sig(T)
   F = typeforfloat(bits)
   values = magnitude_foundation_seq(AkoSignedExtended{bits, sigbits})
   values[end-1] = eltype(floats)(Inf)
   values[end] = eltype(floats)(NaN)
   values
end

