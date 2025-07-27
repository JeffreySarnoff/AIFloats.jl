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
    bits = n_bits(T)
    sigbits = n_sig_bits(T)
    SignedFinite(bits, sigbits)
end

# use types to eliminate an ambiguity
function SignedFinite(bits::Int, sigbits::Int)
    T = typeforfloat(bits)
    S = typeforcode(bits)
    codes = encoding_seq(S, bits)
    values = value_seq(AkoSignedFinite{bits, sigbits})
    SignedFinite{bits, sigbits, T, S}(values, codes)
end

function SignedExtended(T::Type{<:AbstractSigned})
    bits = n_bits(T)
    sigbits = n_sig_bits(T)
    SignedExtended(bits, sigbits)
end

# use types to eliminate an ambiguity
function SignedExtended(bits::Int, sigbits::Int)
    T = typeforfloat(bits)
    S = typeforcode(bits)
    codes = encoding_seq(S, bits)
    values = value_seq(AkoSignedExtended{bits, sigbits})
    SignedExtended{bits, sigbits, T, S}(values, codes)
end

function value_seq(T::Type{<:AkoSignedFinite})
   bits = n_bits(T)
   sigbits = n_sig_bits(T)
   F = typeforfloat(bits)
   values = mag_foundation_seq(AkoSignedFinite{bits, sigbits})
   negvalues = map(-, values)
   negvalues[1] = (F)(NaN)
   append!(values, negvalues) 
   values
end

function value_seq(T::Type{<:AkoSignedExtended})
   bits = n_bits(T)
   sigbits = n_sig_bits(T)
   F = typeforfloat(bits)
   values = mag_foundation_seq(AkoSignedExtended{bits, sigbits})
   values[end] = eltype(values)(Inf)
   negvalues = map(-, values)
   negvalues[1] = (F)(NaN)
   append!(values, negvalues)
   values
end

