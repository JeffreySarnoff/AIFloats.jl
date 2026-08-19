abstract type BinaryFloat <: AbstractFloat end

"""
    Binary{K,P,S,D}

A 3109 complete binary format specifier.

- K is BitwidthOf(format)
- P is PrecisionOf(format)
- S is SignednessOf(format)
- D is DomainOf(format)
"""
struct Binary{K,P,S,D} <: BinaryFloat end

function Binary(K::I, P::I, S::ΣBool, D::ΔBool) where {I<:Integer}
    fields = resolve_fields(K, P, S, D)
    Binary{fields...}
end


"""
    resolve_fields

provide internal canonical forms for the field values
"""
function resolve_fields(K::I, P::I, S::ΣBool, D::ΔBool) where {I<:Integer}
    bitwidth = Int8(K)
    bitprecision = Int8(P)
    signedness = convert(Bool, S)
    domain = convert(Bool, D)
    validformat(bitwidth, bitprecision, signedness, domain)
    (bitwidth, bitprecision, signedness, domain)
end


is_unsigned(b::Binary{K,P,S,D}) where {K,P,S,D} = S === false
is_signed(b::Binary{K,P,S,D}) where {K,P,S,D} = S === true

is_finite(b::Binary{K,P,S,D}) where {K,P,S,D} = D === false
is_extended(b::Binary{K,P,S,D}) where {K,P,S,D} = D === true

# validation of binary specifiers
validformat(K::I, P::I, S::Union{Signedness,Bool}, D::Union{Domain,Bool}) where {I<:Integer} =
     ((K > 2) && (P > 0) && (P <= K - convert(Bool, S)) && (S isa Signedness || S isa Bool) && (D isa Domain || D isa Bool)) ? nothing : throw(ArgumentError("Invalid format: K=$K, P=$P, S=$S, D=$D"))

validformat(b::Binary{K,P,S,D}) where {K,P,S,D} = validformat(K, P, S, D)  

# format-level accessors
BitwidthOf(::Type{Binary{K,P,S,D}}) where {K,P,S,D} = K
PrecisionOf(::Type{Binary{K,P,S,D}}) where {K,P,S,D} = P
SignednessOf(::Type{Binary{K,P,S,D}}) where {K,P,S,D} = S
DomainOf(::Type{Binary{K,P,S,D}}) where {K,P,S,D} = D

BitwidthOf(::Binary{K,P,S,D}) where {K,P,S,D} = K
PrecisionOf(::Binary{K,P,S,D}) where {K,P,S,D} = P
SignednessOf(::Binary{K,P,S,D}) where {K,P,S,D} = S
DomainOf(::Binary{K,P,S,D}) where {K,P,S,D} = D

TrailingSignificantBitsOf(::Type{Binary{K,P,S,D}}) where {K,P,S,D} = P - one(IntParam)

function Base.show(io::IO, ::MIME"text/plain", b::Binary{K,P,S,D}) where {K,P,S,D}
    print(io, "Binary{", K, ", ", P, ", ", S, ", ", D, "}")
end

function Base.show(io::IO, b::Binary{K,P,S,D}) where {K,P,S,D}
    s = string("Binary{", K, ", ", P, ", ", S, ", ", D, "}")
    print(io, s)
end
