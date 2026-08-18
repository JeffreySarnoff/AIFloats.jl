"""
    Binary{K,P,S,D}

A 3109 complete binary format specifier.

- K is BitwidthOf(format)
- P is PrecisionOf(format)
- S is SignednessOf(format)
- D is DomainOf(format)
"""
struct Binary{K,P,S,D} end

function Binary(K::I, P::I, S::Union{Signedness,Bool}, D::Union{Domain,Bool}) where {I<:Integer}
    fields = resolve_fields(K, P, S, D)
    validformat(fields...)
    Binary{fields...}
end

"""
    Format(K,P,S,D)

A 3109 complete format specifier

- K is BitwidthOf(format)
- P is PrecisionOf(format)
- S is SignenessOf(format)
- D is DomainOf(format)
"""
struct Format
    K::Int8
    P::Int8
    S::Bool
    D::Bool
end

function format(K::I, P::I, S::Union{Signedness,Bool}, D::Union{Domain,Bool}) where {I<:Integer}
    Format(resolve_fields(K, P, S, D)...)
end

"""
    resolve_fields

provide internal canonical forms for the field values
"""
function resolve_fields(K::I, P::I, S::Union{Signedness,Bool}, D::Union{Domain,Bool}) where {I<:Integer}
    bitwidth = Int8(K)
    bitprecision = Int8(P)
    signedness = convert(Bool, S)
    domain = convert(Bool, D)
    validformat(bitwidth, bitprecision, signedness, domain)
    (bitwidth, bitprecision, signedness, domain)
end

function FormatOf(B::Binary{K,P,S,D}) where {K,P,S,D}
    fields = resolve_fields(K, P, S, D)
    Format(fields...)
end

function BinaryOf(format::Format)
    fields = resolve_fields(format.K, format.P, format.S, format.D)
    Binary{fields...}
end

BitwidthOf(::Binary{K,P,S,D}) where {K,P,S,D} = K
PrecisionOf(::Binary{K,P,S,D}) where {K,P,S,D} = P
SignednessOf(::Binary{K,P,S,D}) where {K,P,S,D} = S
DomainOf(::Binary{K,P,S,D}) where {K,P,S,D} = D

BitwidthOf(format::Format) = format.K
PrecisionOf(format::Format) = format.P
SignednessOf(format::Format) = format.S
DomainOf(format::Format) = format.D

function Base.show(io::IO, ::MIME"text/plain", b::Binary{K,P,S,D}) where {K,P,S,D}
    print(io, "Binary{", K, ", ", P, ", ", S, ", ", D, "}")
end

function Base.show(io::IO, b::Binary{K,P,S,D}) where {K,P,S,D}
    s = string("Binary{", K, ", ", P, ", ", S, ", ", D, "}")
    print(io, s)
end

function Base.show(io::IO, ::MIME"text/plain", f::Format)
    print(io, "Format(", f.K, ", ", f.P, ", ", f.S, ", ", f.D, ")")
end

function Base.show(io::IO, f::Format)
    s = string("Format(", f.K, ", ", f.P, ", ", f.S, ", ", f.D, ")")
    print(io, s)
end

is_unsigned(format::Format) = format.S === false
is_signed(format::Format) = format.S === true
is_finite(format::Format) = format.D === false
is_extended(format::Format) = format.D === true

is_unsigned(b::Binary{K,P,S,D}) where {K,P,S,D} = S === false
is_signed(b::Binary{K,P,S,D}) where {K,P,S,D} = S === true
is_finite(b::Binary{K,P,S,D}) where {K,P,S,D} = D === false
is_extended(b::Binary{K,P,S,D}) where {K,P,S,D} = D === true

# validation of format and binary specifiers
validformat(K::I, P::I, S::Union{Signedness,Bool}, D::Union{Domain,Bool}) where {I<:Integer} =
     ((K > 2) && (P > 0) && (P <= K - Bool(S)) && (S isa Signedness || S isa Bool) && (D isa Domain || D isa Bool)) ? nothing : throw(ArgumentError("Invalid format: K=$K, P=$P, S=$S, D=$D"))

validformat(f::Format) = validformat(f.K, f.P, f.S, f.D)
validformat(b::Binary{K,P,S,D}) where {K,P,S,D} = validformat(K, P, S, D)  
