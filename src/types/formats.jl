"""
    Binary{K,P,S,D}

A 3109 complete binary format specifier.

- K is BitwidthOf(format)
- P is PrecisionOf(format)
- S is SignednessOf(format)
- D is DomainOf(format)
"""
struct Binary{K,P,S,D} end

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

"""
    format_fields

provide internal canonical forms for the field values
"""
function format_fields(K::I, P::I, S::Union{Signedness,Bool}, D::Union{Domain,Bool}) where {I<:Integer}
    bitwidth = Int8(K)
    bitprecision = Int8(P)
    signedness = convert(Bool, S)
    domain = convert(Bool, D)
    (bitwidth, bitprecision, signedness, domain)
end

function format(K::I, P::I, S::Union{Signedness,Bool}, D::Union{Domain,Bool}) where {I<:Integer}
    Format(format_fields(K, P, S, D)...)
end

function FormatOf(B::Binary{K,P,S,D}) where {K,P,S,D}
    Format(Int8(K), Int8(P), Bool(S), Bool(D))
end

function binary(K::I, P::I, S::Union{Signedness,Bool}, D::Union{Domain,Bool}) where {I<:Integer}
    Binary{K, P, convert(Bool, S), convert(Bool, D)}()
end

function Binary(K::I, P::I, S::Union{Signedness,Bool}, D::Union{Domain,Bool}) where {I<:Integer}
    Binary{K, P, convert(Bool, S), convert(Bool, D)}()
end

BinaryOf(format::Format) =
    Binary{Int(format.K), Int(format.P), format.S, format.D}()

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

function Base.show(io::IO, ::MIME"text/plain", f::Format)
    print(io, "Format(", f.K, ", ", f.P, ", ", f.S, ", ", f.D, ")")
end

is_unsigned(format::Format) = format.S === false
is_signed(format::Format) = format.S === true
is_finite(format::Format) = format.D === false
is_extended(format::Format) = format.D === true

is_unsigned(b::Binary{K,P,S,D}) where {K,P,S,D} = S === false
is_signed(b::Binary{K,P,S,D}) where {K,P,S,D} = S === true
is_finite(b::Binary{K,P,S,D}) where {K,P,S,D} = D === false
is_extended(b::Binary{K,P,S,D}) where {K,P,S,D} = D === true
