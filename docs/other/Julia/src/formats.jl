# Source: lib/format-core.maude, lib/format-queries.maude, lib/format-names.maude.
@enum Signedness UNSIGNED SIGNED
@enum Domain FINITE EXTENDED
abstract type Format end

"""BinaryFormat(k, p, signedness, domain): a validated P3109 binary format."""
struct BinaryFormat <: Format
    width::BigInt
    precision::BigInt
    signedness::Signedness
    domain::Domain
    function BinaryFormat(k::Integer, p::Integer, s::Signedness, d::Domain)
        valid_format(k, p, s, d) || throw(ArgumentError("invalid binary format"))
        new(big(k), big(p), s, d)
    end
end
valid_format(k::Integer, p::Integer, s::Signedness, ::Domain) =
    k > 2 && p > 0 && (s == SIGNED ? p < k : p <= k)
valid_format(::Format) = true
struct ExternalFormat <: Format
    name::Symbol
    width::Int
    precision::Int
    bias::Int
end
const BINARY64 = ExternalFormat(:binary64, 64, 53, 1023)
const BINARY32 = ExternalFormat(:binary32, 32, 24, 127)
const BINARY16 = ExternalFormat(:binary16, 16, 11, 15)
const BFLOAT16 = ExternalFormat(:BFloat16, 16, 8, 127)
Base.:(==)(f::BinaryFormat, g::BinaryFormat) =
    (f.width, f.precision, f.signedness, f.domain) == (g.width, g.precision, g.signedness, g.domain)
Base.isequal(f::BinaryFormat, g::BinaryFormat) = f == g
Base.hash(f::BinaryFormat, h::UInt) = hash((f.width, f.precision, f.signedness, f.domain), h)
bitwidth(f::Format) = f.width
precision_bits(f::Format) = f.precision
signedness(f::BinaryFormat) = f.signedness
signedness(::ExternalFormat) = SIGNED
domain(f::BinaryFormat) = f.domain
domain(::ExternalFormat) = EXTENDED
exponent_bias(f::BinaryFormat) =
    big(1) << (bitwidth(f) - precision_bits(f) - (signedness(f) == SIGNED))
exponent_bias(f::ExternalFormat) = big(f.bias)
exponent_bits(f::Format) = bitwidth(f) - precision_bits(f) + (signedness(f) == UNSIGNED)
trailing_bits(f::Format) = precision_bits(f) - 1
internal_format(f::Format) = f isa BinaryFormat
valid_code(f::Format, c::Integer) = 0 <= c < big(1) << bitwidth(f)
function checked_code(f::Format, c::Integer)
    valid_code(f, c) || throw(DomainError(c, "code outside format"))
    return big(c)
end
nan_code(f::BinaryFormat) =
    signedness(f) == SIGNED ? big(1) << (bitwidth(f)-1) : (big(1) << bitwidth(f))-1
positive_limit(f::BinaryFormat) = nan_code(f)-1
max_finite_code(f::BinaryFormat) = positive_limit(f) - (domain(f) == EXTENDED)
min_finite_code(f::BinaryFormat) = signedness(f) == SIGNED ? max_finite_code(f)+nan_code(f) : big(0)
min_positive_code(::BinaryFormat) = big(1)
max_subnormal_code(f::BinaryFormat) =
    precision_bits(f) == 1 ? nan_code(f) : (big(1) << trailing_bits(f))-1
min_normal_code(f::BinaryFormat) = big(1) << trailing_bits(f)
format_name(f::BinaryFormat) =
    "Binary$(bitwidth(f))p$(precision_bits(f))" *
    (signedness(f) == SIGNED ? "s" : "u") *
    (domain(f) == FINITE ? "f" : "e")
format_name(f::ExternalFormat) = String(f.name)
