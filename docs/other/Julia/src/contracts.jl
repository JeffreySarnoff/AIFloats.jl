# Source: external-signature and contracts/*.maude. No concrete view is assumed.
module Contracts
using ..P3109Reference: residual
public ExternalBackend,
    RealBackend,
    backend_format,
    backend_decode,
    backend_encode,
    backend_datum,
    backend_valid_code,
    backend_canonical,
    backend_quiet_nan,
    backend_positive_zero,
    backend_bound,
    backend_finite_count,
    real_zero,
    real_one,
    add_real,
    multiply_real,
    negate_real,
    inverse_real,
    less_real
abstract type ExternalBackend end
abstract type RealBackend end
backend_format(b::ExternalBackend) = residual(:backendFormat, b; reason = :missing_backend)
backend_decode(b::ExternalBackend, c) = residual(:backendDecode, b, c; reason = :missing_backend)
backend_encode(b::ExternalBackend, x) = residual(:backendEncode, b, x; reason = :missing_backend)
backend_datum(b::ExternalBackend, x) = residual(:backendDatum, b, x; reason = :missing_backend)
backend_valid_code(b::ExternalBackend, c) =
    residual(:backendValidCode, b, c; reason = :missing_backend)
backend_canonical(b::ExternalBackend, c) =
    residual(:backendCanonical, b, c; reason = :missing_backend)
backend_quiet_nan(b::ExternalBackend) = residual(:backendQuietNaN, b; reason = :missing_backend)
backend_positive_zero(b::ExternalBackend) =
    residual(:backendPositiveZero, b; reason = :missing_backend)
backend_bound(b::ExternalBackend, q) = residual(:backendBound, b, q; reason = :missing_backend)
backend_finite_count(b::ExternalBackend) =
    residual(:backendFiniteCount, b; reason = :missing_backend)
real_zero(b::RealBackend) = residual(:realZero, b; reason = :missing_backend)
real_one(b::RealBackend) = residual(:realOne, b; reason = :missing_backend)
add_real(b::RealBackend, x, y) = residual(:addReal, b, x, y; reason = :missing_backend)
multiply_real(b::RealBackend, x, y) = residual(:multiplyReal, b, x, y; reason = :missing_backend)
negate_real(b::RealBackend, x) = residual(:negateReal, b, x; reason = :missing_backend)
inverse_real(b::RealBackend, x) = residual(:inverseReal, b, x; reason = :missing_backend)
less_real(b::RealBackend, x, y) = residual(:lessReal, b, x, y; reason = :missing_backend)
end

decode(f::ExternalFormat, c::Integer) =
    residual(:externalDecode, f, checked_code(f, c); reason = :missing_backend)
encode(f::ExternalFormat, x) = residual(:externalEncode, f, x; reason = :missing_backend)
is_datum(f::ExternalFormat, x) = residual(:externalDatum, f, x; reason = :missing_backend)
project(f::ExternalFormat, p::Projection, x::ExactValue) =
    residual(:project, f, p, x; reason = :missing_backend)
external_bound(f::ExternalFormat, q) = residual(:externalBound, f, q; reason = :missing_backend)
max_finite_code(f::ExternalFormat) = external_bound(f, :maxFiniteQuery)
min_finite_code(f::ExternalFormat) = external_bound(f, :minFiniteQuery)
min_positive_code(f::ExternalFormat) = external_bound(f, :minPositiveQuery)
max_subnormal_code(f::ExternalFormat) = external_bound(f, :maxSubnormalQuery)
min_normal_code(f::ExternalFormat) = external_bound(f, :minNormalQuery)

"""Bind external metadata to an explicitly supplied backend; no backend is installed implicitly."""
struct BoundFormat{B<:Contracts.ExternalBackend} <: Format
    metadata::ExternalFormat
    backend::B
    function BoundFormat(f::ExternalFormat, b::B) where {B<:Contracts.ExternalBackend}
        Contracts.backend_format(b) == f ||
            throw(ArgumentError("backend format does not match metadata"))
        new{B}(f, b)
    end
end
bitwidth(f::BoundFormat) = bitwidth(f.metadata)
precision_bits(f::BoundFormat) = precision_bits(f.metadata)
signedness(f::BoundFormat) = signedness(f.metadata)
domain(f::BoundFormat) = domain(f.metadata)
exponent_bias(f::BoundFormat) = exponent_bias(f.metadata)
format_name(f::BoundFormat) = format_name(f.metadata)
function decode(f::BoundFormat, c::Integer)
    checked_code(f, c)
    ok=Contracts.backend_valid_code(f.backend, c)
    ok === false && throw(DomainError(c, "backend rejected code"))
    ok === true || return residual(:externalDecode, f, c; reason = :missing_backend)
    return Contracts.backend_decode(f.backend, c)
end
is_datum(f::BoundFormat, x) = Contracts.backend_datum(f.backend, x)
function encode(f::BoundFormat, x)
    ok=is_datum(f, x)
    ok === false && throw(DomainError(x, "backend rejected datum"))
    ok === true || return residual(:externalEncode, f, x; reason = :missing_backend)
    return Contracts.backend_encode(f.backend, x)
end
external_bound(f::BoundFormat, q) = Contracts.backend_bound(f.backend, q)
max_finite_code(f::BoundFormat) = external_bound(f, :maxFiniteQuery)
min_finite_code(f::BoundFormat) = external_bound(f, :minFiniteQuery)
min_positive_code(f::BoundFormat) = external_bound(f, :minPositiveQuery)
max_subnormal_code(f::BoundFormat) = external_bound(f, :maxSubnormalQuery)
min_normal_code(f::BoundFormat) = external_bound(f, :minNormalQuery)
function project(f::BoundFormat, p::Projection, x::ExactValue)
    x === NAN && return encode(f, x)
    low_code, high_code=min_finite_code(f), max_finite_code(f)
    (low_code isa Residual || high_code isa Residual) &&
        return residual(:project, f, p, x; reason = :missing_backend)
    low, high=decode(f, low_code), decode(f, high_code)
    (low isa FiniteValue && high isa FiniteValue) ||
        return residual(:project, f, p, x; reason = :missing_backend)
    rounded=round_to_precision(precision_bits(f), exponent_bias(f), p.rounding, x)
    return encode(
        f,
        saturate(
            low.value,
            high.value,
            p.saturation,
            p.rounding,
            rounded,
            signedness(f),
            domain(f),
        ),
    )
end
