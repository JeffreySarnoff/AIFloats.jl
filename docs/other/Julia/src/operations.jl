# Source: scalar/block templates, block-core, block-ops, predicates and order-next.
"""Apply a decoded kernel and perform one final scalar projection."""
function scalar(kernel, formats::Tuple, result::Format, policy::Projection, codes::Tuple)
    length(formats) == length(codes) || throw(DimensionMismatch("operand formats and codes"))
    values = map(decode, formats, codes)
    any(x -> x isa Residual, values) &&
        return residual(:scalar, kernel, formats, result, policy, codes; reason = :missing_backend)
    return project(result, policy, kernel(values...))
end
struct BlockValue{S,C}
    scale::S
    codes::C
end
Base.:(==)(x::BlockValue, y::BlockValue) = x.scale == y.scale && Tuple(x.codes) == Tuple(y.codes)
function valid_block(n, fs, fx, s, codes)
    return n >= 1 && length(codes) == n && valid_code(fs, s) && all(c -> valid_code(fx, c), codes)
end
function decode_block(n, fs, fx, s, codes)
    valid_block(n, fs, fx, s, codes) || throw(ArgumentError("invalid block"))
    scale = decode(fs, s)
    return map(c -> multiply(scale, decode(fx, c)), collect(codes))
end
function normalize_element(scale, x)
    (is_nan(scale) || is_nan(x)) && return NAN
    (scale isa Residual || x isa Residual) && return residual(:normalizeElement, scale, x)
    is_zero(scale) === true && return finite(0)
    if is_infinite(scale)
        s = value_sign(x)
        return s === UNKNOWN ? residual(:normalizeElement, scale, x) : finite(value_sign(scale)*s)
    end
    return divide(x, scale)
end
function project_elements(fr, p::BlockProjection, values; scale = finite(1))
    valid_block_projection(p, length(values)) || throw(DimensionMismatch("block projection length"))
    policies = if p.mode <= TO_ODD
        Iterators.repeated(Projection(p.mode, p.saturation))
    else
        (Projection(RoundPolicy(p.mode, p.bits, r), p.saturation) for r in p.randoms)
    end
    return [
        project(fr, policy, normalize_element(scale, x)) for (x, policy) in zip(values, policies)
    ]
end
"""Apply a kernel positionally to blocks, retaining the supplied result scale."""
function block_apply(kernel, n, formats::Tuple, fs, fr, p::BlockProjection, inputs::Tuple, s)
    length(formats) == length(inputs) || throw(DimensionMismatch("block operands"))
    checked_code(fs, s)
    valid_block_projection(p, n) || throw(DimensionMismatch("block random sequence"))
    values = map((f, x) -> decode_block(n, f[1], f[2], x[1], x[2]), formats, inputs)
    outputs = [kernel(args...) for args in zip(values...)]
    return BlockValue(s, project_elements(fr, p, outputs; scale = decode(fs, s)))
end
"""Apply a scaled operation with exact scale multiplication and final projection."""
function scaled(kernel, formats::Tuple, fr, p::Projection, inputs::Tuple)
    values = map((f, x) -> multiply(decode(f[1], x[1]), decode(f[2], x[2])), formats, inputs)
    return project(fr, p, kernel(values...))
end
convert_from_block(n, fs, fx, fr, p, s, codes) =
    project_elements(fr, p, decode_block(n, fs, fx, s, codes))
function convert_to_block(n, fx, fs, fr, p, codes, s)
    n >= 1 && length(codes) == n || throw(DimensionMismatch("block length"))
    return project_elements(fr, p, [decode(fx, c) for c in codes]; scale = decode(fs, s))
end
function convert_to_block_max_abs(n, fx, fs, fr, sp, p, codes)
    n >= 1 && length(codes) == n || throw(DimensionMismatch("block length"))
    xs = [decode(fx, c) for c in codes]
    largest = foldl(
        (a, x) -> extrema(a, magnitude(x); maximum = true, finite_only = true),
        xs;
        init = NAN,
    )
    s = project(fs, sp, largest)
    return BlockValue(s, project_elements(fr, p, xs; scale = decode(fs, s)))
end
block_reduce(kernel, initial, n, fs, fx, fr, p, s, codes) =
    project(fr, p, foldl(kernel, decode_block(n, fs, fx, s, codes); init = initial))
function block_dot(n, fsx, fx, fsy, fy, fr, p, sx, xs, sy, ys)
    x, y = decode_block(n, fsx, fx, sx, xs), decode_block(n, fsy, fy, sy, ys)
    total = foldl((a, xy) -> add(a, multiply(xy...)), zip(x, y); init = finite(0))
    return project(fr, p, total)
end
function is_normal(f, c)
    x = decode(f, c)
    x isa Residual && return residual(:IsNormal, f, c; reason = :missing_backend)
    (!is_finite(x) || is_zero(x) === true) && return false
    return mathematical_le(decode(f, min_normal_code(f)), magnitude(x))
end
function is_subnormal(f, c)
    x = decode(f, c)
    x isa Residual && return residual(:IsSubnormal, f, c; reason = :missing_backend)
    return is_finite(x) && !is_zero(x) && !is_normal(f, c)
end
function classify(f, c)
    x = decode(f, c)
    x isa Residual && return residual(:Class, f, c; reason = :missing_backend)
    is_nan(x) && return :ClsNaN
    is_zero(x) === true && return :ClsZero
    suffix = is_infinite(x) ? "Infinity" : is_normal(f, c) ? "Normal" : "Subnormal"
    return Symbol("Cls", is_negative(x) ? "Negative" : "Positive", suffix)
end
function total_order(f, g, c, d)
    internal_format(f) && internal_format(g) ||
        throw(ArgumentError("total order requires internal formats"))
    x, y = decode(f, c), decode(g, d)
    return is_nan(x) || (!is_nan(y) && mathematical_le(x, y))
end
function decoded_predicate(predicate, name::Symbol, f, c)
    x = decode(f, c)
    x isa Residual && return residual(name, x; reason = :missing_backend)
    return predicate(x)
end
function next_code(f::BinaryFormat, c::Integer, up::Bool)
    x = decode(f, c)
    is_nan(x) && return nan_code(f)
    if up
        (x === POS_INF || (domain(f) == FINITE && c == max_finite_code(f))) && return nan_code(f)
        return is_negative(x) ? (c == nan_code(f)+1 ? big(0) : c-1) : c+1
    end
    (
        x === NEG_INF ||
        (domain(f) == FINITE && c == min_finite_code(f)) ||
        (signedness(f) == UNSIGNED && c == 0)
    ) && return nan_code(f)
    return is_negative(x) ? c+1 : c == 0 ? nan_code(f)+1 : c-1
end
next_code(::Format, ::Integer, ::Bool) =
    throw(ArgumentError("next-value operations require an internal format"))
