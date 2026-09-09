# Source: lib/conformance.maude. These records declare claims, not certificates.
struct Specialization{F,P,B}
    kind::Symbol
    name::String
    formats::F
    size::BigInt
    projection::P
    block_projection::B
end
specialization(kind, name, formats; size = 0, projection = nothing, block_projection = nothing) =
    Specialization(kind, String(name), Tuple(formats), big(size), projection, block_projection)
Base.:(==)(x::Specialization, y::Specialization) =
    (x.kind, x.name, x.formats, x.size, x.projection, x.block_projection) ==
    (y.kind, y.name, y.formats, y.size, y.projection, y.block_projection)
@enum KappaKind FINITE_STEPS INFINITY_MISMATCH NAN_MISMATCH
struct Kappa
    kind::KappaKind
    steps::BigInt
    function Kappa(kind::KappaKind, steps::Integer = 0)
        steps >= 0 || throw(ArgumentError("negative kappa bound"))
        new(kind, big(steps))
    end
end
Base.:(==)(x::Kappa, y::Kappa) = x.kind == y.kind && x.steps == y.steps
merge_kappa(x::Kappa, y::Kappa) =
    Kappa(max(x.kind, y.kind), max(x.steps, y.steps)*(x.kind==FINITE_STEPS && y.kind==FINITE_STEPS))
struct KappaPart{C}
    codes::C
    bound::Kappa
end
struct Observation{C,F}
    name::String
    inputs::C
    format::F
    expected::BigInt
    observed::BigInt
end
Observation(name, inputs, f, c::Integer, d::Integer) =
    Observation(String(name), inputs, f, big(c), big(d))
struct Declaration{S,C,P}
    kind::Symbol
    identity::S
    name::String
    bound::Kappa
    universe::C
    parts::P
    evidence::Symbol
end
declaration(kind, s, name, e; bound = Kappa(FINITE_STEPS), universe = (), parts = ()) =
    Declaration(kind, s, String(name), bound, universe, parts, e)
const F4 = BinaryFormat(4, 2, SIGNED, FINITE)
const F8 = BinaryFormat(8, 4, SIGNED, EXTENDED)
const G8 = BinaryFormat(8, 3, SIGNED, EXTENDED)
const FS = BinaryFormat(8, 1, UNSIGNED, FINITE)
in_f4(f) = f == F4
in_f8(f) = f == F8 || f == G8
in_fs(f) = f == FS
allowed_external(f) = f in (BINARY32, BINARY16, BFLOAT16)
valid_fx_tail(fs) = all(allowed_external, fs) && allunique(fs)
valid_fx(fs) = !isempty(fs) && valid_fx_tail(fs)
all_formats(fs) = all(valid_format, fs)
const MINMAX_NAMES = (
    "Minimum",
    "Maximum",
    "MinimumNumber",
    "MaximumNumber",
    "MinimumMagnitude",
    "MaximumMagnitude",
    "MinimumMagnitudeNumber",
    "MaximumMagnitudeNumber",
    "MinimumFinite",
    "MaximumFinite",
)
const COMPARE_NAMES =
    ("CompareLess", "CompareLessEqual", "CompareEqual", "CompareGreater", "CompareGreaterEqual")
const PREDICATE_NAMES = (
    "IsZero",
    "IsOne",
    "IsNaN",
    "IsInfinite",
    "IsFinite",
    "IsSignMinus",
    "IsNormal",
    "IsSubnormal",
    "NextGreaterThan",
    "NextLessThan",
)
const FORMAT_NAMES = (
    "BitwidthOf",
    "PrecisionOf",
    "SignednessOf",
    "DomainOf",
    "ExponentBitwidthOf",
    "TrailingSignificandBitwidthOf",
    "ExponentBiasOf",
    "MaxFiniteOf",
    "MinFiniteOf",
    "MinPositiveOf",
    "MaxSubnormalOf",
    "MinNormalOf",
)
numeric_plain_name(n) = n in (
    "NextGreaterThan",
    "NextLessThan",
    "MaxFiniteOf",
    "MinFiniteOf",
    "MinPositiveOf",
    "MaxSubnormalOf",
    "MinNormalOf",
)
function required_numeric(name, formats, external)
    core(f) = in_f4(f) || in_f8(f)
    allf(f) = core(f) || f in external
    output(f) = in_f8(f) || f in external
    n = length(formats)
    if n == 2
        f, g = formats
        return (name in ("Convert", "Recip") && allf(f) && allf(g)) ||
               (name in ("Abs", "Negate") && f==g && core(f))
    elseif n == 3
        f, g, h = formats
        return (name in ("Add", "Subtract", "Multiply") && core(f) && core(g) && output(h)) ||
               (name in MINMAX_NAMES && f==g==h && core(f))
    elseif n == 4
        f, g, h, j = formats
        return name in ("FMA", "FAA") && core(f) && core(g) && h==j && h in external
    elseif n == 5
        f, g, h, j, l = formats
        return name in ("ScaledAdd", "ScaledSubtract", "ScaledMultiply") &&
               in_fs(f) &&
               f==h &&
               core(g) &&
               core(j) &&
               output(l)
    end
    return false
end
function required_plain(name, formats, external)
    if length(formats) == 1
        f = first(formats)
        return (name in PREDICATE_NAMES && (in_f4(f)||in_f8(f))) ||
               (name in FORMAT_NAMES && (in_f4(f)||in_f8(f)||f in external))
    elseif length(formats) == 2
        f, g = formats
        return name in COMPARE_NAMES && f==g && (in_f4(f)||in_f8(f))
    end
    return false
end
function required(s::Specialization, external)
    valid_fx(external) || return false
    s.kind == :numeric && return s.projection == Projection(NEAREST_EVEN, SAT_NONE) &&
           required_numeric(s.name, s.formats, external)
    return s.kind == :plain && required_plain(s.name, s.formats, external)
end
include("arity_tables.jl")
numeric_arity(n, a) = (String(n), a) in NUMERIC_ARITIES
plain_arity(n, a) = (String(n), a) in PLAIN_ARITIES
block_element_arity(n, a) = (String(n), a) in BLOCK_ARITIES
function valid_specialization(s::Specialization)
    all_formats(s.formats) || return false
    n = length(s.formats)
    s.kind == :numeric && return s.projection isa Projection && numeric_arity(s.name, n)
    s.kind == :plain && return plain_arity(s.name, n)
    s.size >= 1 || return false
    if s.kind == :blockElements
        return valid_block_projection(s.block_projection, s.size) && block_element_arity(s.name, n)
    elseif s.kind == :blockReduction
        return s.projection isa Projection && (
            (s.name in ("BlockReduceAdd", "BlockReduceMultiply") && n==3) ||
            (s.name=="BlockDotProduct" && n==5)
        )
    end
    return s.kind == :blockScale &&
           s.name == "ConvertToBlockMaxAbsFinite" &&
           n==3 &&
           s.projection isa Projection &&
           valid_block_projection(s.block_projection, s.size)
end
numeric_result(s::Specialization) = s.kind != :plain || numeric_plain_name(s.name)
partition_union(parts) = collect(Iterators.flatten(parts))
partition_disjoint(parts) = allunique(Iterators.flatten(parts))
function partition(universe, parts)
    allunique(universe) && partition_disjoint(parts) || return false
    return Set(universe) == Set(Iterators.flatten(parts))
end
function well_formed_declaration(d::Declaration)
    isempty(d.name) && return false
    valid_specialization(d.identity) || return false
    d.kind == :exact && return true
    d.name != d.identity.name && numeric_result(d.identity) || return false
    return d.kind == :approximate ||
           (d.kind == :partitioned && partition(d.universe, map(p->p.codes, d.parts)))
end
has_declaration(s, ds) = any(d -> well_formed_declaration(d) && d.identity == s, ds)
declarations_cover(ss, ds) = all(s -> has_declaration(s, ds), ss)
part_bound(parts) = foldl((k, p)->merge_kappa(k, p.bound), parts; init = Kappa(FINITE_STEPS))
function declaration_kappa(d::Declaration)
    well_formed_declaration(d) && numeric_result(d.identity) ||
        throw(ArgumentError("invalid numeric declaration"))
    return d.kind == :partitioned ? part_bound(d.parts) : d.bound
end
function finite_rank(f, c)
    x=decode(f, c)
    is_finite(x) || throw(DomainError(c, "rank requires a finite datum"))
    signedness(f)==UNSIGNED && return big(c)
    return is_negative(x) ? min_finite_code(f)-c : max_finite_code(f)+c
end
function observation_kappa(o::Observation)
    x, y = decode(o.format, o.expected), decode(o.format, o.observed)
    is_nan(x) != is_nan(y) && return Kappa(NAN_MISMATCH)
    is_nan(x) && return Kappa(FINITE_STEPS)
    is_infinite(x) ||
        is_infinite(y) ||
        return Kappa(
            FINITE_STEPS,
            abs(finite_rank(o.format, o.expected)-finite_rank(o.format, o.observed)),
        )
    return x === y ? Kappa(FINITE_STEPS) : Kappa(INFINITY_MISMATCH)
end
batch_kappa(os) =
    foldl((k, o)->merge_kappa(k, observation_kappa(o)), os; init = Kappa(FINITE_STEPS))

"""Inspect an evidence tag as the source does; this does not verify its claim."""
evidence_complete(e::Symbol) = e in (:exhaustiveEvidence, :proofEvidence)
