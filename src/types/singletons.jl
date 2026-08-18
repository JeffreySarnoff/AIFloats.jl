abstract type FormatKind end
abstract type Signedness <: FormatKind end
abstract type Domain <: FormatKind end

# format signedness
struct ΣUNSIGNED <: Signedness end
struct ΣSIGNED <: Signedness end

const UNSIGNED = ΣUNSIGNED()
const SIGNED = ΣSIGNED()

Base.convert(::Type{Bool}, x::Signedness) =
    x === SIGNED ? true : false

Base.convert(::Type{Signedness}, x::Bool) =
   x ? SIGNED : UNSIGNED

Signedness(x::Bool) = Base.convert(Signedness, x)

Base.convert(::Type{Bool}, ::Type{ΣUNSIGNED}) = false
Base.convert(::Type{Bool}, ::Type{ΣSIGNED}) = true

is_unsigned(x::Signedness) = x === UNSIGNED
is_unsigned(x::Bool) = !x

is_signed(x::Signedness) = x === SIGNED
is_signed(x::Bool) = x

# format domain
struct ΔFINITE <: Domain end
struct ΔEXTENDED <: Domain end

const FINITE = ΔFINITE()
const EXTENDED = ΔEXTENDED()

function Base.convert(::Type{Bool}, x::Domain)
    x === EXTENDED ? true : false
end

Base.convert(::Type{Domain}, x::Bool) = x ? EXTENDED : FINITE

Base.convert(::Type{Bool}, ::Type{ΔFINITE}) = false
Base.convert(::Type{Bool}, ::Type{ΔEXTENDED}) = true

Domain(x::Bool) = convert(Domain, x)

is_finite(x::Domain) = x === FINITE
is_finite(x::Bool) = !x

is_extended(x::Domain) = x === EXTENDED
is_extended(x::Bool) = x

@inline Base.string(x::Signedness) = x === SIGNED ? "SIGNED" : "UNSIGNED"
@inline Base.string(x::Domain) = x === EXTENDED ? "EXTENDED" : "FINITE"

function Base.show(io::IO, ::MIME"text/plain", S::Signedness)
    str = string(S)
    print(io, str)
end

function Base.show(io::IO, S::Signedness)
    str = string(S)
    print(io, str)
end

function Base.show(io::IO, ::MIME"text/plain", D::Domain)
    str = string(D)
    print(io, str)
end

function Base.show(io::IO, D::Domain)
    d = string(D)
    print(io, d)
end

# Projection Components (Rounding, Saturation)

abstract type ProjectionComponent end
abstract type RoundingMode <: ProjectionComponent end
abstract type SaturationMode <: ProjectionComponent end

abstract type DeterministicRoundingMode <: RoundingMode end
abstract type ToNearestRoundingMode <: DeterministicRoundingMode end
abstract type UnidirectionalRoundingMode <: DeterministicRoundingMode end
abstract type ParityRoundingMode <: DeterministicRoundingMode end
abstract type StochasticRoundingMode <: RoundingMode end

abstract type SaturatingSaturationMode <: SaturationMode end
abstract type NonsaturatingSaturationMode <: SaturationMode end

# rounding modes
struct RTE <: ToNearestRoundingMode end
struct RTA <: ToNearestRoundingMode end
struct RUP <: UnidirectionalRoundingMode end
struct RDN <: UnidirectionalRoundingMode end
struct RTZ <: UnidirectionalRoundingMode end
struct RTO <: ParityRoundingMode end
struct RSA <: StochasticRoundingMode end
struct RSB <: StochasticRoundingMode end
struct RSC <: StochasticRoundingMode end

# saturation modes
struct SF <: SaturatingSaturationMode end
struct SP <: SaturatingSaturationMode end
struct SN <: NonsaturatingSaturationMode end
