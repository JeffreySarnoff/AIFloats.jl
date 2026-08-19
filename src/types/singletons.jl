abstract type FormatKind end
abstract type Signedness <: FormatKind end
abstract type Domain <: FormatKind end

# format signedness
struct ΣUNSIGNED <: Signedness end
struct ΣSIGNED <: Signedness end

const UNSIGNED = ΣUNSIGNED()
const SIGNED = ΣSIGNED()

const ΣBool = Union{ΣUNSIGNED, ΣSIGNED, Bool}
const ΣUBool = Union{ΣUNSIGNED, Bool}
const ΣSBool = Union{ΣSIGNED, Bool}

Base.convert(::Type{Bool}, x::Signedness) =
    x === SIGNED ? true : false

Base.convert(::Type{Signedness}, x::Bool) =
   x ? SIGNED : UNSIGNED

Signedness(x::Bool) = Base.convert(Signedness, x)

Base.convert(::Type{Bool}, ::Type{ΣUNSIGNED}) = ΣUnsigned
Base.convert(::Type{Bool}, ::Type{ΣSIGNED}) = ΣSigned

is_unsigned(x::Signedness) = x === UNSIGNED
is_unsigned(x::Bool) = !x

is_signed(x::Signedness) = x === SIGNED
is_signed(x::Bool) = x

# format domain
struct ΔFINITE <: Domain end
struct ΔEXTENDED <: Domain end

const FINITE = ΔFINITE()
const EXTENDED = ΔEXTENDED()

const ΔBool = Union{ΔFINITE, ΔEXTENDED, Bool}
const ΔFBool = Union{ΔFINITE, Bool}
const ΔEBool = Union{ΔEXTENDED, Bool}

function Base.convert(::Type{Bool}, x::Domain)
    x === EXTENDED ? true : false
end

Base.convert(::Type{Domain}, x::Bool) = x ? EXTENDED : FINITE

Base.convert(::Type{Bool}, ::Type{ΔFINITE}) = ΔFinite
Base.convert(::Type{Bool}, ::Type{ΔEXTENDED}) = ΔExtended

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
struct ρRTE <: ToNearestRoundingMode end
struct ρRTA <: ToNearestRoundingMode end
struct ρRTP <: UnidirectionalRoundingMode end
struct ρRTN <: UnidirectionalRoundingMode end
struct ρRTZ <: UnidirectionalRoundingMode end
struct ρRTO <: ParityRoundingMode end
struct ρRSA <: StochasticRoundingMode end
struct ρRSB <: StochasticRoundingMode end
struct ρRSC <: StochasticRoundingMode end

const RTE = ρRTE()
const RTA = ρRTA()
const RTP = ρRTP()
const RTN = ρRTN()
const RTZ = ρRTZ()
const RTO = ρRTO()
const RSA = ρRSA()
const RSB = ρRSB()
const RSC = ρRSC()

Base.string(x::ρRTE) = "RTE"
Base.string(x::ρRTA) = "RTA"
Base.string(x::ρRTP) = "RTP"
Base.string(x::ρRTN) = "RTN"
Base.string(x::ρRTZ) = "RTZ"
Base.string(x::ρRTO) = "RTO"
Base.string(x::ρRSA) = "RSA"
Base.string(x::ρRSB) = "RSB"
Base.string(x::ρRSC) = "RSC"

Base.String(x::ρRTE) = "RoundToEven"
Base.String(x::ρRTA) = "RoundToAway"
Base.String(x::ρRTP) = "RoundTowardPositive"
Base.String(x::ρRTN) = "RoundTowardNegative"
Base.String(x::ρRTZ) = "RoundTowardZero"
Base.String(x::ρRTO) = "RoundToOdd"
Base.String(x::ρRSA) = "StochasticA"
Base.String(x::ρRSB) = "StochasticB"
Base.String(x::ρRSC) = "StochasticC"

# saturation modes
struct ρSF <: SaturatingSaturationMode end
struct ρSP <: SaturatingSaturationMode end
struct ρSN <: NonsaturatingSaturationMode end

const SF = ρSF()
const SP = ρSP()
const SN = ρSN()

Base.string(x::ρSF) = "SF"
Base.string(x::ρSP) = "SP"
Base.string(x::ρSN) = "SN"

Base.String(x::ρSF) = "SatFinite"
Base.String(x::ρSP) = "SatPropagate"
Base.String(x::ρSN) = "SatNone"

# show projection components

Base.show(io::IO, ::MIME"text/plain", r::RoundingMode) = print(io, string(r))
Base.show(io::IO, r::RoundingMode) = print(io, string(r))

Base.show(io::IO, ::MIME"text/plain", s::SaturationMode) = print(io, string(s))
Base.show(io::IO, s::SaturationMode) = print(io, string(s))

# projections
struct Projection{R<:RoundingMode, S<:SaturationMode}
    rho::Tuple{R, S}
end

Projection(r::R, s::S) where {R<:RoundingMode, S<:SaturationMode} =
    Projection{R,S}((r,s))

const RTE_SF = Projection(RTE, SF)
const RTE_SP = Projection(RTE, SP)
const RTE_SN = Projection(RTE, SN)

const RTA_SF = Projection(RTA, SF)
const RTA_SP = Projection(RTA, SP)
const RTA_SN = Projection(RTA, SN)

const RTP_SF = Projection(RTP, SF)
const RTP_SP = Projection(RTP, SP)
const RTP_SN = Projection(RTP, SN)

const RTN_SF = Projection(RTN, SF)
const RTN_SP = Projection(RTN, SP)
const RTN_SN = Projection(RTN, SN)

const RTZ_SF = Projection(RTZ, SF)
const RTZ_SP = Projection(RTZ, SP)
const RTZ_SN = Projection(RTZ, SN)

const RTO_SF = Projection(RTO, SF)
const RTO_SP = Projection(RTO, SP)
const RTO_SN = Projection(RTO, SN)

const RSA_SF = Projection(RSA, SF)
const RSA_SP = Projection(RSA, SP)
const RSA_SN = Projection(RSA, SN)

const RSB_SF = Projection(RSB, SF)
const RSB_SP = Projection(RSB, SP)
const RSB_SN = Projection(RSB, SN)

const RSC_SF = Projection(RSC, SF)
const RSC_SP = Projection(RSC, SP)
const RSC_SN = Projection(RSC, SN)

RoundOf(p::Projection{R,S}) where {R<:RoundingMode, S<:SaturationMode} = p.rho[1]
SatOf(p::Projection{R,S}) where {R<:RoundingMode, S<:SaturationMode} = p.rho[2]

Base.show(io::IO, ::MIME"text/plain", p::Projection{R,S}) where {R<:RoundingMode, S<:SaturationMode} =
    print(io, "ρ(", string(RoundOf(p)), ", ", string(SatOf(p)), ")"    )

Base.show(io::IO, p::Projection{R,S}) where {R<:RoundingMode, S<:SaturationMode} =
    print(io, "ρ(", String(RoundOf(p)), ", ", String(SatOf(p)), ")")
