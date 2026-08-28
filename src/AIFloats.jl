module AIFloats

export AIFloat, BinaryFloat, Binary,
# Binary format signedness
ΣBool, UNSIGNED, SIGNED, is_unsigned, is_signed,
# Binary  format domain
ΔBool, FINITE, EXTENDED, is_finite, is_extended,
# rounding modes
# NearestTiesToEven, NearestTiesToAway, TowardPositive, TowardNegative, TowardZero, ToOdd, StochasticUnbiased, StochasticBiased, StochasticFast
RTE, RTA, RTP, RTN, RTZ, RTO, RSA, RSB, RSC,
# saturation modes
# SatFinite, SatPropogate, SatNone
SF, SP, SN,
# projection functions
Projection, RoundOf, SatOf,
# projections
RTE_SF, RTE_SP, RTE_SN, RTA_SF, RTA_SP, RTA_SN, RTP_SF, RTP_SP, RTP_SN, RTN_SF, RTN_SP, RTN_SN, RTZ_SF, RTZ_SP, RTZ_SN, RTO_SF, RTO_SP, RTO_SN, RSA_SF, RSA_SP, RSA_SN, RSB_SF, RSB_SP, RSB_SN, RSC_SF, RSC_SP, RSC_SN,
# Binary format API
BitwidthOf, PrecisionOf, SignednessOf, DomainOf,
# external types (IEEE 754, bfloat16)
binary16, binary32, binary64, binary128, bfloat16,
# dual use constants: both implementation-facing and user-facing
IntParam, 
CodeType, ValueType

# published, must be imported explicitly
public resolve_fields

# working with other Julia packages
using Quadmath
using BFloat16s

# internal organization
include("types/constants.jl")
include("types/external.jl")
include("types/singletons.jl")
include("types/binaryformats.jl")

# include("rules/constraints.jl")  # TODO: file does not exist yet

include("content/gentables.jl")

end  

# AIFloats.jl
