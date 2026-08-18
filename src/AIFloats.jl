module AIFloats

using SmallCollections

export AIFloat,
# format signedness
UNSIGNED, SIGNED, is_unsigned, is_signed,
# format domain
FINITE, EXTENDED, is_finite, is_extended,
# rounding modes
RTE, RTA, RUP, RDN, RTZ, RTO, RSA, RSB, RSC,
# saturation modes
SF, SP, SN,
# projection functions
Projection, RoundOf, SatOf,
# projections
RTE_SF, RTE_SP, RTE_SN, RTA_SF, RTA_SP, RTA_SN, RUP_SF, RUP_SP, RUP_SN, RDN_SF, RDN_SP, RDN_SN, RTZ_SF, RTZ_SP, RTZ_SN, RTO_SF, RTO_SP, RTO_SN, RSA_SF, RSA_SP, RSA_SN, RSB_SF, RSB_SP, RSB_SN, RSC_SF, RSC_SP, RSC_SN,
# format API
Format, Binary,
format, binary, format_fields, FormatOf, BinaryOf,
BitwidthOf, PrecisionOf, SignednessOf, DomainOf,
# external types (IEEE 754, bfloat16)
binary16, binary32, binary64, bfloat16

# internal organization
include("types/external.jl")
include("types/singletons.jl")
include("types/formats.jl")

include("rules/constraints.jl")

include("content/gentables.jl")

end  

# AIFloats.jl
