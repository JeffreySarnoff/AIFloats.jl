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
# format API
Format, Binary,
format, binary, format_fields, FormatOf, BinaryOf,
BitwidthOf, PrecisionOf, SignednessOf, DomainOf,
# external types (IEEE 754, bfloat16)
binary16, binary32, binary64, bfloat16,
hello_world

# internal organization
include("types/external.jl")
include("types/singletons.jl")
include("types/formats.jl")

hello_world() = "Hello, World!"

end  

# AIFloats.jl
