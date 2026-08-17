module AIFloats

export AIFloat,
# format signedness
UNSIGNED, SIGNED, 
# format domain
FINITE, EXTENDED,
# rounding modes
RNE, RNA, RUP, RDN, RTZ, RTO, RSA, RSB, RSC.
# saturation modes
SF, SP, SN,
# external types (IEEE 754, bfloat16)
binary16, binary32, binary64, bfloat16

# internal organization
include("types/external.jl")
include("types/singletons.jl")
include("types/formats.jl")

end  # AIFloats.jl
