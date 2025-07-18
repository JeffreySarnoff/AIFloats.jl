# remove ambiguities identified by Aqua.jl

UnsignedFinite{bits, sigbits, T, S}(::Real, ::RoundingMode) where {S<:Unsigned, T<:AbstractFP, sigbits, bits} = false
UnsignedExtended{bits, sigbits, T, S}(::Real, ::RoundingMode) where {S<:Unsigned, T<:AbstractFP, sigbits, bits} = false

SignedFinite{bits, sigbits, T, S}(::Real, ::RoundingMode) where {S<:Unsigned, T<:AbstractFP, sigbits, bits} = false
SignedExtended{bits, sigbits, T, S}(::Real, ::RoundingMode) where {S<:Unsigned, T<:AbstractFP, sigbits, bits} = false
