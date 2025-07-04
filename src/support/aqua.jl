# remove ambiguities identified by Aqua.jl

UnsignedFiniteFloat{bits, sigbits, T, S}(::Real, ::RoundingMode) where {S<:Unsigned, T<:AbstractFloat, sigbits, bits} = false
UnsignedExtendedFloat{bits, sigbits, T, S}(::Real, ::RoundingMode) where {S<:Unsigned, T<:AbstractFloat, sigbits, bits} = false

SignedFiniteFloat{bits, sigbits, T, S}(::Real, ::RoundingMode) where {S<:Unsigned, T<:AbstractFloat, sigbits, bits} = false
SignedExtendedFloat{bits, sigbits, T, S}(::Real, ::RoundingMode) where {S<:Unsigned, T<:AbstractFloat, sigbits, bits} = false
