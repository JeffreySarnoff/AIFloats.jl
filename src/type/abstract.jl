
abstract type AbstractAIFloat{Bits, SigBits} <: AbstractFloat end

abstract type SignedAIFloat{Bits, SigBits}   <: AbstractAIFloat{Bits, SigBits} end
abstract type UnsignedAIFloat{Bits, SigBits} <: AbstractAIFloat{Bits, SigBits} end

abstract type SignedFiniteAIFloat{Bits, SigBits}   <: SignedAIFloat{Bits, SigBits} end
abstract type SignedExtendedAIFloat{Bits, SigBits} <: SignedAIFloat{Bits, SigBits} end

abstract type UnsignedFiniteAIFloat{Bits, SigBits}   <: UnsignedAIFloat{Bits, SigBits} end
abstract type UnsignedExtendedAIFloat{Bits, SigBits} <: UnsignedAIFloat{Bits, SigBits} end

codes(x::A) where {A<:AbstractAIFloat} = x.codes
floats(x::A) where {A<:AbstractAIFloat} = x.floats

#=

"""
    FloatML{Bits, SigBits}

The abstract type umbrella for all P3109 compliant floating-point types.
- one Zero, one NaN
- sign-symmetric nonzero unbiased exponents

see also [`UnsignedFloatML`](@ref), [`SignedFloatML`](@ref)
"""
abstract type AbstractFloatML{Bits, SigBits} <: AbstractFloat end

abstract type SignedFloat
"""
    UnsignedFloatML{Bits, SigBits}

The abstraction over all P3109 compliant unsigned floating-point types.
- one Zero, one NaN
- sign-symmetric nonzero unbiased exponents

see also [`FloatML`](@ref), [`SignedFloatML`](@ref)
"""
abstract type UnsignedFloatML{Bits, SigBits} <: FloatML{Bits, SigBits} end

"""
    SignedFloatML{Bits, SigBits}

The abstraction over all P3109 compliant signed floating-point types.
- one Zero, one NaN
- sign-symmetric nonzero numeric values
- sign-symmetric nonzero unbiased exponents

see also [`FloatML`](@ref), [`UnsignedFloatML`](@ref)
"""
abstract type SignedFloatML{Bits, SigBits} <: FloatML{Bits, SigBits} end


"""
    UFiniteFloatML{Bits, SigBits}

The abstraction over all P3109 compliant unsigned finite floating-point types.
- one Zero, no Infs, one NaN
- sign-symmetric nonzero unbiased exponents

see also [`FloatML`](@ref), [`SFiniteFloatML`](@ref), [`UExtendedFloatML`](@ref), [`SExtendedFloatML`](@ref)
""" UFiniteFloatML
abstract type UFiniteFloatML{Bits, SigBits}   <: UnsignedFloatML{Bits, SigBits} end

"""
    SFiniteFloatML{Bits, SigBits}

The abstraction over all P3109 compliant signed finite floating-point types.
- one Zero, no Infs, one NaN
- sign-symmetric nonzero numeric values
- sign-symmetric nonzero unbiased exponents

see also [`FloatML`](@ref), [`UFiniteFloatML`](@ref), [`UExtendedFloatML`](@ref), [`SExtendedFloatML`](@ref)
"""
abstract type SFiniteFloatML{Bits, SigBits}   <: SignedFloatML{Bits, SigBits} end


"""
    UExtendedFloatML{Bits, SigBits}

The abstraction over all P3109 compliant unsigned extended floating-point types.
- one Zero, one Inf, one NaN
- sign-symmetric nonzero unbiased exponents

see also [`FloatML`](@ref), [`SExtendedFloatML`](@ref), [`UFiniteFloatML`](@ref), [`SFiniteFloatML`](@ref)
"""
abstract type UExtendedFloatML{Bits, SigBits} <: UnsignedFloatML{Bits, SigBits} end

"""
    SExtendedFloatML{Bits, SigBits}

The abstraction over all P3109 compliant signed extended floating-point types.
- one Zero, two Infs, one NaN
- sign-symmetric nonzero numeric values
- sign-symmetric nonzero unbiased exponents

see also [`FloatML`](@ref), [`UExtendedFloatML`](@ref), [`SFiniteFloatML`](@ref), [`UFiniteFloatML`](@ref)
"""
abstract type SExtendedFloatML{Bits, SigBits} <: SignedFloatML{Bits, SigBits} end

"""
    FiniteFloatML{Bits, SigBits}

The abstraction over all P3109 compliant finite floating-point types.
- one Zero, no Infs, one NaN
- sign-symmetric nonzero unbiased exponents

see also [`FloatML`](@ref), [`ExtendedFloatML`](@ref)
"""
const FiniteFloatML{Bits, SigBits} = Union{UFiniteFloatML{Bits, SigBits}, SFiniteFloatML{Bits, SigBits}}

"""
    ExtendedFloatML{Bits, SigBits}

The abstraction over all P3109 compliant extended floating-point types.
- one Zero, at least one Inf, one NaN
- sign-symmetric nonzero unbiased exponents

see also [`FloatML`](@ref), [`FiniteFloatML`](@ref)
"""
const ExtendedFloatML{Bits, SigBits} = Union{UExtendedFloatML{Bits, SigBits}, SExtendedFloatML{Bits, SigBits}}
=#
