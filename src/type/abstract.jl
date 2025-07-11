
"""
    AbstractAIFloat{bitwidth, precision}

supertype: AbstractFloat

see [`AbstractSigned`](@ref), [`AbstractUnsigned`](@ref)
""" AbstractAIFloat

abstract type AbstractAIFloat{Bits, SigBits, IsSigned} <: AbstractFloat end

"""
    AbstractSigned{bitwidth, precision}

supertype: AbstractAIFloat

see [`AbstractAIFloat`](@ref), [`AbstractUnsigned`](@ref)
""" AbstractSigned

abstract type AbstractSigned{Bits, SigBits} <: AbstractAIFloat{Bits, SigBits, true} end

"""
    AbstractUnsigned{bitwidth, precision}

supertype: AbstractAIFloat

see [`AbstractAIFloat`](@ref), [`AbstractSigned`](@ref)
""" AbstractUnsigned

abstract type AbstractUnsigned{Bits, SigBits} <: AbstractAIFloat{Bits, SigBits, false} end

"""
    AkoSignedFinite{bitwidth, precision}

supertype: AbstractSigned

see [`AIFloat`](@ref), [`AkoSignedExtended`](@ref), [`AbstractSigned`](@ref),

""" AkoSignedFinite

abstract type AkoSignedFinite{Bits, SigBits} <: AbstractSigned{Bits, SigBits} end

"""
    AkoSignedExtended{bitwidth, precision}

supertype: AbstractSigned

see [`AIFloat`](@ref), [`AkoSignedFinite`](@ref), [`AbstractSigned`](@ref),
""" AkoSignedExtended

abstract type AkoSignedExtended{Bits, SigBits} <: AbstractSigned{Bits, SigBits} end

"""
    AkoUnsignedFinite{bitwidth, precision}

supertype: AbstractUnsigned

see [`AIFloat`](@ref), [`AkoUnsignedExtended`](@ref), [`AbstractUnsigned`](@ref),
""" AkoUnsignedFinite

abstract type AkoUnsignedFinite{Bits, SigBits} <: AbstractUnsigned{Bits, SigBits} end

"""
    AkoUnsignedExtended{bitwidth, precision}

supertype: AbstractUnsigned

see [`AIFloat`](@ref), [`AkoUnsignedFinite`](@ref), [`AbstractUnsigned`](@ref)
""" AkoUnsignedExtended

abstract type AkoUnsignedExtended{Bits, SigBits} <: AbstractUnsigned{Bits, SigBits} end

