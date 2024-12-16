module FloatsForML

export AbstractBinaryFloat, AbstractSignedFloat, AbstractUnsignedFloat,
    AkoSignedFiniteFloat, AkoSignedInfiniteFloat, 
    AkoUnsignedFiniteFloat, AkoUnsignedInfiniteFloat,
    # structs with fields ordered by CodePoint
    SignedFiniteFloat, SignedInfiniteFloat,
    UnsignedFiniteFloat, UnsignedInfiniteFloat,
    # structs with fields ordered by FloatValue
    SignedFiniteFP, SignedInfiniteFP,
    UnsignedFiniteFP, UnsignedInfiniteFP,
    # 
    CodePoint, FloatValue, codes, floats,
    #
    is_signed, is_unsigned, is_finite, is_infinite,
    #
    n_numeric_values, n_finite_values, n_infinite_values,
    n_subnormal_values, subnormal_max, subnormal_min,
    n_normal_values, normal_max, normal_min,
    exponent_max, exponent_min, exponent_bias,
    #
    n_bits, n_sig_bits, n_fraction_bits, n_exponent_bits, n_sign_bits,
    n_values, n_sig_values, n_fraction_values, n_exponent_values, 
    n_fraction_cycles, n_exponent_cycles


abstract type AbstractBinaryFloat{Bits, SigBits} <: AbstractFloat end

abstract type AbstractSignedFloat{Bits, SigBits}      <: AbstractBinaryFloat{Bits, SigBits} end
  abstract type AkoSignedFiniteFloat{Bits, SigBits}   <: AbstractSignedFloat{Bits, SigBits} end
  abstract type AkoSignedInfiniteFloat{Bits, SigBits} <: AbstractSignedFloat{Bits, SigBits} end

abstract type AbstractUnsignedFloat{Bits, SigBits}      <: AbstractBinaryFloat{Bits, SigBits} end
  abstract type AkoUnsignedFiniteFloat{Bits, SigBits}   <: AbstractUnsignedFloat{Bits, SigBits} end
  abstract type AkoUnsignedInfiniteFloat{Bits, SigBits} <: AbstractUnsignedFloat{Bits, SigBits} end

include("construct.jl")
include("type.jl")
include("predicates.jl")
include("substructural.jl")
include("aqua.jl")

"""
    AbstractBinaryFloat

A specialization of AbstractFloat with parameters {Bits, SigBits}.
- comports with IEEE SA P3109 

See also [`AbstractFloat`](@ref).
""" AbstractBinaryFloat

"""
    AbstractUnsignedFloat

An unsigned binary floating-point abstraction.
    - Provides NaN

See also [`AbstractBinaryFloat`, `AbstractSignedFloat`](@ref).
""" AbstractUnsignedFloat

"""
    AbstractSignedFloat

A signed binary floating-point abstraction.
    - Provides NaN

See also [`AbstractBinaryFloat`, `AbstractUnsignedBinaryFloat`](@ref).
""" AbstractSignedFloat

"""
    AkoSignedInfiniteFloat

    An Infinite Finite projection of AbstractBinaryFloat. Has NaN, has Inf.
    - Provides NaN
    - Provides ±Inf

See also [`AbstractBinaryFloat`, `AbstractSignedFloat`](@ref).
""" AkoSignedInfiniteFloat

"""
    AkoUnsignedInfiniteFloat

    An Infinite projection of AbstractSignedFloat.
    - Provides NaN
    - Provides Inf

See also [`AbstractBinaryFloat`, `AbstractUnsignedFloat`](@ref).
""" AkoUnsignedInfiniteFloat

"""
    AkoSignedFiniteFloat

    An finite projection of AbstractSignedFloat
    - Provides NaN
 
See also [`AbstractBinaryFloat`, `AbstractSignedFloat`](@ref).
""" AkoSignedFiniteFloat

"""
    AkoUnsignedFiniteFloat

    An infinite projection of AbstractUnsignedFloat.
    - Provides NaN
 
See also [`AbstractBinaryFloat`, `AbstractUnsignedFloat`](@ref).
""" AkoUnsignedFiniteFloat


end  # FloatsForML
