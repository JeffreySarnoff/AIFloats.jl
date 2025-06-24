#=

export  AbstractAIFloat, AbsSignedFloat, AbsUnsignedFloat,
        AbsSignedFiniteFloat, AbsSignedExtendedFloat,
        AbsUnsignedFiniteFloat, AbsUnsignedExtendedFloat,
        nBits, nSigBits, nFracBits, nValues, nNumericValues, nNonzeroNumericValues,
        nSigMagnitudes, nNonzeroSigMagnitudes, nFracMagnitudes, nNonzeroFracMagnitudes,
        nExpBits, nExpValues, nNonzeroExpValues, nMagnitudes, nNonzeroMagnitudes,
        nFiniteValues, nNonzeroFiniteValues, nFiniteMagnitudes, nNonzeroFiniteMagnitudes,
        nNonnegValues, nPositiveValues, nNegativeValues,
        nFiniteNonnegValues, nFinitePositiveValues, nFiniteNegativeValues,
        nPrenormalMagnitudes, nSubnormalMagnitudes, nPrenormalValues, nSubnormalValues,
        nNormalMagnitudes, nNormalValues, nExtendedNormalMagnitudes, nExtendedNormalValues,
        expUnbiasedMax, expUnbiasedMin, expUnbiasedValues, expBias,
        is_extended, is_finite, is_signed, is_unsigned,
        nNaNs, nZeros, nInfs, nPosInfs, nNegInfs,
        normal_magnitude_steps, prenormal_magnitude_steps,
        normal_exp_stride, foundation_extremal_exps, foundation_exps,
        exp_unbiased_magnitude_strides, pow2_foundation_exps,
        prenormal_magnitude_steps, normal_magnitude_steps, normal_exp_stride,
        foundation_extremal_exps, foundation_exps, exp_unbiased_magnitude_strides, pow2_foundation_exps,
        foundation_magnitudes, foundation_values, value_sequence)

=#

abstract type AbstractAIFloat{Bits, SigBits, IsSigned} <: AbstractFloat end

abstract type AbsSignedFloat{Bits, SigBits} <: AbstractAIFloat{Bits, SigBits, true} end
abstract type AbsUnsignedFloat{Bits, SigBits} <: AbstractAIFloat{Bits, SigBits, false} end

abstract type AbsSignedFiniteFloat{Bits, SigBits} <: AbsSignedFloat{Bits, SigBits} end
abstract type AbsSignedExtendedFloat{Bits, SigBits} <: AbsSignedFloat{Bits, SigBits} end

abstract type AbsUnsignedFiniteFloat{Bits, SigBits} <: AbsUnsignedFloat{Bits, SigBits} end
abstract type AbsUnsignedExtendedFloat{Bits, SigBits} <: AbsUnsignedFloat{Bits, SigBits} end

# predicates for abstract types

is_aifloat(@nospecialize(T::Type{<:AbstractFloat})) = false
is_aifloat(@nospecialize(T::Type{<:AbstractAIFloat})) = true

is_signed(@nospecialize(T::Type{<:AbsSignedFloat}))     = true
is_signed(@nospecialize(T::Type{<:AbsUnsignedFloat}))   = false

is_unsigned(@nospecialize(T::Type{<:AbsSignedFloat}))   = false
is_unsigned(@nospecialize(T::Type{<:AbsUnsignedFloat})) = true

is_finite(@nospecialize(T::Type{<:AbsSignedFiniteFloat}))     = true
is_finite(@nospecialize(T::Type{<:AbsUnsignedFiniteFloat}))   = true
is_finite(@nospecialize(T::Type{<:AbsSignedExtendedFloat}))   = false
is_finite(@nospecialize(T::Type{<:AbsUnsignedExtendedFloat})) = false

is_extended(@nospecialize(T::Type{<:AbsSignedFiniteFloat}))     = false
is_extended(@nospecialize(T::Type{<:AbsUnsignedFiniteFloat}))   = false
is_extended(@nospecialize(T::Type{<:AbsSignedExtendedFloat}))   = true
is_extended(@nospecialize(T::Type{<:AbsUnsignedExtendedFloat})) = true

# cover instantiations
is_aifloat(@nospecialize(x::T)) where {T<:AbstractFloat} = false
is_aifloat(@nospecialize(x::T)) where {T<:AbstractAIFloat} = true

for F in (:is_extended, :is_finite, :is_signed, :is_unsigned) 
    @eval $F(x::T) where {T<:AbstractAIFloat} = $F(T)
end

# counts predicated on abstract [sub]type

nNaNs(@nospecialize(T::Type{<:AbstractAIFloat})) = 1
nZeros(@nospecialize(T::Type{<:AbstractAIFloat})) = 1

nInfs(@nospecialize(T::Type{<:AbsSignedFiniteFloat}))     = 0
nInfs(@nospecialize(T::Type{<:AbsUnsignedFiniteFloat}))   = 0
nInfs(@nospecialize(T::Type{<:AbsSignedExtendedFloat}))   = 2
nInfs(@nospecialize(T::Type{<:AbsUnsignedExtendedFloat})) = 1

nPosInfs(@nospecialize(T::Type{<:AbstractAIFloat})) = (nInfs(T) + 1) >> 1
nNegInfs(@nospecialize(T::Type{<:AbsSignedFloat})) = (nInfs(T) + 1) >> 1
nNegInfs(@nospecialize(T::Type{<:AbsUnsignedFloat})) = 0

# counts predicated on type defining parameters and type specifying qualities
# parameters: (bits, sigbits, exponent bias)
# qualities: (signedness [signed / unsigned], finiteness [finite / extended (has Inf[s])])

nBits(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = Bits
nSigBits(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = SigBits
nFracBits(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = nSigBits(T) - 1

nSignBits(::Type{T}) where {Bits, SigBits, T<:AbsSignedFloat{Bits, SigBits}} = 1
nSignBits(::Type{T}) where {Bits, SigBits, T<:AbsUnsignedFloat{Bits, SigBits}} = 0

nValues(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = 1 << nBits(T)
nNumericValues(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = nValues(T) - 1
nNonzeroNumericValues(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = nNumericValues(T) - 1

nSigMagnitudes(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = 1 << nSigBits(T)
nNonzeroSigMagnitudes(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = nSigMagnitudes(T) - 1

nFracMagnitudes(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = 1 << nFracBits(T)
nNonzeroFracMagnitudes(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = nFracMagnitudes(T) - 1

nExpBits(::Type{T}) where {Bits, SigBits, T<:AbsSignedFloat{Bits, SigBits}} = nBits(T) - nSigBits(T)
nExpBits(::Type{T}) where {Bits, SigBits, T<:AbsUnsignedFloat{Bits, SigBits}} = nBits(T) - nSigBits(T) + 1

nExpValues(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = 1 << nExpBits(T)
nNonzeroExpValues(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = nExpValues(T) - 1


nMagnitudes(::Type{T}) where {Bits, SigBits, T<:AbsSignedFloat{Bits, SigBits}} = nValues(T) >> 1
nMagnitudes(::Type{T}) where {Bits, SigBits, T<:AbsUnsignedFloat{Bits, SigBits}} = nNumericValues(T)

nNonzeroMagnitudes(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = nMagnitudes(T) - 1

nFiniteValues(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = nNumericValues(T) - nInfs(T)
nNonzeroFiniteValues(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = nFiniteValues(T) - 1

nFiniteMagnitudes(::Type{T}) where {Bits, SigBits, T<:AbsSignedFloat{Bits, SigBits}} = nMagnitudes(T) - nPosInfs(T)
nNonzeroFiniteMagnitudes(::Type{T}) where {Bits, SigBits, T<:AbsSignedFloat{Bits, SigBits}} = nFiniteMagnitudes(T) - 1

nNonnegValues(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = nMagnitudes(T)
nPositiveValues(::Type{T}) where {Bits, SigBits, T<:AbsSignedFloat{Bits, SigBits}} = nNonnegValues(T) - 1
nNegativeValues(::Type{T}) where {Bits, SigBits, T<:AbsSignedFloat{Bits, SigBits}} = nNumericValues(T) - nNonnegValues(T)

nFiniteNonnegValues(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = nNonnegValues(T) - nPosInfs(T)
nFinitePositiveValues(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = nPositiveValues(T) - nPosInfs(T)
nFiniteNegativeValues(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = nNegativeValues(T) - nNegInfs(T)

nPrenormalMagnitudes(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = 1 << (SigBits - 1)
nSubnormalMagnitudes(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = nPrenormalMagnitudes(T) - 1

nPrenormalValues(::Type{T}) where {Bits, SigBits, T<:AbsSignedFloat{Bits, SigBits}} = 2 * nPrenormalMagnitudes(T) - 1
nPrenormalValues(::Type{T}) where {Bits, SigBits, T<:AbsUnsignedFloat{Bits, SigBits}} = nPrenormalMagnitudes(T)

nSubnormalValues(::Type{T}) where {Bits, SigBits, T<:AbsSignedFloat{Bits, SigBits}} = nPrenormalValues(T) - 1

nNormalMagnitudes(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = nFiniteMagnitudes(T) - nPrenormalMagnitudes(T)
nNormalValues(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = nFiniteValues(T) - nPrenormalValues(T)

nExtendedNormalMagnitudes(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} =
    nNormalMagnitudes(T) + nPosInfs(T)

nExtendedNormalValues(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} =
    nNormalMagnitudes(T) + nInfs(T)

# support for instantiations
for F in (:nBits, :nSigBits, :nFracBits,
          :nNaNs, :nZeros, :nInfs, :nPosInfs, :nNegInfs,
          :nValues, :nNumericValues, :nNonzeroNumericValues,
          :nSigMagnitudes, :nNonzeroSigMagnitudes, :nFracMagnitudes, :nNonzeroFracMagnitudes,
          :nMagnitudes, :nNonzeroMagnitudes,
          :nFiniteValues, :nNonzeroFiniteValues, :nFiniteMagnitudes, :nNonzeroFiniteMagnitudes,
          :nNonnegValues, :nPositiveValues, :nNegativeValues,
          :nFiniteNonnegValues, :nFinitePositiveValues, :nFiniteNegativeValues,
          :nPrenormalMagnitudes, :nSubnormalMagnitudes, :nPrenormalValues, :nSubnormalValues,
          :nNormalMagnitudes, :nNormalValues, :nExtendedNormalMagnitudes, :nExtendedNormalValues) 
    @eval $F(x::T) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = $F(T)
end

# exponent field characterizations

expBiasedMin(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = 0
expBiasedMax(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = nExpValues(T) - 1
expBiasedValues(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = collect(expBiasedMin(T):expBiasedMax(T))

expUnbiasedMin(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = expBiasedMin(T) - expBias(T)
expUnbiasedMax(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = expBiasedMax(T) - expBias(T)
expUnbiasedValues(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = collect(expUnbiasedMin(T):expUnbiasedMax(T))[2:end]

expMaxValue(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = 2.0^(expUnbiasedMax(T))
expMinValue(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = 2.0^(expUnbiasedMin(T))
expValues(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = map(two_pow, expUnbiasedValues(T))

expBias(::Type{T}) where {Bits, SigBits, T<:AbsSignedFloat{Bits, SigBits}}   = 1 << (Bits - SigBits - 1) # floor(2^(Bits - SigBits - 1))
expBias(::Type{T}) where {Bits, SigBits, T<:AbsUnsignedFloat{Bits, SigBits}} = 1 << (Bits - SigBits)     # floor(2^(Bits - SigBits))

# cover instantiations

for F in (:expBias, :expMaxValue, :expMinValue, :expValues,
          :expUnbiasedMax, :expUnbiasedMin, :expUnbiasedValues)
    @eval $F(x::T) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = $F(T)
end

