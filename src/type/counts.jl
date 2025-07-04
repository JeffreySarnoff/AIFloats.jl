
# counts predicated on abstract [sub]type

nNaNs(@nospecialize(T::Type{<:AbstractAIFloat})) = 1
nZeros(@nospecialize(T::Type{<:AbstractAIFloat})) = 1

nInfs(@nospecialize(T::Type{<:AbsSignedFiniteFloat}))     = 0
nInfs(@nospecialize(T::Type{<:AbsUnsignedFiniteFloat}))   = 0
nInfs(@nospecialize(T::Type{<:AbsSignedExtendedFloat}))   = 2
nInfs(@nospecialize(T::Type{<:AbsUnsignedExtendedFloat})) = 1

nPosInfs(@nospecialize(T::Type{<:AbstractAIFloat}))  = (nInfs(T) + 1) >> 1
nNegInfs(@nospecialize(T::Type{<:AbsSignedFloat}))   = (nInfs(T) + 1) >> 1
nNegInfs(@nospecialize(T::Type{<:AbsUnsignedFloat})) = 0

# counts predicated on type defining parameters and type specifying qualities
# parameters: (bits, sigbits, exponent bias)
# qualities: (signedness [signed / unsigned], finiteness [finite / extended (has Inf[s])])

nBits(::Type{T<:AbstractAIFloat{Bits, SigBits}}) where {Bits, SigBits} = Bits
nSigBits(::Type{T<:AbstractAIFloat{Bits, SigBits}}) where {Bits, SigBits} = SigBits

nFracBits(@nospecialize(T::Type{<:AbstractAIFloat})) = nSigBits(T) - 1

nSignBits(@nospecialize(T::Type{<:AbsSignedFloat})) = 1
nSignBits(@nospecialize(T::Type{<:AbsUnsignedFloat})) = 0

nExpBits(@nospecialize(T::Type{<:AbsSignedFloat})) = nBits(T) - nSigBits(T)
nExpBits(@nospecialize(T::Type{<:AbsUnsignedFloat})) = nBits(T) - nSigBits(T) + 1

nMagnitudes(T::Type{<:AbsUnsignedFloat}) = 2^(nBits(T)) - 1
nMagnitudes(T::Type{<:AbsSignedFloat})   = 2^(nBits(T)  - 1)

nFiniteMagnitudes(T::Type{<:AbsUnsignedFiniteFloat}) = nMagnitudes(T) - nInfs(T)
nNonzeroMagnitudes(T::Type{<:AbsUnsignedFiniteFloat}) = nMagnitudes(T) - nZeros(T)
nNonzeroFiniteMagnitudes(T::Type{<:AbsUnsignedFiniteFloat}) = nFiniteMagnitudes(T) - nZeros(T)

nValues(T::Type{<:AbstractAIFloat}) = 2^nBits(T)
nNumericValues(T::Type{<:AbstractAIFloat}) = nValues(T) - nNans(T)
nNonzeroNumericValues(T::Type{<:AbstractAIFloat}) = nNumericValues(T) - nZeros(T)
nFiniteNumericValues(T::Type{<:AbstractAIFloat}) = nNumericValues(T) - nInfs(T)
nNonzeroFiniteNumericValues(T::Type{<:AbstractAIFloat}) = nFiniteNumericValues(T) - nZeros(T)

#--->

nSigMagnitudes(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = 1 << nSigBits(T)
nNonzeroSigMagnitudes(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = nSigMagnitudes(T) - 1

nFracMagnitudes(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = 1 << nFracBits(T)
nNonzeroFracMagnitudes(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = nFracMagnitudes(T) - 1

nExpValues(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = 1 << nExpBits(T)
nNonzeroExpValues(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = nExpValues(T) - 1

nNonnegValues(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = nMagnitudes(T)
nPositiveValues(::Type{T}) where {Bits, SigBits, T<:AbsSignedFloat{Bits, SigBits}} = nNonnegValues(T) - 1
nNegativeValues(::Type{T}) where {Bits, SigBits, T<:AbsSignedFloat{Bits, SigBits}} = nNumericValues(T) - nNonnegValues(T)

nFiniteNonnegValues(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = nNonnegValues(T) - nPosInfs(T)
nFinitePositiveValues(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = nPositiveValues(T) - nPosInfs(T)
nFiniteNegativeValues(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = nNegativeValues(T) - nNegInfs(T)

nPrenormalMagnitudes(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = 2^(SigBits-1) # 1 << (SigBits - 1)
nSubnormalMagnitudes(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = nPrenormalMagnitudes(T) - 1

nPrenormalValues(::Type{T}) where {Bits, SigBits, T<:AbsSignedFloat{Bits, SigBits}} = 2 * nPrenormalMagnitudes(T) - 1
nPrenormalValues(::Type{T}) where {Bits, SigBits, T<:AbsUnsignedFloat{Bits, SigBits}} = nPrenormalMagnitudes(T)

nSubnormalValues(::Type{T}) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = nPrenormalValues(T) - 1

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
