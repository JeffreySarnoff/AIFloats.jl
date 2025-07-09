
# counts predicated on abstract [sub]type

nNaNs(@nospecialize(T::Type{<:AbstractAIFloat})) = 1
nZeros(@nospecialize(T::Type{<:AbstractAIFloat})) = 1

nInfs(@nospecialize(T::Type{<:AkoSignedFinite}))     = 0
nInfs(@nospecialize(T::Type{<:AkoUnsignedFinite}))   = 0
nInfs(@nospecialize(T::Type{<:AkoSignedExtended}))   = 2
nInfs(@nospecialize(T::Type{<:AkoUnsignedExtended})) = 1

nPosInfs(@nospecialize(T::Type{<:AbstractAIFloat}))  = (nInfs(T) + 1) >> 1
nNegInfs(@nospecialize(T::Type{<:AbstractSigned}))   = (nInfs(T) + 1) >> 1
nNegInfs(@nospecialize(T::Type{<:AbstractUnsigned})) = 0

# counts predicated on type defining parameters and type specifying qualities
# parameters: (bits, sigbits, exponent bias)
# qualities: (signedness [signed / unsigned], finiteness [finite / extended (has Inf[s])])

nBits(T::Type{<:AbstractAIFloat{Bits, SigBits}}) where {Bits, SigBits} = Bits
nSigBits(T::Type{<:AbstractAIFloat{Bits, SigBits}}) where {Bits, SigBits} = SigBits

nFracBits(@nospecialize(T::Type{<:AbstractAIFloat})) = nSigBits(T) - 1

nSignBits(@nospecialize(T::Type{<:AbstractSigned})) = 1
nSignBits(@nospecialize(T::Type{<:AbstractUnsigned})) = 0

nExpBits(@nospecialize(T::Type{<:AbstractSigned})) = nBits(T) - nSigBits(T)
nExpBits(@nospecialize(T::Type{<:AbstractUnsigned})) = nBits(T) - nSigBits(T) + 1

nMagnitudes(T::Type{<:AbstractUnsigned}) = 2^(nBits(T)) - 1
nMagnitudes(T::Type{<:AbstractSigned})   = 2^(nBits(T)  - 1)

nFiniteMagnitudes(T::Type{<:AbstractAIFloat}) = nMagnitudes(T) - nInfs(T)
nNonzeroMagnitudes(T::Type{<:AbstractAIFloat}) = nMagnitudes(T) - nZeros(T)
nNonzeroFiniteMagnitudes(T::Type{<:AbstractAIFloat}) = nFiniteMagnitudes(T) - nZeros(T)

nValues(T::Type{<:AbstractAIFloat}) = 2^nBits(T)

nNumericValues(T::Type{<:AbstractAIFloat}) = nValues(T) - nNaNs(T)
nNonzeroNumericValues(T::Type{<:AbstractAIFloat}) = nNumericValues(T) - nZeros(T)
nFiniteValues(T::Type{<:AbstractAIFloat}) = nNumericValues(T) - nInfs(T)
nNonzeroFiniteValues(T::Type{<:AbstractAIFloat}) = nFiniteValues(T) - nZeros(T)

#--->

nSigMagnitudes(T::Type{<:AbstractAIFloat}) = 1 << nSigBits(T)
nNonzeroSigMagnitudes(T::Type{<:AbstractAIFloat}) = nSigMagnitudes(T) - 1

nFracMagnitudes(T::Type{<:AbstractAIFloat}) = 1 << nFracBits(T)
nNonzeroFracMagnitudes(T::Type{<:AbstractAIFloat}) = nFracMagnitudes(T) - 1

nExpValues(T::Type{<:AbstractAIFloat}) = 1 << nExpBits(T)
nNonzeroExpValues(T::Type{<:AbstractAIFloat}) = nExpValues(T) - 1

nNonnegValues(T::Type{<:AbstractAIFloat}) = nMagnitudes(T)
nPositiveValues(T::Type{<:AbstractAIFloat}) = nNonnegValues(T) - 1
nNegativeValues(T::Type{<:AbstractAIFloat}) = nNumericValues(T) - nNonnegValues(T)

nFiniteNonnegValues(T::Type{<:AbstractAIFloat}) = nNonnegValues(T) - nPosInfs(T)
nFinitePositiveValues(T::Type{<:AbstractAIFloat}) = nPositiveValues(T) - nPosInfs(T)
nFiniteNegativeValues(T::Type{<:AbstractAIFloat}) = nNegativeValues(T) - nNegInfs(T)

nPrenormalMagnitudes(T::Type{<:AbstractAIFloat}) = 2^(nSigBits(T)-1) # 1 << (SigBits - 1)
nSubnormalMagnitudes(T::Type{<:AbstractAIFloat}) = nPrenormalMagnitudes(T) - 1

nPrenormalValues(::Type{T}) where {Bits, SigBits, T<:AbstractSigned{Bits, SigBits}} = 2 * nPrenormalMagnitudes(T) - 1
nPrenormalValues(::Type{T}) where {Bits, SigBits, T<:AbstractUnsigned{Bits, SigBits}} = nPrenormalMagnitudes(T)

nSubnormalValues(T::Type{<:AbstractAIFloat}) = nPrenormalValues(T) - 1

nNormalMagnitudes(T::Type{<:AbstractAIFloat}) = nFiniteMagnitudes(T) - nPrenormalMagnitudes(T)
nNormalValues(T::Type{<:AbstractAIFloat}) = nFiniteValues(T) - nPrenormalValues(T)

nExtendedNormalMagnitudes(T::Type{<:AbstractAIFloat}) =
    nNormalMagnitudes(T) + nPosInfs(T)

nExtendedNormalValues(T::Type{<:AbstractAIFloat}) =
    nNormalMagnitudes(T) + nInfs(T)

# support for instantiations
for F in (:nBits, :nSigBits, :nFracBits, :nExpBits, :nSignBits,
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
