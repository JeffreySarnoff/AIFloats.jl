
# primitive aspects

nZeros(Bits, SigBits) = 1
nNaNs(Bits, SigBits) = 1

nBits(Bits, SigBits)= Bits
nSigBits(Bits, SigBits) = SigBits
nFracBits(Bits, SigBits) = SigBits - oftype(SigBits, 1)
nExpBits(Bits, SigBits, isSigned) = (Bits - SigBits) + (oftype(SigBits, 0) + !isSigned)
nSignBits(Bits, SigBits, isSigned) = oftype(SigBits, 0) + isSigned

nValues(Bits, SigBits) = 2^Bits
nNumericValues(Bits, SigBits) = nValues(Bits, SigBits) - 1 # remove NaN
nNonzeroNumericValues(Bits, SigBits) = nNumericValues(Bits, SigBits) - 1 # remove Zero

nNonnegNumericValues(Bits, SigBits, isSigned) = nNumericValues(Bits, SigBits) >> (0 + isSigned) # + isodd(nNumericValues)
nPositiveValues(Bits, SigBits, isSigned) = nNonnegNumericValues(Bits, SigBits, isSigned) - 1 # remove Zero
nNegativeValues(Bits, SigBits, isSigned) = isSigned * nPositiveValues(Bits, SigBits, isSigned)

nMagnitudes(Bits, SigBits, isSigned) = nNonnegNumericValues(Bits, SigBits, isSigned)
nNonzeroMagnitudes(Bits, SigBits, isSigned) = nMagnitudes(Bits, SigBits, isSigned) - 1
nFracMagnitudes(Bits, SigBits) = 2^nFracBits(Bits, SigBits)
nNonzeroFracMagnitudes(Bits, SigBits) = nFracMagnitudes(Bits, SigBits) - 1

nFiniteValues(Bits, SigBits, isSigned, isExtended) = nNumericValues(Bits, SigBits) - nInfs(Bits, SigBits, isSigned, isExtended)
nPositiveFiniteValues(Bits, SigBits, isSigned, isExtended) = nFiniteValues(Bits, SigBits, isSigned, isExtended) >> (0 + isSigned)
nNegativeFiniteValues(Bits, SigBits, isSigned, isExtended) = isSigned * nPositiveFiniteValues(Bits, SigBits, isSigned, isExtended)


nInfs(Bits, SigBits, isSigned, isExtended) = nInfs(Val(isSigned), Val(isExtended))
nPosInfs(Bits, SigBits, isSigned, isExtended) = nPosInfs(Val(isSigned), Val(isExtended))
nNegInfs(Bits, SigBits, isSigned, isExtended) = nNegInfs(Val(isSigned), Val(isExtended))

nInfs(isSigned::Val{IsUnsigned}, isExtended::Val{IsFinite}) = 0
nInfs(isSigned::Val{IsSigned}, isExtended::Val{IsFinite}) = 0
nInfs(isSigned::Val{IsUnsigned}, isExtended::Val{IsExtended}) = 1
nInfs(isSigned::Val{IsSigned}, isExtended::Val{IsExtended}) = 2

nPosInfs(isSigned::Val{IsUnsigned}, isExtended::Val{IsFinite}) = 0
nPosInfs(isSigned::Val{IsSigned}, isExtended::Val{IsFinite}) = 0
nPosInfs(isSigned::Val{IsUnsigned}, isExtended::Val{IsExtended}) = 1
nPosInfs(isSigned::Val{IsSigned}, isExtended::Val{IsExtended}) = 1

nNegInfs(isSigned::Val{IsUnsigned}, isExtended::Val{IsFinite}) = 0
nNegInfs(isSigned::Val{IsSigned}, isExtended::Val{IsFinite}) = 0
nNegInfs(isSigned::Val{IsUnsigned}, isExtended::Val{IsExtended}) = 1
nNegInfs(isSigned::Val{IsSigned}, isExtended::Val{IsExtended}) = 1
