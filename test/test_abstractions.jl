using FloatsForML, Test

# AbstractAIFloat{K,P}
aai41, aai42, aai43, aai44 =
   AbstractAIFloat{4,1}, AbstractAIFloat{4,2}, AbstractAIFloat{4,3}, AbstractAIFloat{4,4};
aai51, aai52, aai53, aai54, aai55 =
   AbstractAIFloat{5,1}, AbstractAIFloat{5,2}, AbstractAIFloat{5,3}, AbstractAIFloat{5,4}, AbstractAIFloat{5,5};

aai4s = [aai41, aai42, aai43, aai44];
aai5s = [aai51, aai52, aai53, aai54, aai55];

# Abs[Un|Signed]AIFloat{K,P}
auai41, auai42, auai43, auai44 =
   AbsUnsignedAIFloat{4,1}, AbsUnsignedAIFloat{4,2}, AbsUnsignedAIFloat{4,3}, AbsUnsignedAIFloat{4,4};
auai51, auai52, auai53, auai54, auai55 =
   AbsUnsignedAIFloat{5,1}, AbsUnsignedAIFloat{5,2}, AbsUnsignedAIFloat{5,3}, AbsUnsignedAIFloat{5,4}, AbsUnsignedAIFloat{5,5};
asai41, asai42, asai43, asai44 =
   AbsSignedAIFloat{4,1}, AbsSignedAIFloat{4,2}, AbsSignedAIFloat{4,3}, AbsSignedAIFloat{4,4};
asai51, asai52, asai53, asai54, asai55 =
   AbsSignedAIFloat{5,1}, AbsSignedAIFloat{5,2}, AbsSignedAIFloat{5,3}, AbsSignedAIFloat{5,4}, AbsSignedAIFloat{5,5};

auai4s = [auai41, auai42, auai43, auai44];
auai5s = [auai51, auai52, auai53, auai54, auai55];
asai4s = [asai41, asai42, asai43, asai44];
asai5s = [asai51, asai52, asai53, asai54, asai55];

# Abs[Un|Signed][Finite|Extended]AIFloat{K,P}

aufai41, aufai42, aufai43, aufai44 =
    AbsUnsignedFiniteAIFloat{4,1}, AbsUnsignedFiniteAIFloat{4,2}, AbsUnsignedFiniteAIFloat{4,3}, AbsUnsignedFiniteAIFloat{4,4};
aufai51, aufai52, aufai53, aufai54, aufai55 =
    AbsUnsignedFiniteAIFloat{5,1}, AbsUnsignedFiniteAIFloat{5,2}, AbsUnsignedFiniteAIFloat{5,3}, AbsUnsignedFiniteAIFloat{5,4}, AbsUnsignedFiniteAIFloat{5,5};
asfai41, asfai42, asfai43, asfai44 =
    AbsSignedFiniteAIFloat{4,1}, AbsSignedFiniteAIFloat{4,2}, AbsSignedFiniteAIFloat{4,3}, AbsSignedFiniteAIFloat{4,4};
asfai51, asfai52, asfai53, asfai54, asfai55 =
    AbsSignedFiniteAIFloat{5,1}, AbsSignedFiniteAIFloat{5,2}, AbsSignedFiniteAIFloat{5,3}, AbsSignedFiniteAIFloat{5,4}, AbsSignedFiniteAIFloat{5,5};

aufai4s = [aufai41, aufai42, aufai43, aufai44];
aufai5s = [aufai51, aufai52, aufai53, aufai54, aufai55];
asfai4s = [asfai41, asfai42, asfai43, asfai44];
asfai5s = [asfai51, asfai52, asfai53, asfai54, asfai55];

aueai41, aueai42, aueai43, aueai44 =
    AbsUnsignedExtendedAIFloat{4,1}, AbsUnsignedExtendedAIFloat{4,2}, AbsUnsignedExtendedAIFloat{4,3}, AbsUnsignedExtendedAIFloat{4,4};
aueai51, aueai52, aueai53, aueai54, aueai55 =
    AbsUnsignedExtendedAIFloat{5,1}, AbsUnsignedExtendedAIFloat{5,2}, AbsUnsignedExtendedAIFloat{5,3}, AbsUnsignedExtendedAIFloat{5,4}, AbsUnsignedExtendedAIFloat{5,5};
aseai41, aseai42, aseai43, aseai44 =
    AbsSignedExtendedAIFloat{4,1}, AbsSignedExtendedAIFloat{4,2}, AbsSignedExtendedAIFloat{4,3}, AbsSignedExtendedAIFloat{4,4};
aseai51, aseai52, aseai53, aseai54, aseai55 =
    AbsSignedExtendedAIFloat{5,1}, AbsSignedExtendedAIFloat{5,2}, AbsSignedExtendedAIFloat{5,3}, AbsSignedExtendedAIFloat{5,4}, AbsSignedExtendedAIFloat{5,5};

aueai4s = [aueai41, aueai42, aueai43, aueai44];
aueai5s = [aueai51, aueai52, aueai53, aueai54, aueai55];
aseai4s = [aseai41, aseai42, aseai43, aseai44];
aseai5s = [aseai51, aseai52, aseai53, aseai54, aseai55];

# AbstractAIFloats

@testset "AbstractAIFloat{4,_}" begin
    for T in aai4s
        bits = T.parameters[1]
        sigbits = T.parameters[2]

        @test nBits(T) == bits
        @test nSigBits(T) == sigbits
        @test nFracBits(T) == sigbits - 1
        @test nValues(T) == 2^bits
        @test nNumericValues(T) == nValues(T) - 1
        @test nNonzeroNumericValues(T) == nNumericValues(T) - 1
        @test nFracMagnitudes(T) == 2^nFracBits(T)
        @test nNonzeroFracMagnitudes(T) == nFracMagnitudes(T) - 1
    end
end

@testset "AbstractAIFloat{5,_}" begin
    for T in aai5s
        bits = T.parameters[1]
        sigbits = T.parameters[2]

        @test nBits(T) == bits
        @test nSigBits(T) == sigbits
        @test nFracBits(T) == sigbits - 1
        @test nValues(T) == 2^bits
        @test nNumericValues(T) == nValues(T) - 1
        @test nNonzeroNumericValues(T) == nNumericValues(T) - 1
        @test nFracMagnitudes(T) == 2^nFracBits(T)
        @test nNonzeroFracMagnitudes(T) == nFracMagnitudes(T) - 1
    end
end

 @testset "Abs[Unsigned|Signed]AIFloat{4,_}" begin
    for T in vcat(auai4s, asai4s)
        bits = T.parameters[1]
        sigbits = T.parameters[2]
        isSigned = is_signed(T)
        isUnsigned = is_unsigned(T)

        @test nSignBits(T) == isSigned ? 1 : 0
        @test nExpBits(T) == isUnsigned ? 0 : 1
        @test nMagnitudes(T) == isUnsigned ? nNumericValues(T) : nValues(T) >> 1
        @test nNonzeroMagnitudes(T) == nMagnitudes(T) - 1
        @test nPositiveValues(T) == nNonzeroMagnitudes(T)
        @test nNegativeValues(T) == isUnsigned ? 0 : nPositiveValues(T)
        @test nExpValues(T) == 2^nExpBits(T)
        @test nNonzeroExpValues(T) == nExpValues(T) - 1
    end
end

@testset "Abs[Unsigned|Signed]AIFloat{5,_}" begin
    for T in vcat(auai5s, asai5s)
        bits = T.parameters[1]
        sigbits = T.parameters[2]
        isSigned = is_signed(T)
        isUnsigned = is_unsigned(T)

        @test nSignBits(T) == isSigned ? 1 : 0
        @test nExpBits(T) == isUnsigned ? 0 : 1
        @test nMagnitudes(T) == isUnsigned ? nNumericValues(T) : nValues(T) >> 1
        @test nNonzeroMagnitudes(T) == nMagnitudes(T) - 1
        @test nPositiveValues(T) == nNonzeroMagnitudes(T)
        @test nNegativeValues(T) == isUnsigned ? 0 : nPositiveValues(T)
        @test nExpValues(T) == 2^nExpBits(T)
        @test nNonzeroExpValues(T) == nExpValues(T) - 1
    end
end

@testset "AbsUnsigned[Finite|Extended]AIFloat{4,_}" begin
    for T in vcat(aufai4s, aueai4s)
        bits = T.parameters[1]
        sigbits = T.parameters[2]
        isSigned = is_signed(T)
        isUnsigned = is_unsigned(T)
        isFinite = is_finite(T)
        isExtended = is_extended(T)

        @test nInfs(T) == isExtended ? isSigned ? 2 : 1 : 0
        @test nPosInfs(T) == isExtended ? 1 : 0
        @test nNegInfs(T) == isExtended ? isSigned ? 1 : 0 : 0
        @test nFiniteValues(T) == nNumericValues(T) - nInfs(T)
        @test nPositiveFiniteValues(T) == isUnsigned ? nFiniteValues(T) - 1 : nFiniteValues(T) >> 1
        @test nNegativeFiniteValues(T) == isUnsigned ? 0 : nPositiveFiniteValues(T)
    end
end

@testset "AbsUnsigned[Finite|Extended]AIFloat{5,_}" begin
    for T in vcat(aufai5s, aueai5s)
        bits = T.parameters[1]
        sigbits = T.parameters[2]
        isSigned = is_signed(T)
        isUnsigned = is_unsigned(T)
        isFinite = is_finite(T)
        isExtended = is_extended(T)

        @test nInfs(T) == isExtended ? isSigned ? 2 : 1 : 0
        @test nPosInfs(T) == isExtended ? 1 : 0
        @test nNegInfs(T) == isExtended ? isSigned ? 1 : 0 : 0
        @test nFiniteValues(T) == nNumericValues(T) - nInfs(T)
        @test nPositiveFiniteValues(T) == isUnsigned ? nFiniteValues(T) - 1 : nFiniteValues(T) >> 1
        @test nNegativeFiniteValues(T) == isUnsigned ? 0 : nPositiveFiniteValues(T)
    end
end

@testset "AbsSigned[Finite|Extended]AIFloat{4,_}" begin
    for T in vcat(asfai4s, aseai4s)
        bits = T.parameters[1]
        sigbits = T.parameters[2]
        isSigned = is_signed(T)
        isUnsigned = is_unsigned(T)
        isFinite = is_finite(T)
        isExtended = is_extended(T)

        @test nInfs(T) == isExtended ? isSigned ? 2 : 1 : 0
        @test nPosInfs(T) == isExtended ? 1 : 0
        @test nNegInfs(T) == isExtended ? isSigned ? 1 : 0 : 0
        @test nFiniteValues(T) == nNumericValues(T) - nInfs(T)
        @test nPositiveFiniteValues(T) == isUnsigned ? nFiniteValues(T) - 1 : nFiniteValues(T) >> 1
        @test nNegativeFiniteValues(T) == isUnsigned ? 0 : nPositiveFiniteValues(T)
    end
end


@testset "AbsSigned[Finite|Extended]AIFloat{5,_}" begin
    for T in vcat(asfai5s, aseai5s)
        bits = T.parameters[1]
        sigbits = T.parameters[2]
        isSigned = is_signed(T)
        isUnsigned = is_unsigned(T)
        isFinite = is_finite(T)
        isExtended = is_extended(T)

        @test nInfs(T) == isExtended ? isSigned ? 2 : 1 : 0
        @test nPosInfs(T) == isExtended ? 1 : 0
        @test nNegInfs(T) == isExtended ? isSigned ? 1 : 0 : 0
        @test nFiniteValues(T) == nNumericValues(T) - nInfs(T)
        @test nPositiveFiniteValues(T) == isUnsigned ? nFiniteValues(T) - 1 : nFiniteValues(T) >> 1
        @test nNegativeFiniteValues(T) == isUnsigned ? 0 : nPositiveFiniteValues(T)
    end
end
