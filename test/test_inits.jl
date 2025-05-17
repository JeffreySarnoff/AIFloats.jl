module TestInits

export aai4s, aai5s,
       auai4s, auai5s, asai4s, asai5s,
       aufai4s, aufai5s, asfai4s, asfai5s,
       aueai4s, aueai5s, aseai4s, aseai5s

using AIFloats, AlignedAllocs

aai41, aai42, aai43, aai44 =
    AbstractAIFloat{4, 1},
    AbstractAIFloat{4, 2},
    AbstractAIFloat{4, 3},
    AbstractAIFloat{4, 4};
aai51, aai52, aai53, aai54, aai55 =
    AbstractAIFloat{5, 1},
    AbstractAIFloat{5, 2},
    AbstractAIFloat{5, 3},
    AbstractAIFloat{5, 4},
    AbstractAIFloat{5, 5};

aai4s = [aai41, aai42, aai43, aai44];
aai5s = [aai51, aai52, aai53, aai54, aai55];

# Abs[Un|Signed]AIFloat{K,P}
auai41, auai42, auai43, auai44 =
    AbsUnsignedFloat{4, 1},
    AbsUnsignedFloat{4, 2},
    AbsUnsignedFloat{4, 3},
    AbsUnsignedFloat{4, 4};
auai51, auai52, auai53, auai54, auai55 =
    AbsUnsignedFloat{5, 1},
    AbsUnsignedFloat{5, 2},
    AbsUnsignedFloat{5, 3},
    AbsUnsignedFloat{5, 4},
    AbsUnsignedFloat{5, 5};
asai41, asai42, asai43, asai44 =
    AbsSignedFloat{4, 1},
    AbsSignedFloat{4, 2},
    AbsSignedFloat{4, 3},
    AbsSignedFloat{4, 4};
asai51, asai52, asai53, asai54, asai55 =
    AbsSignedFloat{5, 1},
    AbsSignedFloat{5, 2},
    AbsSignedFloat{5, 3},
    AbsSignedFloat{5, 4},
    AbsSignedFloat{5, 5};

auai4s = [auai41, auai42, auai43, auai44];
auai5s = [auai51, auai52, auai53, auai54, auai55];
asai4s = [asai41, asai42, asai43, asai44];
asai5s = [asai51, asai52, asai53, asai54, asai55];

# Abs[Un|Signed][Finite|Extended]AIFloat{K,P}

aufai41, aufai42, aufai43, aufai44 =
    AbsUnsignedFiniteFloat{4, 1},
    AbsUnsignedFiniteFloat{4, 2},
    AbsUnsignedFiniteFloat{4, 3},
    AbsUnsignedFiniteFloat{4, 4};
aufai51, aufai52, aufai53, aufai54, aufai55 =
    AbsUnsignedFiniteFloat{5, 1},
    AbsUnsignedFiniteFloat{5, 2},
    AbsUnsignedFiniteFloat{5, 3},
    AbsUnsignedFiniteFloat{5, 4},
    AbsUnsignedFiniteFloat{5, 5};
asfai41, asfai42, asfai43, asfai44 =
    AbsSignedFiniteFloat{4, 1},
    AbsSignedFiniteFloat{4, 2},
    AbsSignedFiniteFloat{4, 3},
    AbsSignedFiniteFloat{4, 4};
asfai51, asfai52, asfai53, asfai54, asfai55 =
    AbsSignedFiniteFloat{5, 1},
    AbsSignedFiniteFloat{5, 2},
    AbsSignedFiniteFloat{5, 3},
    AbsSignedFiniteFloat{5, 4},
    AbsSignedFiniteFloat{5, 5};

aufai4s = [aufai41, aufai42, aufai43, aufai44];
aufai5s = [aufai51, aufai52, aufai53, aufai54, aufai55];
asfai4s = [asfai41, asfai42, asfai43, asfai44];
asfai5s = [asfai51, asfai52, asfai53, asfai54, asfai55];

aueai41, aueai42, aueai43, aueai44 =
    AbsUnsignedExtendedFloat{4, 1},
    AbsUnsignedExtendedFloat{4, 2},
    AbsUnsignedExtendedFloat{4, 3},
    AbsUnsignedExtendedFloat{4, 4};
aueai51, aueai52, aueai53, aueai54, aueai55 =
    AbsUnsignedExtendedFloat{5, 1},
    AbsUnsignedExtendedFloat{5, 2},
    AbsUnsignedExtendedFloat{5, 3},
    AbsUnsignedExtendedFloat{5, 4},
    AbsUnsignedExtendedFloat{5, 5};
aseai41, aseai42, aseai43, aseai44 =
    AbsSignedExtendedFloat{4, 1},
    AbsSignedExtendedFloat{4, 2},
    AbsSignedExtendedFloat{4, 3},
    AbsSignedExtendedFloat{4, 4};
aseai51, aseai52, aseai53, aseai54, aseai55 =
    AbsSignedExtendedFloat{5, 1},
    AbsSignedExtendedFloat{5, 2},
    AbsSignedExtendedFloat{5, 3},
    AbsSignedExtendedFloat{5, 4},
    AbsSignedExtendedFloat{5, 5};

aueai4s = [aueai41, aueai42, aueai43, aueai44];
aueai5s = [aueai51, aueai52, aueai53, aueai54, aueai55];
aseai4s = [aseai41, aseai42, aseai43, aseai44];
aseai5s = [aseai51, aseai52, aseai53, aseai54, aseai55];

end # module TestInits
