using FloatsForML, Test

# AbstractAIFloat{K,P}
aai41, aai42, aai43, aai44 =
   AbstractAIFloat{4,1}, AbstractAIFloat{4,2}, AbstractAIFloat{4,3}, AbstractAIFloat{4,4};
aai51, aai52, aai53, aai54, aai55 =
   AbstractAIFloat{5,1}, AbstractAIFloat{5,2}, AbstractAIFloat{5,3}, AbstractAIFloat{5,4}, AbstractAIFloat{5,5};

# Abstract[Un|Signed]AIFloat{K,P}
auai41, auai42, auai43, auai44 =
   AbstractUnsignedAIFloat{4,1}, AbstractUnsignedAIFloat{4,2}, AbstractUnsignedAIFloat{4,3}, AbstractUnsignedAIFloat{4,4};
auai51, auai52, auai53, auai54, auai55 =
   AbstractUnsignedAIFloat{5,1}, AbstractUnsignedAIFloat{5,2}, AbstractUnsignedAIFloat{5,3}, AbstractUnsignedAIFloat{5,4}, AbstractUnsignedAIFloat{5,5};
asai41, asai42, asai43, asai44 =
   AbstractSignedAIFloat{4,1}, AbstractSignedAIFloat{4,2}, AbstractSignedAIFloat{4,3}, AbstractSignedAIFloat{4,4};
asai51, asai52, asai53, asai54, asai55 =
   AbstractSignedAIFloat{5,1}, AbstractSignedAIFloat{5,2}, AbstractSignedAIFloat{5,3}, AbstractSignedAIFloat{5,4}, AbstractSignedAIFloat{5,5};

# Abstract[Un|Signed][Finite|Extended]AIFloat{K,P}

aufai41, aufai42, aufai43, aufai44 =
    AbstractUnsignedFiniteAIFloat{4,1}, AbstractUnsignedFiniteAIFloat{4,2}, AbstractUnsignedFiniteAIFloat{4,3}, AbstractUnsignedFiniteAIFloat{4,4};
aufai51, aufai52, aufai53, aufai54, aufai55 =
    AbstractUnsignedFiniteAIFloat{5,1}, AbstractUnsignedFiniteAIFloat{5,2}, AbstractUnsignedFiniteAIFloat{5,3}, AbstractUnsignedFiniteAIFloat{5,4}, AbstractUnsignedFiniteAIFloat{5,5};
asfai41, asfai42, asfai43, asfai44 =
    AbstractSignedFiniteAIFloat{4,1}, AbstractSignedFiniteAIFloat{4,2}, AbstractSignedFiniteAIFloat{4,3}, AbstractSignedFiniteAIFloat{4,4};
asfai51, asfai52, asfai53, asfai54, asfai55 =
    AbstractSignedFiniteAIFloat{5,1}, AbstractSignedFiniteAIFloat{5,2}, AbstractSignedFiniteAIFloat{5,3}, AbstractSignedFiniteAIFloat{5,4}, AbstractSignedFiniteAIFloat{5,5};

aueai41, aueai42, aueai43, aueai44 =
    AbstractUnsignedExtendedAIFloat{4,1}, AbstractUnsignedExtendedAIFloat{4,2}, AbstractUnsignedExtendedAIFloat{4,3}, AbstractUnsignedExtendedAIFloat{4,4};
aueai51, aueai52, aueai53, aueai54, aueai55 =
    AbstractUnsignedExtendedAIFloat{5,1}, AbstractUnsignedExtendedAIFloat{5,2}, AbstractUnsignedExtendedAIFloat{5,3}, AbstractUnsignedExtendedAIFloat{5,4}, AbstractUnsignedExtendedAIFloat{5,5};
aseai41, aseai42, aseai43, aseai44 =
    AbstractSignedExtendedAIFloat{4,1}, AbstractSignedExtendedAIFloat{4,2}, AbstractSignedExtendedAIFloat{4,3}, AbstractSignedExtendedAIFloat{4,4};
aseai51, aseai52, aseai53, aseai54, aseai55 =
    AbstractSignedExtendedAIFloat{5,1}, AbstractSignedExtendedAIFloat{5,2}, AbstractSignedExtendedAIFloat{5,3}, AbstractSignedExtendedAIFloat{5,4}, AbstractSignedExtendedAIFloat{5,5};
