
uf21, uf22  = collect(UnsignedFiniteFloat(2,i) for i=1:2);
uf31, uf32, uf33  = collect(UnsignedFiniteFloat(3,i) for i=1:3);
uf41, uf42, uf43, uf44  = collect(UnsignedFiniteFloat(4,i) for i=1:4);
uf51, uf52, uf53, uf54, uf55  = collect(UnsignedFiniteFloat(5,i) for i=1:5);
uf61, uf62, uf63, uf64, uf65, uf66  = collect(UnsignedFiniteFloat(6,i) for i=1:6);
uf71, uf72, uf73, uf74, uf75, uf76, uf77  = collect(UnsignedFiniteFloat(7,i) for i=1:7);
uf81, uf82, uf83, uf84, uf85, uf86, uf87, uf88  = collect(UnsignedFiniteFloat(8,i) for i=1:8);
uf91, uf92, uf93, uf94, uf95, uf96, uf97, uf98, uf99  = collect(UnsignedFiniteFloat(9,i) for i=1:9);
ufA1, ufA2, ufA3, ufA4, ufA5, ufA6, ufA7, ufA8, ufA9, ufAA  = collect(UnsignedFiniteFloat(10,i) for i=1:10);
ufB1, ufB2, ufB3, ufB4, ufB5, ufB6, ufB7, ufB8, ufB9, ufBA, ufBB  = collect(UnsignedFiniteFloat(11,i) for i=1:11);
ufC1, ufC2, ufC3, ufC4, ufC5, ufC6, ufC7, ufC8, ufC9, ufCA, ufCB, ufCC  = collect(UnsignedFiniteFloat(12,i) for i=1:12);
ufD1, ufD2, ufD3, ufD4, ufD5, ufD6, ufD7, ufD8, ufD9, ufDA, ufDB, ufDC, ufDD  = collect(UnsignedFiniteFloat(13,i) for i=1:13);
ufE1, ufE2, ufE3, ufE4, ufE5, ufE6, ufE7, ufE8, ufE9, ufEA, ufEB, ufEC, ufED, ufEE  = collect(UnsignedFiniteFloat(14,i) for i=1:14);
ufF1, ufF2, ufF3, ufF4, ufF5, ufF6, ufF7, ufF8, ufF9, ufFA, ufFB, ufFC, ufFD, ufFE, ufFF  = collect(UnsignedFiniteFloat(15,i) for i=1:15);
# ufG1, ufG2, ufG3, ufG4, ufG5, ufG6, ufG7, ufG8, ufG9, ufGA, ufGB, ufGC, ufGD, ufGE, ufGF, ufGG  = collect(UnsignedFiniteFloat(16,i) for i=1:16);
ufG2, ufG3, ufG4, ufG5, ufG6, ufG7, ufG8, ufG9, ufGA, ufGB, ufGC, ufGD, ufGE, ufGF, ufGG  = collect(UnsignedFiniteFloat(16,i) for i=2:16);

ue21, ue22  = collect(UnsignedExtendedFloat(2,i) for i=1:2);
ue31, ue32, ue33  = collect(UnsignedExtendedFloat(3,i) for i=1:3);
ue41, ue42, ue43, ue44  = collect(UnsignedExtendedFloat(4,i) for i=1:4);
ue51, ue52, ue53, ue54, ue55  = collect(UnsignedExtendedFloat(5,i) for i=1:5);
ue61, ue62, ue63, ue64, ue65, ue66  = collect(UnsignedExtendedFloat(6,i) for i=1:6);
ue71, ue72, ue73, ue74, ue75, ue76, ue77  = collect(UnsignedExtendedFloat(7,i) for i=1:7);
ue81, ue82, ue83, ue84, ue85, ue86, ue87, ue88  = collect(UnsignedExtendedFloat(8,i) for i=1:8);
ue91, ue92, ue93, ue94, ue95, ue96, ue97, ue98, ue99  = collect(UnsignedExtendedFloat(9,i) for i=1:9);
ueA1, ueA2, ueA3, ueA4, ueA5, ueA6, ueA7, ueA8, ueA9, ueAA  = collect(UnsignedExtendedFloat(10,i) for i=1:10);
ueB1, ueB2, ueB3, ueB4, ueB5, ueB6, ueB7, ueB8, ueB9, ueBA, ueBB  = collect(UnsignedExtendedFloat(11,i) for i=1:11);
ueC1, ueC2, ueC3, ueC4, ueC5, ueC6, ueC7, ueC8, ueC9, ueCA, ueCB, ueCC  = collect(UnsignedExtendedFloat(12,i) for i=1:12);
ueD1, ueD2, ueD3, ueD4, ueD5, ueD6, ueD7, ueD8, ueD9, ueDA, ueDB, ueDC, ueDD  = collect(UnsignedExtendedFloat(13,i) for i=1:13);
ueE1, ueE2, ueE3, ueE4, ueE5, ueE6, ueE7, ueE8, ueE9, ueEA, ueEB, ueEC, ueED, ueEE  = collect(UnsignedExtendedFloat(14,i) for i=1:14);
ueF1, ueF2, ueF3, ueF4, ueF5, ueF6, ueF7, ueF8, ueF9, ueFA, ueFB, ueFC, ueFD, ueFE, ueFF  = collect(UnsignedExtendedFloat(15,i) for i=1:15);
ueG2, ueG3, ueG4, ueG5, ueG6, ueG7, ueG8, ueG9, ueGA, ueGB, ueGC, ueGD, ueGE, ueGF, ueGG  = collect(UnsignedExtendedFloat(16,i) for i=2:16);


sf21  = collect(SignedFiniteFloat(2,i) for i=1:1);
sf31, sf32  = collect(SignedFiniteFloat(3,i) for i=1:2);
sf41, sf42, sf43  = collect(SignedFiniteFloat(4,i) for i=1:3);
sf51, sf52, sf53, sf54  = collect(SignedFiniteFloat(5,i) for i=1:4);
sf61, sf62, sf63, sf64, sf65  = collect(SignedFiniteFloat(6,i) for i=1:5);
sf71, sf72, sf73, sf74, sf75, sf76  = collect(SignedFiniteFloat(7,i) for i=1:6);
sf81, sf82, sf83, sf84, sf85, sf86, sf87  = collect(SignedFiniteFloat(8,i) for i=1:7);
sf91, sf92, sf93, sf94, sf95, sf96, sf97, sf98  = collect(SignedFiniteFloat(9,i) for i=1:8);
sfA1, sfA2, sfA3, sfA4, sfA5, sfA6, sfA7, sfA8, sfA9  = collect(SignedFiniteFloat(10,i) for i=1:9);
sfB1, sfB2, sfB3, sfB4, sfB5, sfB6, sfB7, sfB8, sfB9, sfBA  = collect(SignedFiniteFloat(11,i) for i=1:10);
sfC1, sfC2, sfC3, sfC4, sfC5, sfC6, sfC7, sfC8, sfC9, sfCA, sfCB  = collect(SignedFiniteFloat(12,i) for i=1:11);
sfD1, sfD2, sfD3, sfD4, sfD5, sfD6, sfD7, sfD8, sfD9, sfDA, sfDB, sfDC  = collect(SignedFiniteFloat(13,i) for i=1:12);
sfE1, sfE2, sfE3, sfE4, sfE5, sfE6, sfE7, sfE8, sfE9, sfEA, sfEB, sfEC, sfED  = collect(SignedFiniteFloat(14,i) for i=1:13);
sfF1, sfF2, sfF3, sfF4, sfF5, sfF6, sfF7, sfF8, sfF9, sfFA, sfFB, sfFC, sfFD, sfFE  = collect(SignedFiniteFloat(15,i) for i=1:14);
sfG1, sfG2, sfG3, sfG4, sfG5, sfG6, sfG7, sfG8, sfG9, sfGA, sfGB, sfGC, sfGD, sfGE, sfGF  = collect(SignedFiniteFloat(16,i) for i=1:15);

se21  = collect(SignedExtendedFloat(2,i) for i=1:1);
se31, se32  = collect(SignedExtendedFloat(3,i) for i=1:2);
se41, se42, se43  = collect(SignedExtendedFloat(4,i) for i=1:3);
se51, se52, se53, se54  = collect(SignedExtendedFloat(5,i) for i=1:4);
se61, se62, se63, se64, se65  = collect(SignedExtendedFloat(6,i) for i=1:5);
se71, se72, se73, se74, se75, se76  = collect(SignedExtendedFloat(7,i) for i=1:6);
se81, se82, se83, se84, se85, se86, se87  = collect(SignedExtendedFloat(8,i) for i=1:7);
se91, se92, se93, se94, se95, se96, se97, se98  = collect(SignedExtendedFloat(9,i) for i=1:8);
seA1, seA2, seA3, seA4, seA5, seA6, seA7, seA8, seA9  = collect(SignedExtendedFloat(10,i) for i=1:9);
seB1, seB2, seB3, seB4, seB5, seB6, seB7, seB8, seB9, seBA  = collect(SignedExtendedFloat(11,i) for i=1:10);
seC1, seC2, seC3, seC4, seC5, seC6, seC7, seC8, seC9, seCA, seCB  = collect(SignedExtendedFloat(12,i) for i=1:11);
seD1, seD2, seD3, seD4, seD5, seD6, seD7, seD8, seD9, seDA, seDB, seDC  = collect(SignedExtendedFloat(13,i) for i=1:12);
seE1, seE2, seE3, seE4, seE5, seE6, seE7, seE8, seE9, seEA, seEB, seEC, seED  = collect(SignedExtendedFloat(14,i) for i=1:13);
seF1, seF2, seF3, seF4, seF5, seF6, seF7, seF8, seF9, seFA, seFB, seFC, seFD, seFE  = collect(SignedExtendedFloat(15,i) for i=1:14);
seG1, seG2, seG3, seG4, seG5, seG6, seG7, seG8, seG9, seGA, seGB, seGC, seGD, seGE, seGF  = collect(SignedExtendedFloat(16,i) for i=1:15);

overflowsFloat64(x) = iszero(floats(x)[2])

 function allmatch(::Type{T}, xs) where {T}
          flxs = filter(!isnan, floats(xs))
          flxs2 = map(T, flxs)
          all(flxs .== flxs2)
       end



sf21  = collect(filter(x->isfinite(x) && !signbit(x), floats(SignedFiniteFloat(2,i))) for i=1:1);
sf31, sf32  = collect(filter(x->isfinite(x) && !signbit(x), floats(SignedFiniteFloat(3,i))) for i=1:2);
sf41, sf42, sf43  = collect(filter(x->isfinite(x) && !signbit(x), floats(SignedFiniteFloat(4,i))) for i=1:3);
sf51, sf52, sf53, sf54  = collect(filter(x->isfinite(x) && !signbit(x), floats(SignedFiniteFloat(5,i))) for i=1:4);
sf61, sf62, sf63, sf64, sf65  = collect(filter(x->isfinite(x) && !signbit(x), floats(SignedFiniteFloat(6,i))) for i=1:5);
sf71, sf72, sf73, sf74, sf75, sf76  = collect(filter(x->isfinite(x) && !signbit(x), floats(SignedFiniteFloat(7,i))) for i=1:6);
sf81, sf82, sf83, sf84, sf85, sf86, sf87  = collect(filter(x->isfinite(x) && !signbit(x), floats(SignedFiniteFloat(8,i))) for i=1:7);
sf91, sf92, sf93, sf94, sf95, sf96, sf97, sf98  = collect(filter(x->isfinite(x) && !signbit(x), floats(SignedFiniteFloat(9,i))) for i=1:8);
sfA1, sfA2, sfA3, sfA4, sfA5, sfA6, sfA7, sfA8, sfA9  = collect(filter(x->isfinite(x) && !signbit(x), floats(SignedFiniteFloat(10,i))) for i=1:9);
sfB1, sfB2, sfB3, sfB4, sfB5, sfB6, sfB7, sfB8, sfB9, sfBA  = collect(filter(x->isfinite(x) && !signbit(x), floats(SignedFiniteFloat(11,i))) for i=1:10);
sfC1, sfC2, sfC3, sfC4, sfC5, sfC6, sfC7, sfC8, sfC9, sfCA, sfCB  = collect(filter(x->isfinite(x) && !signbit(x), floats(SignedFiniteFloat(12,i))) for i=1:11);
sfD1, sfD2, sfD3, sfD4, sfD5, sfD6, sfD7, sfD8, sfD9, sfDA, sfDB, sfDC  = collect(filter(x->isfinite(x) && !signbit(x), floats(SignedFiniteFloat(13,i))) for i=1:12);
sfE1, sfE2, sfE3, sfE4, sfE5, sfE6, sfE7, sfE8, sfE9, sfEA, sfEB, sfEC, sfED  = collect(filter(x->isfinite(x) && !signbit(x), floats(SignedFiniteFloat(14,i))) for i=1:13);
sfF1, sfF2, sfF3, sfF4, sfF5, sfF6, sfF7, sfF8, sfF9, sfFA, sfFB, sfFC, sfFD, sfFE  = collect(filter(x->isfinite(x) && !signbit(x), floats(SignedFiniteFloat(15,i))) for i=1:14);
sfG1, sfG2, sfG3, sfG4, sfG5, sfG6, sfG7, sfG8, sfG9, sfGA, sfGB, sfGC, sfGD, sfGE, sfGF  = collect(filter(x->isfinite(x) && !signbit(x), floats(SignedFiniteFloat(16,i))) for i=1:15);

s2to8 = unique(sort(vcat(sf21[1],sf31,sf32,sf41, sf42, sf43,sf51, sf52, sf53, sf54,sf61, sf62, sf63, sf64, sf65,sf71, sf72, sf73, sf74, sf75, sf76,sf81, sf82, sf83, sf84, sf85, sf86, sf87)))
s2to8q = map(x->convert(Rational{Int128},x), s2to8)
s2to8frexp = map(frexp, s2to8)
s2to8frexp1 = unique(sort(map(first, s2to8frexp)))
s2to8frexp1q = map(x->convert(Rational,x), s2to8frexp1)

setdiff(s2to8q,  map(x->convert(Rational{BigInt},BigFloat(x)), sfE7)) # Rational{BigInt}[]

uf21, uf22  = collect(filter(isfinite, floats(UnsignedFiniteFloat(2,i))) for i=1:2);
uf31, uf32, uf33  = collect(filter(isfinite, floats(UnsignedFiniteFloat(3,i))) for i=1:3);
uf41, uf42, uf43, uf44  = collect(filter(isfinite, floats(UnsignedFiniteFloat(4,i))) for i=1:4);
uf51, uf52, uf53, uf54, uf55  = collect(filter(isfinite, floats(UnsignedFiniteFloat(5,i))) for i=1:5);
uf61, uf62, uf63, uf64, uf65, uf66  = collect(filter(isfinite, floats(UnsignedFiniteFloat(6,i))) for i=1:6);
uf71, uf72, uf73, uf74, uf75, uf76, uf77  = collect(filter(isfinite, floats(UnsignedFiniteFloat(7,i))) for i=1:7);
uf81, uf82, uf83, uf84, uf85, uf86, uf87, uf88  = collect(filter(isfinite, floats(UnsignedFiniteFloat(8,i))) for i=1:8);
uf91, uf92, uf93, uf94, uf95, uf96, uf97, uf98, uf99  = collect(filter(isfinite, floats(UnsignedFiniteFloat(9,i))) for i=1:9);
ufA1, ufA2, ufA3, ufA4, ufA5, ufA6, ufA7, ufA8, ufA9, ufAA  = collect(filter(isfinite, floats(UnsignedFiniteFloat(10,i))) for i=1:10);
ufB1, ufB2, ufB3, ufB4, ufB5, ufB6, ufB7, ufB8, ufB9, ufBA, ufBB  = collect(filter(isfinite, floats(UnsignedFiniteFloat(11,i))) for i=1:11);
ufC1, ufC2, ufC3, ufC4, ufC5, ufC6, ufC7, ufC8, ufC9, ufCA, ufCB, ufCC  = collect(filter(isfinite, floats(UnsignedFiniteFloat(12,i))) for i=1:12);
ufD1, ufD2, ufD3, ufD4, ufD5, ufD6, ufD7, ufD8, ufD9, ufDA, ufDB, ufDC, ufDD  = collect(filter(isfinite, floats(UnsignedFiniteFloat(13,i))) for i=1:13);
ufE1, ufE2, ufE3, ufE4, ufE5, ufE6, ufE7, ufE8, ufE9, ufEA, ufEB, ufEC, ufED, ufEE  = collect(filter(isfinite, floats(UnsignedFiniteFloat(14,i))) for i=1:14);
ufF1, ufF2, ufF3, ufF4, ufF5, ufF6, ufF7, ufF8, ufF9, ufFA, ufFB, ufFC, ufFD, ufFE, ufFF  = collect(filter(isfinite, floats(UnsignedFiniteFloat(15,i))) for i=1:15);

u2to8 = unique(sort(vcat(uf21[1],uf22,uf31,uf32,uf33,uf41, uf42, uf43,uf44,uf51, uf52, uf53, uf54,uf55,uf61, uf62, uf63, uf64, uf65,uf66,uf71, uf72, uf73, uf74, uf75, uf76,uf77,uf81, uf82, uf83, uf84, uf85, uf86, uf87, uf88)))
u2to8q = map(x->convert(Rational{BigInt},BigFloat(x)), u2to8)
u2to8frexp = map(frexp, u2to8)
u2to8frexp1 = unique(sort(map(first, u2to8frexp)))
u2to8frexp1q = map(x->convert(Rational,x), u2to8frexp1)

setdiff(u2to8q,  map(x->convert(Rational{BigInt},BigFloat(x)), ufF8)) # Rational{BigInt}[]
setdiff(u2to6q,  map(x->convert(Rational{BigInt},BigFloat(x)), ufB6)) # Rational{BigInt}[]