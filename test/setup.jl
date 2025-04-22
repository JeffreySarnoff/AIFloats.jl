using FloatsForML, Test
using FloatsForML: BitsSmallMin, BitsSmallMax, IsUnsigned, IsSigned, IsFinite, IsExtended

Ks = BitsSmallMin:(BitsSmallMax+2)

function KP(x::T) where {K,P, T<:AbstractFloatML{K,P}}
    (K, P)
end

# initialize so index 1 is empty (Ks start from 2)
UFKs = [[]]
UEKs = [[]]
SFKs = [[]]
SEKs = [[]]

for K in Ks
    UFKPs = []
    UEKPs = []
    SFKPs = []
    SEKPs = []
    
    for P in 1:K-1
        UF = MLFloats(K, P, IsUnsigned, IsFinite)
        push!(UFKPs, UF)
        UE = MLFloats(K, P, IsUnsigned, IsExtended)
        push!(UEKPs, UE)
        SF = MLFloats(K, P, IsSigned, IsFinite)
        push!(SFKPs, SF)
        SE = MLFloats(K, P, IsSigned, IsExtended)
        push!(SEKPs, SE)
    end
    push!(UFKs, UFKPs)
    push!(UEKs, UEKPs)
    push!(SFKs, SFKPs)
    push!(SEKs, SEKPs)
end

TupleIdxs = map(k->map(KP, k), UFKs)

for K in 2:10
    for S in (true, false)
        for F in (true, false)
            map(i->MLFloats(K,i,S,F),  1:K-1)
        end
    end
end
