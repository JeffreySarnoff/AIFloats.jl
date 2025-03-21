ilog2(x) = trunc(Int,fld(log2(x),1))
isaligned(xs, bits) = trailing_zeros(UInt(pointer(xs))) >= ilog2(bits)

struct UFiniteFloats{Bits, SigBits, FType, CType} <: UnsignedFiniteAIFloat{Bits, SigBits}
    floats::Vector{FType} 
    codes::Vector{CType}
end

struct UExtendedFloats{Bits, SigBits, FType, CType} <: UnsignedExtendedAIFloat{Bits, SigBits}
    floats::Vector{FType} 
    codes::Vector{CType}
end 

struct SFiniteFloats{Bits, SigBits, FType, CType} <: SignedFiniteAIFloat{Bits, SigBits}
    floats::Vector{FType} 
    codes::Vector{CType}
end

struct SExtendedFloats{Bits, SigBits, FType, CType} <: SignedExtendedAIFloat{Bits, SigBits}
    floats::Vector{FType} 
    codes::Vector{CType}
end

