struct UFiniteMLFloats{Bits, SigBits, Floats, Codes} <: AbsUnsignedFiniteMLFloat{Bits, SigBits}
    floats::Floats
    codes::Codes
end

struct UExtendedMLFloats{Bits, SigBits, Floats, Codes} <: AbsUnsignedExtendedMLFloat{Bits, SigBits}
    floats::Floats
    codes::Codes
end

struct SFiniteMLFloats{Bits, SigBits, Floats, Codes} <: AbsSignedFiniteMLFloat{Bits, SigBits}
    floats::Floats
    codes::Codes
end

struct SExtendedMLFloats{Bits, SigBits, Floats, Codes} <: AbsSignedExtendedMLFloat{Bits, SigBits}
    floats::DenseVector{Floats}
    codes::DenseVector{Codes}
end

codes(@nospecialize(x::AbstractMLFloat)) = x.codes
floats(@nospecialize(x::AbstractMLFloat))= x.floats
