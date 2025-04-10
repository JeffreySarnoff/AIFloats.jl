struct UFiniteFloatsML{Bits, SigBits, Floats, Codes} <: AbsUnsignedFiniteFloatML{Bits, SigBits}
    floats::DenseVector{Floats}
    codes::DenseVector{Codes}
end

struct UExtendedFloatsML{Bits, SigBits, Floats, Codes} <: AbsUnsignedExtendedFloatML{Bits, SigBits}
    floats::DenseVector{Floats}
    codes::DenseVector{Codes}
end

struct SFiniteFloatsML{Bits, SigBits, Floats, Codes} <: AbsSignedFiniteFloatML{Bits, SigBits}
    floats::DenseVector{Floats}
    codes::DenseVector{Codes}
end

struct SExtendedFloatsML{Bits, SigBits, Floats, Codes} <: AbsSignedExtendedFloatML{Bits, SigBits}
    floats::DenseVector{Floats}
    codes::DenseVector{Codes}
end

codes(@nospecialize(x::AbstractFloatML)) = x.codes
floats(@nospecialize(x::AbstractFloatML))= x.floats
