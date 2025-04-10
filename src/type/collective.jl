struct UFiniteFloatsML{Bits, SigBits, Floats, Codes} <: AbsUFiniteFloatML{Bits, SigBits}
    floats::DenseVector{Floats}
    codes::DenseVector{Codes}
end

struct UExtendedFloatsML{Bits, SigBits, Floats, Codes} <: AbsUExtendedFloatML{Bits, SigBits}
    floats::DenseVector{Floats}
    codes::DenseVector{Codes}
end

struct SFiniteFloatsML{Bits, SigBits, Floats, Codes} <: AbsSFiniteFloatML{Bits, SigBits}
    floats::DenseVector{Floats}
    codes::DenseVector{Codes}
end

struct SExtendedFloatsML{Bits, SigBits, Floats, Codes} <: AbsSExtendedFloatML{Bits, SigBits}
    floats::DenseVector{Floats}
    codes::DenseVector{Codes}
end

codes(@nospecialize(x::AbstractFloatML)) = x.codes
floats(@nospecialize(x::AbstractFloatML))= x.floats
