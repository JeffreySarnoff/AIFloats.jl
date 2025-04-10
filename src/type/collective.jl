struct UFiniteFloatsML{Bits, SigBits, Float, Code} <: AbsUFiniteFloatML{Bits, SigBits}
    floats::DenseVector{Float}
    codes::DenseVector{Code}
end

struct UExtendedFloatsML{Bits, SigBits, Float, Code} <: AbsUExtendedFloatML{Bits, SigBits}
    floats::DenseVector{Float}
    codes::DenseVector{Code}
end

struct SFiniteFloatsML{Bits, SigBits, Float, Code} <: AbsSFiniteFloatML{Bits, SigBits}
    floats::DenseVector{Float}
    codes::DenseVector{Code}
end

struct SExtendedFloatsML{Bits, SigBits, Float, Code} <: AbsSExtendedFloatML{Bits, SigBits}
    floats::DenseVector{Float}
    codes::DenseVector{Code}
end

codes(@nospecialize(x::AbstractFloatML)) = x.codes
floats(@nospecialize(x::AbstractFloatML))= x.floats
