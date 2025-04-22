struct UFiniteFloats{Bits, SigBits, Float, Code} <: AbsUFiniteFloatML{Bits, SigBits}
    floats::DenseVector{Float}
    codes::DenseVector{Code}
    nonneg_floats::DenseVector{Float}
    nonneg_codes::DenseVector{Code}
    symbol::Symbol
end

struct UExtendedFloats{Bits, SigBits, Float, Code} <: AbsUExtendedFloatML{Bits, SigBits}
    floats::DenseVector{Float}
    codes::DenseVector{Code}
    nonneg_floats::DenseVector{Float}
    nonneg_codes::DenseVector{Code}
    symbol::Symbol
end

struct SFiniteFloats{Bits, SigBits, Float, Code} <: AbsSFiniteFloatML{Bits, SigBits}
    floats::DenseVector{Float}
    codes::DenseVector{Code}
    nonneg_floats::DenseVector{Float}
    nonneg_codes::DenseVector{Code}
    symbol::Symbol
end

struct SExtendedFloats{Bits, SigBits, Float, Code} <: AbsSExtendedFloatML{Bits, SigBits}
    floats::DenseVector{Float}
    codes::DenseVector{Code}
    nonneg_floats::DenseVector{Float}
    nonneg_codes::DenseVector{Code}
    symbol::Symbol
end

codes(@nospecialize(x::AbstractFloatML))  = x.codes
floats(@nospecialize(x::AbstractFloatML)) = x.floats
symbol(@nospecialize(x::AbstractFloatML)) = x.symbol

nonneg_codes(@nospecialize(x::AbstractFloatML))  = x.nonneg_codes
nonneg_floats(@nospecialize(x::AbstractFloatML)) = x.nonneg_floats
