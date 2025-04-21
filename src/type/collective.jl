struct UFiniteFloats{Bits, SigBits, Float, Code} <: AbsUFiniteFloatML{Bits, SigBits}
    floats::DenseVector{Float}
    codes::DenseVector{Code}
    nonneg_floats::DenseVector{Float}
    nonneg_codes::DenseVector{Code}
end

struct UExtendedFloats{Bits, SigBits, Float, Code} <: AbsUExtendedFloatML{Bits, SigBits}
    floats::DenseVector{Float}
    codes::DenseVector{Code}
    nonneg_floats::DenseVector{Float}
    nonneg_codes::DenseVector{Code}
end

struct SFiniteFloats{Bits, SigBits, Float, Code} <: AbsSFiniteFloatML{Bits, SigBits}
    floats::DenseVector{Float}
    codes::DenseVector{Code}
    nonneg_floats::DenseVector{Float}
    nonneg_codes::DenseVector{Code}
end

struct SExtendedFloats{Bits, SigBits, Float, Code} <: AbsSExtendedFloatML{Bits, SigBits}
    floats::DenseVector{Float}
    codes::DenseVector{Code}
    nonneg_floats::DenseVector{Float}
    nonneg_codes::DenseVector{Code}
end

codes(@nospecialize(x::AbstractFloatML))  = x.codes
floats(@nospecialize(x::AbstractFloatML)) = x.floats

nonneg_codes(@nospecialize(x::AbstractFloatML))  = x.nonneg_codes
nonneg_floats(@nospecialize(x::AbstractFloatML)) = x.nonneg_floats

#=
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

nonneg_codes(x::AbsSFloatML{Bits, SigBits}) where {Bits, SigBits} =
    x.codes[1:(1<<(Bits-1)-1)]

nonneg_floats(x::AbsSFloatML{Bits, SigBits}) where {Bits, SigBits} =
    x.floats[1:(1<<(Bits-1)-1)]

nonneg_codes(x::AbsUFloatML{Bits, SigBits}) where {Bits, SigBits} =
    x.floats[1:(1<<(Bits)-1)]

nonneg_floats(x::AbsUFloatML{Bits, SigBits}) where {Bits, SigBits} =
    x.floats[1:(1<<Bits)-1]

=#
