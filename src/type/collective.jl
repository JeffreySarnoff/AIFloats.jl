for (T,A) in ((:SFiniteFloats, :AbsSignedFiniteAIFloat),
              (:SExtendedFloats, :AbsSignedExtendedAIFloat) )
  @eval begin
    struct $T{Bits, SigBits, Float, Code} <: $A{Bits, SigBits}
        floats::DenseVector{Float}
        codes::DenseVector{Code}
        nonneg_floats::DenseVector{Float}
        nonneg_codes::DenseVector{Code}
        symbol::Symbol
    end
  end
end

codes(@nospecialize(x::AbstractAIFloat))  = x.codes
floats(@nospecialize(x::AbstractAIFloat)) = x.floats
symbol(@nospecialize(x::AbstractAIFloat)) = x.symbol

nonneg_codes(@nospecialize(x::AbstractAIFloat))  = x.nonneg_codes
nonneg_floats(@nospecialize(x::AbstractAIFloat)) = x.nonneg_floats

for (T,A) in ((:UFiniteFloats, :AbsUnsignedFiniteAIFloat),
              (:UExtendedFloats, :AbsUnsignedExtendedAIFloat))
  @eval begin
    struct $T{Bits, SigBits, Float, Code} <: $A{Bits, SigBits}
        floats::DenseVector{Float}
        codes::DenseVector{Code}
        nonneg_floats::DenseVector{Float}
        nonneg_codes::DenseVector{Code}
        symbol::Symbol
  end
  end
end
