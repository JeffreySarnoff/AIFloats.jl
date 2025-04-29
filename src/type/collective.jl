for (T,A) in ((:UFiniteFloats, :AbsUFiniteFloatML),
              (:UExtendedFloats, :AbsUExtendedFloatML),
              (:SFiniteFloats, :AbsSFiniteFloatML),
              (:SExtendedFloats, :AbsSExtendedFloatML) )
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

codes(@nospecialize(x::AbstractFloatML))  = x.codes
floats(@nospecialize(x::AbstractFloatML)) = x.floats
symbol(@nospecialize(x::AbstractFloatML)) = x.symbol

nonneg_codes(@nospecialize(x::AbstractFloatML))  = x.nonneg_codes
nonneg_floats(@nospecialize(x::AbstractFloatML)) = x.nonneg_floats
