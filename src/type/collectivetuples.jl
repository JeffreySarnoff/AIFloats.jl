for (T,A) in ((:UFiniteAIFloats, :AbsUnsignedFiniteAIFloat),
              (:UExtendedAIFloats, :AbsUnsignedExtendedAIFloat))
    @eval begin
        struct $T{Bits, SigBits, N, M, Float, Code} <: $A{Bits, SigBits}
            floats::NTuple{N, Float}
            codes::NTuple{N, Code}
            nonneg_floats::NTuple{M, Float} # nonneg_floats::DenseVector{Float}
            nonneg_codes::NTuple{M, Code} # nonneg_codes::DenseVector{Code}
        end
    end
end

function UFiniteAIFloats(bits, sigbits)
   Float = typeforfloats(bits, sigbits)
   Code = typeforcodes(bits, sigbits)
   N = 2^bits
   M = 2^(bits - sigbits)
   UFiniteAIFloats{bits, sigbits, N, M, Float, Code}
end




     UFiniteAIFloats{bits, sigbits, 0, 0, F, C}


for (T,A) in ((:SFiniteAIFloats, :AbsSignedFiniteAIFloat),
              (:SExtendedAIFloats, :AbsSignedExtendedAIFloat))
  @eval begin
    struct $T{Bits, SigBits, N, M, Float, Code} <: $A{Bits, SigBits}
        floats::NTuple{N, Float}
        codes::NTuple{N, Code}
        nonneg_floats::NTuple{M, Float} # nonneg_floats::DenseVector{Float}
        nonneg_codes::NTuple{M, Code} # nonneg_codes::DenseVector{Code}
    end
  end
end

codes(@nospecialize(x::AbstractAIFloat))  = x.codes
floats(@nospecialize(x::AbstractAIFloat)) = x.floats
symbol(@nospecialize(x::AbstractAIFloat)) = x.symbol

nonneg_codes(@nospecialize(x::AbstractAIFloat))  = x.nonneg_codes
nonneg_floats(@nospecialize(x::AbstractAIFloat)) = x.nonneg_floats


struct NT2 <: AbstractAIFloat{Floats, Codes}
    floats::NTuple{N,T} where {N,T}
end

struct NT3{Floats, Codes} <: AbstractAIFloat{Floats, Codes}
    floats::NTuple{N,T} where {N,T}
end

struct NT4{Floats} <: AbstractAIFloat{Floats}
    floats::NTuple{N,Floats} where {N}
end



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
