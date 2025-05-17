for (T,A) in ((:UFiniteAIFloats, :AbsUnsignedFiniteAIFloat),
              (:UExtendedAIFloats, :AbsUnsignedExtendedAIFloat))
  @eval begin
    struct $T{Bits, SigBits, N, M, Float, Code} <: $A{Bits, SigBits}
        floats::NTuple{N, Float}
        codes::NTuple{N, Code}
        nonneg_floats::NTuple{M, Float} # nonneg_floats::DenseVector{Float}
        nonneg_codes::NTuple{M, Code} # nonneg_codes::DenseVector{Code}
    end

    function $T(bits, sigbits)
        Float = typeforfloats(bits, sigbits)
        Code = typeforcodes(bits, sigbits)
        N = 2^bits
        M = 2^(bits - sigbits)
        $T{bits, sigbits, N, M, Float, Code}()
    end
  end
end



for (T,A) in ((:SFiniteAIFloats, :AbsSignedFiniteAIFloat),
              (:SExtendedAIFloats, :AbsSignedExtendedAIFloat))
  @eval begin
    struct $T{Bits, SigBits, N, M, Float, Code} <: $A{Bits, SigBits}
        floats::NTuple{N, Float}
        codes::NTuple{N, Code}
        nonneg_floats::NTuple{M, Float} # nonneg_floats::DenseVector{Float}
        nonneg_codes::NTuple{M, Code} # nonneg_codes::DenseVector{Code}
    end

    function $T(bits, sigbits)
        Float = typeforfloats(bits, sigbits)
        Code = typeforcodes(bits, sigbits)
        N = 2^bits
        M = 2^(bits - sigbits)
        $T{bits, sigbits, N, M, Float, Code}()
    end
  end
end

codes(@nospecialize(x::AbstractAIFloat))  = x.codes
floats(@nospecialize(x::AbstractAIFloat)) = x.floats
symbol(@nospecialize(x::AbstractAIFloat)) = x.symbol

nonneg_codes(@nospecialize(x::AbstractAIFloat))  = x.nonneg_codes
nonneg_floats(@nospecialize(x::AbstractAIFloat)) = x.nonneg_floats


abstract type AbstractAIFloats{Floats} <: AbstractFloat end

struct T1{N, Floats} <: AbstractAIFloats{Floats}
    floats::NTuple{N,Floats}
end

struct T2{Floats} <: AbstractAIFloats{Floats}
    floats::NTuple{N,Floats} where {N}
end

struct T3 <: AbstractFloat
    floats::NTuple{N,T} where {N,T}
end


