alignment(xs::AbstractArray) = 2^trailing_zeros(UInt(pointer(xs)))
function UFiniteFloatsML(bits::I, sigbits::I) where {I<:Integer}
    codetype  = typeforcode(bits)
    floattype = typeforfloat(bits)

    encoding = encodings(bits)

    vals = foundation_floats(bits+1, sigbits)
    vals[end] = NaN

    fpvals = map(floattype, vals)
    fpmem = memalign_clear(floattype, length(fpvals))
    copyto!(fpmem, fpvals)

    UFiniteFloatsML{bits, sigbits, floattype, codetype}(fpmem, encoding)
end

function UFiniteFloats(bits::I, sigbits::I) where {I<:Integer}
    codetype  = typeforcode(bits)
    floattype = typeforfloat(bits)

    encoding = encodings(bits)

    vals = foundation_floats(bits+1, sigbits)
    vals[end] = NaN

    fpvals = map(floattype, vals)
    fpmem = memalign_clear(floattype, length(fpvals))
    copyto!(fpmem, fpvals)

#=

nonneg_codes(x::AbsSFloatML{Bits, SigBits}) where {Bits, SigBits} =
    x.codes[1:(1<<(Bits-1)-1)]
nonneg_floats(x::AbsSFloatML{Bits, SigBits}) where {Bits, SigBits} =
    x.floats[1:(1<<(Bits-1)-1)]

nonneg_codes(x::AbsUFloatML{Bits, SigBits}) where {Bits, SigBits} =
    x.floats[1:(1<<(Bits)-1)]
nonneg_floats(x::AbsUFloatML{Bits, SigBits}) where {Bits, SigBits} =
    x.floats[1:(1<<Bits)-1]
=#

    nonneg_n = (1<<bits) - 1 
    nonneg_codes = memalign_clear(codetype, nonneg_n)
    nonneg_floats = memalign_clear(floattype, nonneg_n)

    copyto!(nonneg_codes, encoding[1:nonneg_n])
    copyto!(nonneg_floats, fpmem[1:nonneg_n])
    
    UFiniteFloats{bits, sigbits, floattype, codetype}(fpmem, encoding, nonneg_floats, nonneg_codes)
end

function UExtendedFloatsML(bits::I, sigbits::I) where {I<:Integer}
    codetype  = typeforcode(bits)
    floattype = typeforfloat(bits)

    encoding = encodings(bits)

    vals = foundation_floats(bits+1, sigbits)
    vals[end] = NaN
    vals[end-1]= Inf

    fpvals = map(floattype, vals)
    fpmem = memalign_clear(floattype, length(fpvals))
    copyto!(fpmem, fpvals)

    UExtendedFloatsML{bits, sigbits, floattype, codetype}(fpmem, encoding)
end
