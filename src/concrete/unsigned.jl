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
