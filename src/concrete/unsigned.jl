function UFiniteMLFloats(bits, sigbits)
    codetype  = typeforcode(bits)
    floattype = typeforfloat(bits)

    codes = encodings(bits)

    vals = foundation_floats(bits, sigbits)
    vals[end] = NaN

    fpvals = map(floattype, vals)
    fpmem = memalign_clear(floattype, length(fpvals))
    copyto!(fpmem, fpvals)

    UFiniteMLFloats{bits, sigbits, floattype, codetype}(fpmem, codes)
end

function UExtendedMLFloats(bits, sigbits)
    codetype  = typeforcode(bits)
    floattype = typeforfloat(bits)

    codes = encodings(bits)

    vals = foundation_floats(bits, sigbits)
    vals[end] = NaN
    vals[end-1]= Inf

    fpvals = map(floattype, vals)
    fpmem = memalign_clear(floattype, length(fpvals))
    copyto!(fpmem, fpvals)

    UExtendedMLFloats{bits, sigbits, floattype, codetype}(fpmem, codes)
end
