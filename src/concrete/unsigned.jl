function UFiniteFloats(nbits, nsigbits)
    codetype  = typeforcode(nbits)
    floattype = typeforfloat(nbits)

    codes = encodings(nbits)

    vals = foundation_floats(nbits, nsigbits)
    vals[end] = NaN

    fpvals = map(floattype, vals)
    fpmem = memalign_clear(floattype, length(fpvals))
    copyto!(fpmem, fpvals)

    UFiniteFloats{nbits, nsigbits, floattype, codetype}(fpmem, codes)
end

function UExtendedFloats(nbits, nsigbits)
    codetype  = typeforcode(nbits)
    floattype = typeforfloat(nbits)

    codes = encodings(nbits)

    vals = foundation_floats(nbits, nsigbits)
    vals[end] = NaN
    vals[end-1]= Inf

    fpvals = map(floattype, vals)
    fpmem = memalign_clear(floattype, length(fpvals))
    copyto!(fpmem, fpvals)

    UExtendedFloats{nbits, nsigbits, floattype, codetype}(fpmem, codes)
end
