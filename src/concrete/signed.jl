
function SFiniteFloats(nbits, nsigbits)
    codetype  = typeforcode(nbits)
    floattype = typeforfloat(nbits)

    codes = encodings(nbits)
    vals = foundation_floats(nbits-1, nsigbits)
    append!(vals, -1 .* vals)
    vals[1+end>>1] = oftype(vals[end], NaN)

    fpvals = map(floattype, vals)
    fpmem = memalign_clear(floattype, length(fpvals))
    copyto!(fpmem, fpvals)

    SFiniteFloats{nbits, nsigbits, floattype, codetype}(fpmem, codes)
end

function SExtendedFloats(nbits, nsigbits)
    codetype  = typeforcode(nbits)
    floattype = typeforfloat(nbits)

    codes = encodings(nbits)
    vals = foundation_floats(nbits-1, nsigbits)
    vals[end] = oftype(vals[end], Inf)
    append!(vals, -vals)
    vals[1+end>>1] = oftype(vals[end], NaN)

    fpvals = map(floattype, vals)
    fpmem = memalign_clear(floattype, length(fpvals))
    copyto!(fpmem, fpvals)

    SExtendedFloats{nbits, nsigbits, floattype, codetype}(fpmem, codes)
end
