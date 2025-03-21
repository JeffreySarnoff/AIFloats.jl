
function SFiniteFloats(bits, sigbits)
    codetype  = typeforcode(bits)
    floattype = typeforfloat(bits)

    codes = encodings(bits)
    vals = foundation_floats(bits-1, sigbits)
    append!(vals, -1 .* vals)
    vals[1+end>>1] = oftype(vals[end], NaN)

    fpvals = map(floattype, vals)
    fpmem = memalign_clear(floattype, length(fpvals))
    copyto!(fpmem, fpvals)

    SFiniteFloats{bits, sigbits, floattype, codetype}(fpmem, codes)
end

function SExtendedFloats(bits, sigbits)
    codetype  = typeforcode(bits)
    floattype = typeforfloat(bits)

    codes = encodings(bits)
    vals = foundation_floats(bits-1, sigbits)
    vals[end] = oftype(vals[end], Inf)
    append!(vals, -vals)
    vals[1+end>>1] = oftype(vals[end], NaN)

    fpvals = map(floattype, vals)
    fpmem = memalign_clear(floattype, length(fpvals))
    copyto!(fpmem, fpvals)

    SExtendedFloats{bits, sigbits, floattype, codetype}(fpmem, codes)
end
