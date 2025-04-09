
function SFiniteMLFloats(bits, sigbits)
    codetype  = typeforcode(bits)
    floattype = typeforfloat(bits)

    encoding = encodings(bits)
    vals = foundation_floats(bits, sigbits)
    append!(vals, -1 .* vals)
    vals[1+end>>1] = oftype(vals[end], NaN)

    fpvals = map(floattype, vals)
    fpmem = memalign_clear(floattype, length(fpvals))
    copyto!(fpmem, fpvals)

    SFiniteMLFloats{bits, sigbits, floattype, codetype}(fpmem, encoding)
end

function SExtendedMLFloats(bits, sigbits)
    codetype  = typeforcode(bits)
    floattype = typeforfloat(bits)

    encoding = encodings(bits)
    vals = foundation_floats(bits, sigbits)
    vals[end] = oftype(vals[end], Inf)
    append!(vals, -vals)
    vals[1+end>>1] = oftype(vals[end], NaN)

    fpvals = map(floattype, vals)
    fpmem = memalign_clear(floattype, length(fpvals))
    copyto!(fpmem, fpvals)

    SExtendedMLFloats{bits, sigbits, floattype, codetype}(fpmem, encoding)
end
