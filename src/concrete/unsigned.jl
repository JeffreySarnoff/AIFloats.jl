
function UFiniteFloats(bits::I, sigbits::I) where {I<:Integer}
    codetype  = typeforcode(bits)
    floattype = typeforfloat(bits)

    encoding = encodings(bits)

    vals = foundation_floats(bits+1, sigbits)
    vals[end] = convert(floattype, NaN)

    fpvals = map(floattype, vals)
    fpmem = memalign_clear(floattype, length(fpvals))
    copyto!(fpmem, fpvals)

    nonneg_n = (1<<bits) - 1 # drop NaN
    nonneg_codes = memalign_clear(codetype, nonneg_n)
    nonneg_floats = memalign_clear(floattype, nonneg_n)

    copyto!(nonneg_codes, encoding[1:nonneg_n])
    copyto!(nonneg_floats, fpmem[1:nonneg_n])
    
    symbol = Symbol(string("UFFloats", bits, "p",sigbits))

    UFiniteFloats{bits, sigbits, floattype, codetype}(fpmem, encoding, nonneg_floats, nonneg_codes, symbol)
end

function UExtendedFloats(bits::I, sigbits::I) where {I<:Integer}
    codetype  = typeforcode(bits)
    floattype = typeforfloat(bits)

    encoding = encodings(bits)

    vals = foundation_floats(bits+1, sigbits)
    vals[end-1] = convert(floattype, Inf)
    vals[end] = convert(floattype, NaN)

    fpvals = map(floattype, vals)
    fpmem = memalign_clear(floattype, length(fpvals))
    copyto!(fpmem, fpvals)

    nonneg_n = (1<<bits) - 1 # drop NaN
    nonneg_codes = memalign_clear(codetype, nonneg_n)
    nonneg_floats = memalign_clear(floattype, nonneg_n)

    copyto!(nonneg_codes, encoding[1:nonneg_n])
    copyto!(nonneg_floats, fpmem[1:nonneg_n])
    
    symbol = Symbol(string("UEFloats", bits, "p",sigbits))

    UExtendedFloats{bits, sigbits, floattype, codetype}(fpmem, encoding, nonneg_floats, nonneg_codes, symbol)
end
