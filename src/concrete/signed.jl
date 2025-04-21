function SFiniteFloats(bits::I, sigbits::I) where {I<:Integer}
    codetype  = typeforcode(bits)
    floattype = typeforfloat(bits)

    encoding = encodings(bits)
    vals = foundation_floats(bits, sigbits)
    append!(vals, -1 .* vals)
    vals[1+end>>1] = convert(floattype, NaN)

    fpvals = map(floattype, vals)
    fpmem = memalign_clear(floattype, length(fpvals))
    copyto!(fpmem, fpvals)

    
    nonneg_n = (1<<(bits-1)) # keep floatmax 
    nonneg_codes = memalign_clear(codetype, nonneg_n)
    nonneg_floats = memalign_clear(floattype, nonneg_n)

    copyto!(nonneg_codes, encoding[1:nonneg_n])
    copyto!(nonneg_floats, fpmem[1:nonneg_n])

    SFiniteFloats{bits, sigbits, floattype, codetype}(fpmem, encoding, nonneg_floats, nonneg_codes)
end

function SExtendedFloats(bits::I, sigbits::I) where {I<:Integer}
    codetype  = typeforcode(bits)
    floattype = typeforfloat(bits)

    encoding = encodings(bits)
    vals = foundation_floats(bits, sigbits)
    vals[end] = convert(floattype, Inf)
    append!(vals, -vals)
    vals[1+end>>1] = convert(floattype, NaN)

    fpvals = map(floattype, vals)
    fpmem = memalign_clear(floattype, length(fpvals))
    copyto!(fpmem, fpvals)

    nonneg_n = (1<<(bits-1)) # keep +Inf
    nonneg_codes = memalign_clear(codetype, nonneg_n)
    nonneg_floats = memalign_clear(floattype, nonneg_n)

    copyto!(nonneg_codes, encoding[1:nonneg_n])
    copyto!(nonneg_floats, fpmem[1:nonneg_n])

    SExtendedFloats{bits, sigbits, floattype, codetype}(fpmem, encoding, nonneg_floats, nonneg_codes)
end
