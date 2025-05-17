function prettybits(nbits, bitwidth, precision, nonneg; sepidx1 = precision, sepidx2 =bitwidth - precision  )
    nonneg >= 0 && nbits <= bitwidth || throw(DomainError(string(;nbits, bitwidth, nonneg)));
    bits_compact_str = string(nonneg; base=2)
    bstr = "0b" * repeat('0', bitwidth - length(bits_compact_str)) * bits_compact_str

    if 0 < sepidx1 < bitwidth
        bstr = bstr[1:sepidx1] * "_" * bstr[sepidx1+1:end]
    end
    if 0 < sepidx2 < bitwidth
        bstr = bstr[1:sepidx2] * "_" * bstr[sepidx2+1:end]
    end
    return reverse(bstr)
end


function prettybits(nbits, bitwidth, precision, nonneg; sepidx1 = precision, sepidx2 = bitwidth - precision  )
    nonneg >= 0 && nbits <= bitwidth || throw(DomainError(string(;nbits, bitwidth, nonneg)));
    bitstr = string(nonneg, base=2)
        bstr = "0b" *repeat('0', bitwidth - length(bitstr)) * bitstr

    if 0 < sepidx1 < bitwidth
        bstr = bstr[1:sepidx1-1] * "_" * bstr[sepidx1+1:end]
            end
    if 0 < sepidx2 < bitwidth
        bstr = bstr[1:sepidx2] * "_" * bstr[sepidx2+1:end]
            end
    return bstr
end


