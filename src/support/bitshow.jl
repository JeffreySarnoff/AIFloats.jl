function prettybits(nbits, bitwidth, nonneg)
    nonneg >= 0 && nbits <= bitwidth || throw(DomainError(string(;nbits, bitwidth, nonneg)));
    bitstr = string(nonneg, base=2)
    bstr = fill('0', bitwidth - length(bitstr)) * bitstr
    string("0b", bstr)
end
