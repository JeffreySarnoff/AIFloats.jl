function prettybits(xs::T, x::S) where {T<:AbstractAIFloat, S<:Integer}
    nbits = nBits(T)
    nexpbits = nExpBits(T)
    nfracbits = nFracBits(T)
    nsigbits = nSigBits(T)
    nsignbits = nSignBits(T)

    u = x % typeforcode(nbits)
    signfield = u & Base.sign_mask(T)
    expfield = u & Base.exponent_mask(T)
    fracfield = u & trailing_significand_mask(T)
    bsign = string(signfield; base=2)
    bexp = string(expfield; base=2)
    bfrac = string(fracfield; base=2)
    bcode = bsign * bexp * bfrac

    (code = bcode, sign = bsign, exp = bexp, fraction = bfrac)
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


