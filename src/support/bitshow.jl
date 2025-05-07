function prettybits(bitwidth, val)
    n = bitwidth
    s = ""
    while n > 0
        s = string(val & 1, s)
        val >>= 1
        n -= 1
    end
    s
end
