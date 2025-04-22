basetypename(T::Type) = T.name.wrapper
basetypename(x::T) where {T} = basetypename(T)

"""
    compacttype(::Type{T}) where {T<:AbstractFloatML{Bits, SigBits}}

    SExtendedFloats{8, 5, Float64, UInt8} ⤇ SExtendedFloats{8, 5}
""" compacttype

compacttype(T::Type) = basetypename(T){nBits(T), nSigBits(T)}
compacttype(x::T) where {T} = compacttype(T)
