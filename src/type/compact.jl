basetypename(T::Type) = T.name.wrapper
basetypename(x::T) where {T} = basetypename(T)

"""
    compacttype(::Type{T}) where {T<:AbstractAIFloat{Bits, SigBits}}

    SExtendedFloats{8, 5, Float64, UInt8} ⤇ SExtendedFloats{8, 5}
""" compacttype

compacttype(T::Type) = basetypename(T){nBits(T), nSigBits(T)}
compacttype(x::T) where {T} = compacttype(T)

expandedtype(T::Type) = basetypename(T){nBits(T), nSigBits(T), typeforfloat(nBits(T)), typeforcode(nBits(T))}
