
"""
    offset_to_index(x)

convert the P3109 encoding `x` into a Julia index as an UInt16
- *>>* (0xff) ↦ 0x0100
- in 0-based languages, this is a do nothing operation
"""
@inline function offset_to_index(x::StaticInt{N})::CODE where {N}
    idx = (x % UInt16) + one(UInt16)
    x <= static(8) && return idx % UInt8
    idx
end

offset_to_index(x::T) where {T<:Integer} = (x % UInt16) + one(UInt16)

"""
    index_to_offset(x)

convert the Julia index `x` into a P3109 encoding value as a UInt16
- **>>** (0x0100) ↦ 0x00ff
- in 0-based languages, this is a do nothing operation
"""
@inline function index_to_offset(bits::StaticInt{N}, x)::CODE where {N}
    code = (x % UInt16) - one(UInt16)
    N <= static(8) && return code % UInt8
    code
end

@inline index_to_offset(bits::Integer, x)::CODE = index_to_offset(static(bits), x)
