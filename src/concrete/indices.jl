
"""
    offset_to_index(x)

convert the P3109 encoding `x` into a Julia index as an UInt16
- (0x39) ↦ 0x0040
- (255) ↦ 0x01
- in 0-based languages, this is a do nothing operation
""" offset_to_index
@inline function offset_to_index(x::StaticInt{N}) where {N}
    x % UInt16 + one(UInt16)
end

offset_to_index(x::T) where {T<:Integer} = (x % UInt16) + one(UInt16)

"""
    index_to_offset(x)

convert the Julia index `x` into a P3109 offset as a UInt16
- (0x040) ↦ 0x0039
- in 0-based languages, this is a do nothing operation
""" index_to_offset

@inline function index_to_offset(x::StaticInt{N}) where {N}
    (x % UInt16) - one(UInt16)
end

@inline index_to_offset(x::T) where {T<:Integer} = (x % UInt16) - one(UInt16)

"""
    index_to_code(bits, index)

convert the Julia index `x` into a P3109 encoding value as a UInt8|16
- (8, 256) ↦ 0xff
- (9, 256) ↦ 0x00ff
""" index_to_code

@inline function index_to_code(bits, index)
    T = bits <= 8 ? UInt8 : UInt16
    index_to_offset(index) % T
end
