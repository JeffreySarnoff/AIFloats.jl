"""
    unsafe_pointer_from_objref(x)

    **High Risk** (read the name as "unsafe_unsafe_pointer_from_thisnthat")

    The pointer returned references an immutable object.

    - It is dangerous to access the pointed-to object.
    - It is tempting fate to modify or in any way alter
      either the pointer or the pointer's referent.

      julia> unsafe_pointer(x)
      Ptr{Nothing} @0x000001f113152b00
"""
@inline function unsafe_pointer(@nospecialize(x))
    ccall(:jl_value_ptr, Ptr{Cvoid}, (Any,), x)
end

"""
    unsafe_address_from_objref(x)

    **High Risk** (read the name as "unsafe_unsafe_address_from_yonder")

    The address returned is the corresponding internal pointer value.

    - It is very wrong to access the address directly.
    - It is incoherent to modify or otherwise alter the address or its referent.
s
      julia> unsafe_address(x)
      0x000001f113152b00
"""
function unsafe_address(@nospecialize(x))
    convert(UInt64, unsafe_pointer(x))
end



AlignedAllocs.alignment(xs::AbstractArray) = 2^trailing_zeros(UInt64(pointer(xs)))
abstract type AbstractStruct end

struct CartesianComplex{T} <: AbstractStruct
    real::T
    imag::T
end

ccplx = CartesianComplex(1.0, -0.5)

AlignedAllocs.alignment(xs::AbstractStruct) = 2^trailing_zeros(UInt64(pointer(xs)))
AlignedAllocs.alignment(x) = 2^trailing_zeros(UInt64(pointer(xs)))
