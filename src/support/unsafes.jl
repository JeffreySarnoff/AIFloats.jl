"""
    unsafe_pointer_from_objref

    This function is considered *high risk*.

    The pointer returned references an immutable object.

    - It is not safe to use this pointer in any way
      that would modify the object.

    - It is possible to get different values on different calls

    a nonconstant pointer to an immutable object
"""
function unsafe_pointer_from_objref(@nospecialize(x))
    ccall(:jl_value_ptr, Ptr{Cvoid}, (Any,), x)
end
