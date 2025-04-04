# predicates for abstract types

is_signed(@nospecialize(T::Type{<:AbsSignedMLFloat}))     = true
is_signed(@nospecialize(T::Type{<:AbsUnsignedMLFloat}))   = false

is_unsigned(@nospecialize(T::Type{<:AbsSignedMLFloat}))   = false
is_unsigned(@nospecialize(T::Type{<:AbsUnsignedMLFloat})) = true

is_finite(@nospecialize(T::Type{<:AbsSignedFiniteMLFloat}))     = true
is_finite(@nospecialize(T::Type{<:AbsUnsignedFiniteMLFloat}))   = true
is_finite(@nospecialize(T::Type{<:AbsSignedExtendedMLFloat}))   = false
is_finite(@nospecialize(T::Type{<:AbsUnsignedExtendedMLFloat})) = false

is_extended(@nospecialize(T::Type{<:AbsSignedFiniteMLFloat}))     = false
is_extended(@nospecialize(T::Type{<:AbsUnsignedFiniteMLFloat}))   = false
is_extended(@nospecialize(T::Type{<:AbsSignedExtendedMLFloat}))   = true
is_extended(@nospecialize(T::Type{<:AbsUnsignedExtendedMLFloat})) = true

# predicates for concrete types

is_signed(@nospecialize(x::SFiniteMLFloats))   = true
is_signed(@nospecialize(x::SExtendedMLFloats)) = true
is_signed(@nospecialize(x::UFiniteMLFloats))   = false
is_signed(@nospecialize(x::UExtendedMLFloats)) = false

is_unsigned(@nospecialize(x::SFiniteMLFloats))   = false
is_unsigned(@nospecialize(x::SExtendedMLFloats)) = false
is_unsigned(@nospecialize(x::UFiniteMLFloats))   = true
is_unsigned(@nospecialize(x::UExtendedMLFloats)) = true

is_finite(@nospecialize(x::SFiniteMLFloats))   = true
is_finite(@nospecialize(x::SExtendedMLFloats)) = false
is_finite(@nospecialize(x::UFiniteMLFloats))   = true
is_finite(@nospecialize(x::UExtendedMLFloats)) = false

is_extended(@nospecialize(x::SFiniteMLFloats))   = false
is_extended(@nospecialize(x::SExtendedMLFloats)) = true
is_extended(@nospecialize(x::UFiniteMLFloats))   = false
is_extended(@nospecialize(x::UExtendedMLFloats)) = true
