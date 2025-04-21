# predicates for abstract types

is_signed(@nospecialize(T::Type{<:AbsSignedFloatML}))     = true
is_signed(@nospecialize(T::Type{<:AbsUnsignedFloatML}))   = false

is_unsigned(@nospecialize(T::Type{<:AbsSignedFloatML}))   = false
is_unsigned(@nospecialize(T::Type{<:AbsUnsignedFloatML})) = true

is_finite(@nospecialize(T::Type{<:AbsSFiniteFloatML}))     = true
is_finite(@nospecialize(T::Type{<:AbsUFiniteFloatML}))   = true
is_finite(@nospecialize(T::Type{<:AbsSExtendedFloatML}))   = false
is_finite(@nospecialize(T::Type{<:AbsUExtendedFloatML})) = false

is_extended(@nospecialize(T::Type{<:AbsSFiniteFloatML}))     = false
is_extended(@nospecialize(T::Type{<:AbsUFiniteFloatML}))   = false
is_extended(@nospecialize(T::Type{<:AbsSExtendedFloatML}))   = true
is_extended(@nospecialize(T::Type{<:AbsUExtendedFloatML})) = true

# predicates for concrete types

is_signed(@nospecialize(x::SFiniteFloats))   = true
is_signed(@nospecialize(x::SExtendedFloats)) = true
is_signed(@nospecialize(x::UFiniteFloats))   = false
is_signed(@nospecialize(x::UExtendedFloats)) = false

is_unsigned(@nospecialize(x::SFiniteFloats))   = false
is_unsigned(@nospecialize(x::SExtendedFloats)) = false
is_unsigned(@nospecialize(x::UFiniteFloats))   = true
is_unsigned(@nospecialize(x::UExtendedFloats)) = true

is_finite(@nospecialize(x::SFiniteFloats))   = true
is_finite(@nospecialize(x::SExtendedFloats)) = false
is_finite(@nospecialize(x::UFiniteFloats))   = true
is_finite(@nospecialize(x::UExtendedFloats)) = false

is_extended(@nospecialize(x::SFiniteFloats))   = false
is_extended(@nospecialize(x::SExtendedFloats)) = true
is_extended(@nospecialize(x::UFiniteFloats))   = false
is_extended(@nospecialize(x::UExtendedFloats)) = true
