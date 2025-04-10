# predicates for abstract types

is_signed(@nospecialize(T::Type{<:AbsSignedFloatML}))     = true
is_signed(@nospecialize(T::Type{<:AbsUnsignedFloatML}))   = false

is_unsigned(@nospecialize(T::Type{<:AbsSignedFloatML}))   = false
is_unsigned(@nospecialize(T::Type{<:AbsUnsignedFloatML})) = true

is_finite(@nospecialize(T::Type{<:AbsSignedFiniteFloatML}))     = true
is_finite(@nospecialize(T::Type{<:AbsUnsignedFiniteFloatML}))   = true
is_finite(@nospecialize(T::Type{<:AbsSignedExtendedFloatML}))   = false
is_finite(@nospecialize(T::Type{<:AbsUnsignedExtendedFloatML})) = false

is_extended(@nospecialize(T::Type{<:AbsSignedFiniteFloatML}))     = false
is_extended(@nospecialize(T::Type{<:AbsUnsignedFiniteFloatML}))   = false
is_extended(@nospecialize(T::Type{<:AbsSignedExtendedFloatML}))   = true
is_extended(@nospecialize(T::Type{<:AbsUnsignedExtendedFloatML})) = true

# predicates for concrete types

is_signed(@nospecialize(x::SFiniteFloatsML))   = true
is_signed(@nospecialize(x::SExtendedFloatsML)) = true
is_signed(@nospecialize(x::UFiniteFloatsML))   = false
is_signed(@nospecialize(x::UExtendedFloatsML)) = false

is_unsigned(@nospecialize(x::SFiniteFloatsML))   = false
is_unsigned(@nospecialize(x::SExtendedFloatsML)) = false
is_unsigned(@nospecialize(x::UFiniteFloatsML))   = true
is_unsigned(@nospecialize(x::UExtendedFloatsML)) = true

is_finite(@nospecialize(x::SFiniteFloatsML))   = true
is_finite(@nospecialize(x::SExtendedFloatsML)) = false
is_finite(@nospecialize(x::UFiniteFloatsML))   = true
is_finite(@nospecialize(x::UExtendedFloatsML)) = false

is_extended(@nospecialize(x::SFiniteFloatsML))   = false
is_extended(@nospecialize(x::SExtendedFloatsML)) = true
is_extended(@nospecialize(x::UFiniteFloatsML))   = false
is_extended(@nospecialize(x::UExtendedFloatsML)) = true
