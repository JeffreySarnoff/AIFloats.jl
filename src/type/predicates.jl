is_signed(@nospecialize(T::Type{SFiniteMLFloats}))   = true
is_signed(@nospecialize(T::Type{<:SExtendedMLFloats})) = true
is_signed(@nospecialize(T::Type{<:UFiniteMLFloats}))   = false
is_signed(@nospecialize(T::Type{<:UExtendedMLFloats})) = false

is_unsigned(@nospecialize(T::Type{<:SFiniteMLFloats}))   = false
is_unsigned(@nospecialize(T::Type{<:SExtendedMLFloats})) = false
is_unsigned(@nospecialize(T::Type{<:UFiniteMLFloats}))   = true
is_unsigned(@nospecialize(T::Type{<:UExtendedMLFloats})) = true

is_finite(@nospecialize(T::Type{<:SFiniteMLFloats}))   = true
is_finite(@nospecialize(T::Type{<:SExtendedMLFloats})) = false
is_finite(@nospecialize(T::Type{<:UFiniteMLFloats}))   = true
is_finite(@nospecialize(T::Type{<:UExtendedMLFloats})) = false

is_extended(@nospecialize(T::Type{<:SFiniteMLFloats}))   = false
is_extended(@nospecialize(T::Type{<:SExtendedMLFloats})) = true
is_extended(@nospecialize(T::Type{<:UFiniteMLFloats}))   = false
is_extended(@nospecialize(T::Type{<:UExtendedMLFloats})) = true

for T in (:SFiniteMLFloats, :SExtendedMLFloats, :UFiniteMLFloats, :UExtendedMLFloats)
    for F in (:is_signed, :is_unsigned, :is_finite, :is_extended)
        @eval $F(x::$T) = $F($T)
    end
end
