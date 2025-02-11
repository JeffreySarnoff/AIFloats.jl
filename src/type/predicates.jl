is_signed(@nospecialize(T::Type{SFiniteFloats}))   = true
is_signed(@nospecialize(T::Type{<:SExtendedFloats})) = true
is_signed(@nospecialize(T::Type{<:UFiniteFloats}))   = false
is_signed(@nospecialize(T::Type{<:UExtendedFloats})) = false

is_unsigned(@nospecialize(T::Type{<:SFiniteFloats}))   = false
is_unsigned(@nospecialize(T::Type{<:SExtendedFloats})) = false
is_unsigned(@nospecialize(T::Type{<:UFiniteFloats}))   = true
is_unsigned(@nospecialize(T::Type{<:UExtendedFloats})) = true

is_finite(@nospecialize(T::Type{<:SFiniteFloats}))   = true
is_finite(@nospecialize(T::Type{<:SExtendedFloats})) = false
is_finite(@nospecialize(T::Type{<:UFiniteFloats}))   = true
is_finite(@nospecialize(T::Type{<:UExtendedFloats})) = false

is_extended(@nospecialize(T::Type{<:SFiniteFloats}))   = false
is_extended(@nospecialize(T::Type{<:SExtendedFloats})) = true
is_extended(@nospecialize(T::Type{<:UFiniteFloats}))   = false
is_extended(@nospecialize(T::Type{<:UExtendedFloats})) = true

for T in (:SFiniteFloats, :SExtendedFloats, :UFiniteFloats, :UExtendedFloats)
    for F in (:is_signed, :is_unsigned, :is_finite, :is_extended)
        @eval $F(x::$T) = $F($T)
    end
end


