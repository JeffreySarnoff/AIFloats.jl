
# predicates for abstract types

is_aifloat(@nospecialize(T::Type{<:AbstractFloat})) = false
is_aifloat(@nospecialize(T::Type{<:AbstractAIFloat})) = true
is_aifloat(@nospecialize(T::Type)) = false

is_signed(@nospecialize(T::Type{<:AbsSignedFloat}))     = true
is_signed(@nospecialize(T::Type{<:AbsUnsignedFloat}))   = false

is_unsigned(@nospecialize(T::Type{<:AbsSignedFloat}))   = false
is_unsigned(@nospecialize(T::Type{<:AbsUnsignedFloat})) = true

is_finite(@nospecialize(T::Type{<:AbsSignedFiniteFloat}))     = true
is_finite(@nospecialize(T::Type{<:AbsUnsignedFiniteFloat}))   = true
is_finite(@nospecialize(T::Type{<:AbsSignedExtendedFloat}))   = false
is_finite(@nospecialize(T::Type{<:AbsUnsignedExtendedFloat})) = false

is_extended(@nospecialize(T::Type{<:AbsSignedFiniteFloat}))     = false
is_extended(@nospecialize(T::Type{<:AbsUnsignedFiniteFloat}))   = false
is_extended(@nospecialize(T::Type{<:AbsSignedExtendedFloat}))   = true
is_extended(@nospecialize(T::Type{<:AbsUnsignedExtendedFloat})) = true

has_subnormals(::Type{T}) where {Bits, T<:AbstractAIFloat{Bits, 1}} = false
has_subnormals(T::Type{<:AbstractAIFloat}) = true

# cover instantiations
is_aifloat(@nospecialize(x::T)) where {T<:AbstractFloat} = false
is_aifloat(@nospecialize(x::T)) where {T<:AbstractAIFloat} = true

for F in (:is_extended, :is_finite, :is_signed, :is_unsigned, :has_subnormals) 
    @eval $F(x::T) where {T<:AbstractAIFloat} = $F(T)
end

