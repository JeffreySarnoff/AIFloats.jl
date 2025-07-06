
# predicates for abstract types

is_aifloat(@nospecialize(T::Type{<:AbstractFloat})) = false
is_aifloat(@nospecialize(T::Type{<:AbstractAIFloat})) = true
is_aifloat(@nospecialize(T::Type)) = false

is_signed(@nospecialize(T::Type{<:AbstractSignedFloat}))     = true
is_signed(@nospecialize(T::Type{<:AbstractUnsignedFloat}))   = false

is_unsigned(@nospecialize(T::Type{<:AbstractSignedFloat}))   = false
is_unsigned(@nospecialize(T::Type{<:AbstractUnsignedFloat})) = true

is_finite(@nospecialize(T::Type{<:AbstractSignedFinite}))     = true
is_finite(@nospecialize(T::Type{<:AbstractUnsignedFinite}))   = true
is_finite(@nospecialize(T::Type{<:AbstractSignedExtended}))   = false
is_finite(@nospecialize(T::Type{<:AbstractUnsignedExtended})) = false

is_extended(@nospecialize(T::Type{<:AbstractSignedFinite}))     = false
is_extended(@nospecialize(T::Type{<:AbstractUnsignedFinite}))   = false
is_extended(@nospecialize(T::Type{<:AbstractSignedExtended}))   = true
is_extended(@nospecialize(T::Type{<:AbstractUnsignedExtended})) = true

has_subnormals(::Type{T}) where {Bits, T<:AbstractAIFloat{Bits, 1}} = false
has_subnormals(T::Type{<:AbstractAIFloat}) = true

# cover instantiations
is_aifloat(@nospecialize(x::T)) where {T<:AbstractFloat} = false
is_aifloat(@nospecialize(x::T)) where {T<:AbstractAIFloat} = true

for F in (:is_extended, :is_finite, :is_signed, :is_unsigned, :has_subnormals) 
    @eval $F(x::T) where {T<:AbstractAIFloat} = $F(T)
end

