
# predicates for abstract types

is_aifloat(@nospecialize(T::Type{<:AbstractFloat})) = false
is_aifloat(@nospecialize(T::Type{<:AbstractAIFloat})) = true
is_aifloat(@nospecialize(T::Type)) = false

is_signed(@nospecialize(T::Type{<:AbstractSigned}))     = true
is_signed(@nospecialize(T::Type{<:AbstractUnsigned}))   = false

is_unsigned(@nospecialize(T::Type{<:AbstractSigned}))   = false
is_unsigned(@nospecialize(T::Type{<:AbstractUnsigned})) = true

is_finite(@nospecialize(T::Type{<:AkoSignedFinite}))     = true
is_finite(@nospecialize(T::Type{<:AkoUnsignedFinite}))   = true
is_finite(@nospecialize(T::Type{<:AkoSignedExtended}))   = false
is_finite(@nospecialize(T::Type{<:AkoUnsignedExtended})) = false

is_extended(@nospecialize(T::Type{<:AkoSignedFinite}))     = false
is_extended(@nospecialize(T::Type{<:AkoUnsignedFinite}))   = false
is_extended(@nospecialize(T::Type{<:AkoSignedExtended}))   = true
is_extended(@nospecialize(T::Type{<:AkoUnsignedExtended})) = true

has_subnormals(::Type{T}) where {Bits, T<:AbstractAIFloat{Bits, 1}} = false
has_subnormals(T::Type{<:AbstractAIFloat}) = true

# cover instantiations
is_aifloat(@nospecialize(x::T)) where {T<:AbstractFloat} = false
is_aifloat(@nospecialize(x::T)) where {T<:AbstractAIFloat} = true

for F in (:is_extended, :is_finite, :is_signed, :is_unsigned, :has_subnormals) 
    @eval $F(x::T) where {T<:AbstractAIFloat} = $F(T)
end

