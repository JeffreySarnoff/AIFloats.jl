
@inline function is_signed(x::T) where {B,E,T<:AbstractSignedFloat{B,E}}
    @nospecialize
    true
  end
  @inline function is_signed(x::T) where {B,E,T<:AbstractUnsignedFloat{B,E}}
    @nospecialize
    false
  end
  
  is_unsigned(x) = !is_signed(x)
  
  @inline function is_finite(x::T) where {B,E,T<:AkoSignedFiniteFloat{B,E}}
    @nospecialize
    true
  end
  @inline function is_finite(x::T) where {B,E,T<:AkoUnsignedFiniteFloat{B,E}}
    @nospecialize
    true
  end
  @inline function is_finite(x::T) where {B,E,T<:AkoSignedInfiniteFloat{B,E}}
    @nospecialize
    false
  end
  @inline function is_finite(x::T) where {B,E,T<:AkoUnsignedInfiniteFloat{B,E}}
    @nospecialize
    false
  end
  
  is_infinite(x) = !is_finite(x)
  