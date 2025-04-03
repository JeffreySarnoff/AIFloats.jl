struct UFiniteMLFloats{Bits, SigBits, Floats, Codes} <: AbsUnsignedFiniteMLFloat{Bits, SigBits}
    floats::Floats
    codes::Codes
end

struct UExtendedMLFloats{Bits, SigBits, Floats, Codes} <: AbsUnsignedExtendedMLFloat{Bits, SigBits}
    floats::Floats
    codes::Codes
end

struct SFiniteMLFloats{Bits, SigBits, Floats, Codes} <: AbsSignedFiniteMLFloat{Bits, SigBits}
    floats::Floats
    codes::Codes
end

struct SExtendedMLFloats{Bits, SigBits, Floats, Codes} <: AbsSignedExtendedMLFloat{Bits, SigBits}
    floats::Floats
    codes::Codes
end

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

bitwidth(x::AbstractMLFloat{Bitwidth, Precision}) where {Bitwidth, Precision} = Bitwidth
precision(x::AbstractMLFloat{Bitwidth, Precision}) where {Bitwidth, Precision} = Precision
