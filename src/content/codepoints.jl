# the special code points of the P3109 layout
#
# The layout, in one paragraph: zero is code 0 and there is exactly one zero —
# no negative zero. The single NaN sits where −0 would be for signed formats
# (the sign-bit-only pattern) and at the top code for unsigned ones. An EXTENDED
# domain spends one more code on +Inf immediately below the NaN slot, and (when
# signed) the top code on −Inf.
#
# The CODE is primary and the value is built from it: MaxFiniteOf is
# _rawvalue(F, _maxfinite_code(F)), never the reverse. One definition of the
# layout, defined here and imported everywhere — decode does not re-derive it.

_cu(::Type{F}, x) where {F<:Binary} = CodeType(F)(x)

"""
    nan_code(F)

The code point of the format's single NaN: `signmask` (the would-be −0 slot)
for a signed format, the top code for an unsigned one.

Not exported.
"""
nan_code(::Type{F}) where {F<:Binary} = is_signed(F) ? signmask(F) : codemask(F)

"""
    posinf_code(F)

The code point of +Inf — one below the NaN slot. Meaningful only when the
format is EXTENDED. Not exported.
"""
posinf_code(::Type{F}) where {F<:Binary} =
    (is_signed(F) ? signmask(F) : codemask(F)) - _cu(F, 1)

"""
    neginf_code(F)

The code point of −Inf — the top code. Meaningful only for a SIGNED, EXTENDED
format. (For an unsigned format the same code is NaN, which is why decode tests
NaN first.) Not exported.
"""
neginf_code(::Type{F}) where {F<:Binary} = codemask(F)

_maxfinite_code(::Type{F}) where {F<:Binary} =
    (is_signed(F) ? signmask(F) : codemask(F)) - _cu(F, is_extended(F) ? 2 : 1)

_minfinite_code(::Type{F}) where {F<:Binary} =
    is_signed(F) ? (_maxfinite_code(F) | signmask(F)) : _cu(F, 0)

for f in (:nan_code, :posinf_code, :neginf_code, :_maxfinite_code, :_minfinite_code)
    @eval $f(::Type{BV}) where {BV<:BinaryValue} = $f(BinaryFormatOf(BV))
    @eval $f(x::BinaryValue) = $f(BinaryFormatOf(x))
end

# extremal datums, built FROM the codes

"""
    MaxFiniteOf(F)

The largest finite datum of format `F`, as a [`BinaryValue`](@ref).

# Examples

```jldoctest
julia> decode(MaxFiniteOf(Binary(8, 4, SIGNED, FINITE)))
240.0
```
"""
MaxFiniteOf(::Type{F}) where {F<:Binary} = _rawvalue(F, _maxfinite_code(F))

"""
    MinFiniteOf(F)

The smallest (most negative for signed; zero for unsigned) finite datum of `F`.
"""
MinFiniteOf(::Type{F}) where {F<:Binary} = _rawvalue(F, _minfinite_code(F))

"""
    MinPositiveOf(F)

The smallest positive datum: code point 1. The least subnormal when `P > 1`,
the least normal when `P == 1`.
"""
MinPositiveOf(::Type{F}) where {F<:Binary} = _rawvalue(F, _cu(F, 1))

"""
    MaxSubnormalOf(F)

The largest subnormal datum, code `2^(P-1) - 1`. For `P == 1` that code is 0 —
the format has no subnormals and this returns its zero.
"""
MaxSubnormalOf(::Type{F}) where {F<:Binary} =
    _rawvalue(F, _cu(F, (1 << (Int(PrecisionOf(F)) - 1)) - 1))

"""
    MinNormalOf(F)

The smallest normal datum, code `2^(P-1)`.
"""
MinNormalOf(::Type{F}) where {F<:Binary} =
    _rawvalue(F, _cu(F, 1 << (Int(PrecisionOf(F)) - 1)))

for f in (:MaxFiniteOf, :MinFiniteOf, :MinPositiveOf, :MaxSubnormalOf, :MinNormalOf)
    @eval $f(::Type{Union{}}) = throw(ArgumentError("Union{} has no datums"))   # analysis totality
    @eval $f(::Type{BV}) where {BV<:BinaryValue} = $f(BinaryFormatOf(BV))
    @eval $f(x::BinaryValue) = $f(BinaryFormatOf(x))
end

# ωEncode: canonical integer form → code point
#
# Input is value = sign · S · 2^Q with S ∈ 0:2^P (S == 2^P is the next-binade
# carry, draft §4.7.4 NOTE 4). Precondition: the value is in the datum set of F
# — upheld by RoundToPrecision ∘ Saturate, the only callers besides the tests.
"""
    encode(F, sign, S, Q)

The code point of the datum `sign · S · 2^Q` of format `F`, from canonical
integer form (`S ∈ 0:2^P`; `S == 2^P` carries into the next binade).

Kernel-internal half of the codec; the inverse of the field split `decode`
performs. Not exported, and not a user entry point — values enter a format only
through the projection engine.
"""
@inline function encode(::Type{F}, sign::Int, S::Int64, Q::Int64) where {F<:Binary}
    S == 0 && return _cu(F, 0)
    P = Int(PrecisionOf(F))
    hidden = Int64(1) << (P - 1)            # implicit-bit weight; also the first normal S
    if S == (Int64(1) << P)                 # carry into the next binade
        S = hidden
        Q += 1
    end
    local c::CodeType(F)
    if S < hidden                           # subnormal: no exponent field to write
        c = _cu(F, S)
    else
        Eb = Int(Q) + P - 1 + ExponentBiasOf(F)
        c = _cu(F, (S & (hidden - 1)) + (Int64(Eb) << (P - 1)))
    end
    (is_signed(F) && sign < 0) && (c |= signmask(F))
    c
end