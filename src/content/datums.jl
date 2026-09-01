# datum-level API: predicates, the total order, neighbors, classification
#
# Everything here reads the code point; nothing decodes unless the value itself
# is the answer.

# ---- predicates ------------------------------------------------------------

Base.iszero(x::BinaryValue) = iszero(codepoint(x))
Base.isnan(x::BinaryValue)  = codepoint(x) == nan_code(x)
Base.isinf(x::BinaryValue)  = is_extended(x) &&
    (codepoint(x) == posinf_code(x) ||
     (is_signed(x) && codepoint(x) == neginf_code(x)))
Base.isfinite(x::BinaryValue) = !(isnan(x) | isinf(x))

function Base.signbit(x::BinaryValue)
    is_signed(x) || return false
    isnan(x) && return false
    codepoint(x) > signmask(x)          # == signmask is the NaN slot
end

"""
    issubnormal(x::BinaryValue)

Whether the datum is subnormal: magnitude code strictly between 0 and
`2^(P-1)`. A `P == 1` format has no subnormals.
"""
function Base.issubnormal(x::BinaryValue)
    isfinite(x) || return false
    c = codepoint(x)
    m = (is_signed(x) && c >= signmask(x)) ? c - signmask(x) : c
    U = CodeType(x)
    zero(U) < m < (one(U) << (Int(PrecisionOf(x)) - 1))
end

# ---- the total order (draft §4.12.1): NaN FIRST, below −Inf ----------------
#
# order_key maps every datum to a strictly increasing unsigned key. Key 0 is
# reserved for the single NaN — the opposite end from Float64 sorting, and a
# deliberate divergence. The key type is one unit wider than the code
# (orderkeytype), because datum keys run 1:2^K and the top one must not wrap
# onto the NaN key.

"""
    order_key(x::BinaryValue)

The datum's rank in the format's total order, as an unsigned key. NaN gets key
`0` — the draft's total order places NaN first, **below** −Inf; every other
datum's key is its order position plus one.

Not exported.
"""
@inline function order_key(x::BinaryValue)
    T = typeof(x)
    O = orderkeytype(T)
    c = codepoint(x)
    isnan(x) && return zero(O)
    is_signed(T) || return O(c) + one(O)
    sm = signmask(T)
    if c >= sm                                   # negative half, magnitude-reversed
        O(sm) - O(c - sm)
    else
        O(sm) + O(c) + one(O)
    end
end

# ---- classification --------------------------------------------------------

"""
    FPClass

The eight-way classification of a datum: `ClassNaN`, `ClassNegInf`,
`ClassNegNormal`, `ClassNegSubnormal`, `ClassZero`, `ClassPosSubnormal`,
`ClassPosNormal`, `ClassPosInf` — in total-order position.
"""
@enum FPClass::Int8 begin
    ClassNaN = 0
    ClassNegInf
    ClassNegNormal
    ClassNegSubnormal
    ClassZero
    ClassPosSubnormal
    ClassPosNormal
    ClassPosInf
end

"""
    Class(x::BinaryValue)

The datum's [`FPClass`](@ref).

# Examples

```jldoctest
julia> F = Binary(8, 4, SIGNED, EXTENDED);

julia> Class(MaxFiniteOf(F)), Class(BinaryValue(F, AIFloats.nan_code(F)))
(ClassPosNormal, ClassNaN)
```
"""
function Class(x::BinaryValue)
    isnan(x) && return ClassNaN
    iszero(x) && return ClassZero
    neg = signbit(x)
    if isinf(x)
        return neg ? ClassNegInf : ClassPosInf
    end
    if issubnormal(x)
        return neg ? ClassNegSubnormal : ClassPosSubnormal
    end
    neg ? ClassNegNormal : ClassPosNormal
end

# ---- lattice neighbors -----------------------------------------------------
#
# ±1 steps along the total order, running OFF the lattice into NaN at both
# ends (the draft's NextUp/NextDown; unlike Base's saturating nextfloat).
# Written as code arithmetic with explicit pivots, not as key arithmetic —
# order_key's key space has a deliberate gap at signmask (keys are ordered,
# not contiguous), which key±1 stepping would fall into.

"""
    NextGreaterThan(x::BinaryValue)

The next datum above `x` in the total order. The step off the top of the
lattice returns NaN; `NextGreaterThan(NaN)` is the bottom datum — NaN sits
below everything in the total order.
"""
function NextGreaterThan(x::BinaryValue{F,U}) where {F,U}
    isnan(x) && return _rawvalue(F, _bottom_datum_code(F))       # NaN is first
    c = codepoint(x)
    if is_unsigned(F)
        # ascending order IS ascending code; the top datum sits just below NaN
        return c >= nan_code(F) - one(U) ? _rawvalue(F, nan_code(F)) :
                                           _rawvalue(F, c + one(U))
    end
    sm = signmask(F)
    if c > sm                               # negative half: up means magnitude down
        c == sm + one(U) && return _rawvalue(F, zero(U))         # −MinPositive → 0
        _rawvalue(F, c - one(U))
    else                                    # non-negative half (c < sm; c == sm is NaN)
        c == sm - one(U) && return _rawvalue(F, nan_code(F))     # off the top
        _rawvalue(F, c + one(U))
    end
end

"""
    NextLessThan(x::BinaryValue)

The next datum below `x` in the total order; the step below the bottom datum —
and below NaN itself — is NaN, the order's floor.
"""
function NextLessThan(x::BinaryValue{F,U}) where {F,U}
    isnan(x) && return _rawvalue(F, nan_code(F))                 # nothing below NaN
    c = codepoint(x)
    if is_unsigned(F)
        return iszero(c) ? _rawvalue(F, nan_code(F)) : _rawvalue(F, c - one(U))
    end
    sm = signmask(F)
    if c > sm                               # negative half: down means magnitude up
        c == codemask(F) && return _rawvalue(F, nan_code(F))     # below the bottom
        _rawvalue(F, c + one(U))
    else                                    # non-negative half
        iszero(c) && return _rawvalue(F, sm + one(U))            # 0 → −MinPositive
        _rawvalue(F, c - one(U))
    end
end

# the datum at the very bottom of the order (excluding NaN)
_bottom_datum_code(::Type{F}) where {F<:Binary} =
    is_signed(F) ? codemask(F) : _cu(F, 0)