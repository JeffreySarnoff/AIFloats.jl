# ωSaturate — the outcome currency is a CODE POINT
#
# A symbol protocol here would put a five-way === chain at the centre of the
# single write path, and a mistyped row would fall through to the NaN catch-all
# at run time; returning the code point makes a bad row an undefined-variable
# error at load time. (An intermediate tag type was tried in SmallFloats and
# rejected: a six-way Union exceeds the union-splitting budget.)

# the extremal magnitude in canonical (S, Q) form, from the CODE point — the
# same field split as decode, kept in integer space; folds per format
@inline function _extremal_SQ(::Type{F}) where {F<:Binary}
    P = Int(PrecisionOf(F))
    B = ExponentBiasOf(F)
    hidden = Int64(1) << (P - 1)
    c = _maxfinite_code(F)
    tsig = Int64(c & _cu(F, hidden - 1))
    Eb = Int(c >> (P - 1))
    S = Eb == 0 ? tsig : tsig + hidden
    Q = Int64((Eb == 0 ? 1 : Eb) - B - (P - 1))
    (S, Q)
end

# the dispatcher: NaN row, zero row, the (Q, then S) lexicographic range test —
# sound because rounded canonical forms and the extremal form share one
# lexicographic order (subnormals and the lowest normal binade share
# Q = 2 − B − P), signed formats are sign–magnitude symmetric, unsigned
# underflow is simply sign < 0, and HUGEQ exceeds every Q_hi.
"""
    saturate(F, \u03c1, r::Rounded) -> code point

Interim Report \u00a74.7.5 `\u03c9Saturate`, followed by the encode: map the already
rounded value `r` onto a code point of format `F` under `\u03c1`'s saturation mode.

The three modes differ only outside `F`'s finite range, and they differ from
each other only on a **genuine infinity**:

| Mode | Out-of-range finite | `\u00b1Inf` reaching saturation |
|:--|:--|:--|
| [`SF`](@ref) | clamps to the extremal finite | clamps to the extremal finite |
| [`SP`](@ref) | clamps to the extremal finite | kept when `F` can represent it, else clamped |
| [`SN`](@ref) | extremal finite when the rounding direction points back into range, else the infinity, else NaN | the infinity when `F` is `EXTENDED` and signed as needed, else NaN |

Under `SN`, an unsigned extended format has no `-Inf`, so a negative overflow
is NaN; a `FINITE` format has no infinity at all, so every out-of-range result
is NaN. The rounding mode is passed in because \u00a74.7.5 needs it to resolve those
directed rows — saturation itself never rounds.

This is the saturation half of [`project`](@ref);
[`round_to_precision`](@ref) is the other half.

Not exported; call it as `AIFloats.saturate`.
"""
@inline function saturate(::Type{F}, ρ::Projection{RM,SM}, r::Rounded) where
        {F<:Binary, RM<:RoundingMode, SM<:SaturationMode}
    r.kind == KIND_NAN && return nan_code(F)
    over = false
    under = false
    if r.kind == KIND_FIN
        r.S == 0 && return _cu(F, 0)                      # zero is always in range
        Shi, Qhi = _extremal_SQ(F)
        overmag = (r.Q > Qhi) | ((r.Q == Qhi) & (r.S > Shi))
        over  = overmag & (r.sign > 0)
        under = is_signed(F) ? (overmag & (r.sign < 0)) : (r.sign < 0)
        (!over & !under) && return encode(F, Int(r.sign), r.S, r.Q)
    end
    _saturate(SatOf(ρ), RoundOf(ρ), F, r, over, under)
end

# SatFinite: clamp EVERYTHING to the finite range — a genuine infinity too
function _saturate(::ρSF, μ::RoundingMode, ::Type{F}, r::Rounded,
                   over::Bool, under::Bool) where {F<:Binary}
    r.kind == KIND_PINF && return _maxfinite_code(F)
    r.kind == KIND_NINF && return _minfinite_code(F)
    over  && return _maxfinite_code(F)
    under && return _minfinite_code(F)
    nan_code(F)     # unreachable for well-formed input; total anyway
end

# SatPropagate: keep a representable infinity, clamp the rest — falling back
# to the extremal finite exactly where the encoding cannot express it
function _saturate(::ρSP, μ::RoundingMode, ::Type{F}, r::Rounded,
                   over::Bool, under::Bool) where {F<:Binary}
    if r.kind == KIND_PINF
        return is_extended(F) ? posinf_code(F) : _maxfinite_code(F)
    elseif r.kind == KIND_NINF
        return (is_signed(F) && is_extended(F)) ? neginf_code(F) : _minfinite_code(F)
    end
    over  && return _maxfinite_code(F)
    under && return _minfinite_code(F)
    nan_code(F)
end

# SatNone: the draft's direction/signedness/domain-governed rows — a directed
# rounding that points back into the range delivers the extremal finite; an
# EXTENDED domain spends its infinity; everything else is NaN.
function _saturate(::ρSN, μ::RM, ::Type{F}, r::Rounded,
                   over::Bool, under::Bool) where {RM<:RoundingMode, F<:Binary}
    if r.kind == KIND_FIN
        over  && RM <: Union{ρRTZ, ρRTN} && return _maxfinite_code(F)
        under && RM <: Union{ρRTZ, ρRTP} && return _minfinite_code(F)
    end
    if is_extended(F)
        (over  || r.kind == KIND_PINF) && return posinf_code(F)
        if under || r.kind == KIND_NINF
            return is_signed(F) ? neginf_code(F) : nan_code(F)
        end
    end
    nan_code(F)
end