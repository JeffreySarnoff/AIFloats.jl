# ωProject — the single write path into a code point
#
# project = ωRoundToPrecision → ωSaturate → ωEncode. Nothing else produces a
# code point from a value; every constructor-from-value, every operation, and
# every table entry enters here.

"""
    project(F, ρ, X; R = 0, sticky = 0) -> BinaryValue

Map the value `X` (any float carrier — `Float64`, `Float128`, `BigFloat`) onto
format `F` under projection `ρ`: round to `F`'s precision, saturate, encode.
The single write path into a code point.

- `R` is the pre-drawn random integer in `[0, 2^N)` for a stochastic ρ (`0`
  otherwise). Projection is monotone in the value **at fixed R** — the property
  the interval oracle relies on.
- `sticky ∈ {-1, 0, +1}` declares the true value to be `X + sticky·ε` for an
  infinitesimal `ε > 0`, letting an enclosure endpoint stand in for an
  irrational value without losing direction information.

# Examples

```jldoctest
julia> F = Binary(8, 4, SIGNED, EXTENDED);

julia> decode(project(F, RTE_SF, 1.6))
1.625

julia> decode(project(F, RTZ_SF, 1.6))
1.5

julia> decode(project(F, RTE_SF, 1.0e9))   # saturates at the max finite datum
224.0
```
"""
function project(::Type{F}, ρ::Projection{RM,SM}, X;
                 R::Int = 0, sticky::Int = 0) where
        {F<:Binary, RM<:RoundingMode, SM<:SaturationMode}
    isnan(X) && return rawvalue(F, nan_code(F))
    P = Int(PrecisionOf(F))
    B = ExponentBiasOf(F)
    r = round_to_precision(P, B, RoundOf(ρ), X, R, sticky)
    rawvalue(F, saturate(F, ρ, r))
end
project(::Type{BV}, ρ::Projection, X; kw...) where {BV<:BinaryValue} =
    project(BinaryFormatOf(BV), ρ, X; kw...)

# ---- the interval oracle ----------------------------------------------------
#
# Resolves an enclosure to a code point for ANY mode: if the endpoints are
# equal the value is exact; otherwise the truth lies in the OPEN interval
# (d, u) — directed correct rounding of a non-representable value moves
# strictly — and projection is monotone in the value at fixed R, so agreement
# of the two sticky-tagged endpoint projections is a proof. Disagreement means
# a grid point sits inside the interval: escalate precision (Ziv's strategy
# with a decidable ceiling).

# the ceiling is DERIVED: two distinct grid points of F differ by at least
# 2^-(2B + 2P) relatively, and directed/stochastic answers can hinge on which
# side of a datum the value falls — reachable cases need ~2B bits
@inline _intervalcap(::Type{F}) where {F<:Binary} = max(4096, bigprec(F) + 64)

"""
    project_interval(F, ρ, f; R = 0) -> BinaryValue

Project a lazily-refined enclosure onto `F`: `f(prec)` must return directed
MPFR endpoints `(d, u)` with the true value in `[d, u]`, tightening as `prec`
grows. Sound for every rounding mode, including stochastic, at fixed `R`.
Not exported.
"""
function project_interval(::Type{F}, ρ::Projection, f; R::Int = 0) where {F<:Binary}
    _project_interval(F, ρ, f, R, _intervalcap(F))
end

function _project_interval(::Type{F}, ρ::Projection, f, R::Int, maxprec::Int) where {F<:Binary}
    maxprec >= 2 || throw(ArgumentError("project_interval needs maxprec >= 2"))
    # Ziv's first rung. 64 is not a resolution estimate — `_ladderprec` raises
    # it to the operands' own width plus a margin (72 for Float64 operands, 136
    # for Float128), so this constant says "start where the operands put you"
    # rather than naming a precision.
    #
    # Measured over a sweep of ten Group B rows across K = 16 P = 5, K = 16
    # P = 2 and K = 8 P = 4, every code point, resolving each enclosure to a
    # code point: 64 → 14.4 ms, 128 → 14.8, 192 → 16.4, 256 → 17.5, 384 → 20.2.
    # 97.6% of cases resolve on the FIRST rung whatever the start, so a high
    # start is pure waste on almost everything; the 2.4% tail that needs 3–6
    # rungs pays one extra doubling and is far outweighed. Correctness does not
    # depend on this value at all — the loop escalates to `maxprec` regardless —
    # only the number of MPFR calls does.
    prec = min(64, maxprec)
    while true
        d, u = f(prec)
        if isequal(d, u)
            return project(F, ρ, d; R, sticky = 0)          # exact
        end
        cd = project(F, ρ, d; R, sticky = +1)
        cu = project(F, ρ, u; R, sticky = -1)
        codepoint(cd) == codepoint(cu) && return cd
        prec >= maxprec && error("project_interval: unresolved at $maxprec bits for $(string(F))")
        prec = min(2prec, maxprec)
    end
end