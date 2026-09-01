# blocks: shared-scale block formats, scaled operations, reductions (draft §5)
#
# A block is (scale, elements). The elementwise §5.4 schema is implemented
# ONCE — decode all operand blocks → ω-op lanewise → blockproject against the
# supplied result scale — and the Block*/Scaled* variant of every registry
# operation is generated from it (invariant 7: no hand-written per-op
# variants).
#
# This is the correctness cut, like ops/oracle.jl: a lane result is an exact
# carrier value (Float64/Float128/BigFloat) or an Enclosure, and dividing it by
# the result scale is a directed MPFR enclosure resolved by project_interval.
# The one filter kept is the cheap exact one — a Float64 quotient certified by
# fma — because it is what makes the P == 1 (power-of-two scale, MX/E8M0) case
# an exact projection with no interval work. SmallFloats' Float128 quotient
# cascade is not ported; a homogeneous Float64 lane fast path for blockdecode
# and Dyadic-accumulated reductions landed as Step 8 of docs/implmentplan.md.

"""
    Block{B, S<:BinaryValue, E<:BinaryValue}

A P3109 block `(s, (x₁ … x_B))`: a scale datum of type `S` and `B ≥ 1` element
datums of type `E` (draft §5). `isbits`.

```julia
Block(Binary8p1uf(4.0), (Binary5p2se(3.0), Binary5p2se(0.5)))
Block(s, x1, x2, x3)          # varargs form
```
"""
struct Block{B, S<:BinaryValue, E<:BinaryValue}
    s::S
    x::NTuple{B,E}
    # the element type is spelled on the first lane, not as NTuple{B,E}: an
    # empty tuple would leave E unbound. B ≥ 1 is therefore a signature
    # property; the empty case falls to the explicit refusal below.
    function Block(s::S, x::Tuple{E, Vararg{E, Bm1}}) where {Bm1, S<:BinaryValue, E<:BinaryValue}
        new{Bm1 + 1, S, E}(s, x)
    end
end
Block(::BinaryValue, ::Tuple{}) = throw(ArgumentError("block size B must be ≥ 1"))
Block(s::BinaryValue, xs::BinaryValue...) = Block(s, xs)

"""The number of elements `B` of a block or block type."""
blocksize(::Block{B}) where {B} = B
blocksize(::Type{<:Block{B}}) where {B} = B
"""The scale's [`Binary`](@ref) format."""
scaleformat(::Block{B,S,E}) where {B,S,E} = BinaryFormatOf(S)
scaleformat(::Type{Block{B,S,E}}) where {B,S,E} = BinaryFormatOf(S)
"""The elements' [`Binary`](@ref) format."""
elemformat(::Block{B,S,E}) where {B,S,E} = BinaryFormatOf(E)
elemformat(::Type{Block{B,S,E}}) where {B,S,E} = BinaryFormatOf(E)

Base.:(==)(a::Block{B}, b::Block{B}) where {B} = a.s == b.s && a.x == b.x
Base.isequal(a::Block{B}, b::Block{B}) where {B} = isequal(a.s, b.s) && all(map(isequal, a.x, b.x))

function Base.show(io::IO, b::Block{B}) where {B}
    print(io, "Block(", b.s, ", (")
    join(io, b.x, ", ")
    B == 1 && print(io, ",")
    print(io, "))")
end

# ---- carrier harmonizing -----------------------------------------------------
# ωeval's exact selections are homogeneous in the carrier by design (a mixed
# call is a caller bug there). Block lanes can legitimately mix — one block's
# products stayed Float64, another's escalated to BigFloat — so lanes are
# brought to one carrier before ωeval: identical types pass through, anything
# else lifts EXACTLY to BigFloat.
@inline _samecarrier(x) = (x,)
@inline _samecarrier(x::C, y::C) where {C} = (x, y)
@inline _samecarrier(x::C, y::C, z::C) where {C} = (x, y, z)
# float128use.md §4 proposed adding exact Float64/Float128 mixed methods here.
# TRIED AND REJECTED ON MEASUREMENT: a Float64 does widen to Float128 exactly,
# but the eight extra methods widened `_samecarrier`'s inferred return at the
# generated call sites, and ScaledAdd went 192 -> 312 ns and 7 -> 15
# allocations for no measurable gain anywhere. The plan's own warning ("avoid a
# broad implementation until inference has been measured") applies to a spray
# of narrow methods too. The mixed block reduction it hoped to fix does not
# even route through here — it uses `_reduce_add_value`/`_exactbig`.
@inline _samecarrier(x, y) = (_exactbig(x), _exactbig(y))
@inline _samecarrier(x, y, z) = (_exactbig(x), _exactbig(y), _exactbig(z))

# The fold carrier for ConvertToBlockMaxAbsFinite: the lanes' own when they
# agree, Float128 for the one mixture that widens exactly, BigFloat otherwise.
# Each branch seeds with ITS carrier's NaN so the draft's "NaN loses to any
# finite operand" contract is unchanged.
@inline _maxfold(M, ::Type{C}) where {C} =
    foldl((a, m) -> ωeval(Val(:MaximumFinite), a, m), M; init = _cnan(C))
# `Block` guarantees B ≥ 1, so an empty tuple never reaches here — but it
# matches every NTuple method below at B = 0, and an unreachable ambiguity is
# still an ambiguity (Aqua fails on it). Resolved explicitly rather than left.
@inline _maxabs_fold(M::Tuple{}) = _maxfold(M, BigFloat)
@inline _maxabs_fold(M::NTuple{B,Float64}) where {B}  = _maxfold(M, Float64)
@inline _maxabs_fold(M::NTuple{B,Float128}) where {B} = _maxfold(M, Float128)
@inline function _maxabs_fold(M::NTuple{B,Union{Float64,Float128}}) where {B}
    _maxfold(map(Float128, M), Float128)          # exact widening
end
@inline _maxabs_fold(M) = _maxfold(map(_exactbig, M), BigFloat)

# ---- ωBlockDecode (draft §5.1.1) --------------------------------------------
# Is this block's arithmetic entirely Float64? Both `datumcarrier` calls depend
# only on the type parameters, so this folds at compile time and the fast lane
# below costs nothing for a block whose carriers are wider.
@inline _f64_block(::Type{S}, ::Type{E}) where {S,E} =
    datumcarrier(BinaryFormatOf(S)) === Float64 && datumcarrier(BinaryFormatOf(E)) === Float64

"""
    _f64_lanes(b) -> (NTuple{B,Float64}, Bool)

The lanes computed in Float64 together with a proof they are EXACT. Returns a
fully concrete pair — never a union — so nothing is boxed; callers that need
the general carrier go through [`blockdecode`](@ref) instead. `ok == false`
means at least one lane is inexact or not finite, and the caller must fall back
to the generic path, which is where the draft's ∞/NaN fold algebra lives.
"""
@inline function _f64_lanes(b::Block{B,S,E}) where {B,S,E}
    Sv = decode(b.s)::Float64
    xs = ntuple(i -> decode(b.x[i])::Float64, Val(B))
    # the draft has a SINGLE zero: ωMultiply returns +0 for a zero product,
    # where raw multiplication yields −0 whenever the signs differ. Missing
    # this made the fast lane disagree with the generic one on sign of zero
    # (caught by test-blocks.jl's "blockdecode ≡ lane semantics").
    lanes = ntuple(i -> (p = Sv * xs[i]; iszero(p) ? 0.0 : p), Val(B))
    # a NaN or ±∞ lane fails isfinite, so specials always take the generic path
    ok = all(i -> isfinite(lanes[i]) && fma(Sv, xs[i], -lanes[i]) == 0.0, 1:B)
    (lanes, ok)
end

"""
    blockdecode(b::Block) -> NTuple{B}

The values the block denotes: per lane `ωMultiply(decode(s), decode(xᵢ))`,
exact on a carrier (Float64 when the product is exactly representable there,
BigFloat otherwise). The draft's fold algebra applies: `0 · ∞` and NaN lanes
are NaN. Not exported.
"""
@inline function blockdecode(b::Block{B,S,E}) where {B,S,E}
    # The values here are the SAME ones the generic path produces — the point is
    # inference. `ωeval`'s return is a carrier union, so `ntuple` boxes every
    # lane even when all of them land as Float64 (measured: 17 allocations for a
    # B = 16 block whose result was already NTuple{16,Float64}).
    if _f64_block(S, E)
        lanes, ok = _f64_lanes(b)
        ok && return lanes
    end
    Sv = decode(b.s)
    ntuple(i -> ωeval(Val(:Multiply), Sv, decode(b.x[i])), Val(B))
end

# ---- ωBlockProject element pipeline (draft §5.1.2) --------------------------
_res_isnan(v::CarrierValue) = isnan(v)
_res_isnan(::Enclosure) = false                 # enclosures are finite by construction
_res_sign(v::CarrierValue) = Float64(sign(v))
function _res_sign(e::Enclosure)
    d, u = e.f(256)
    s = sign(d)
    Float64(iszero(s) ? sign(u) : s)
end

# enclosure of (value of res)/S for finite nonzero S. The divisor enters as an
# EXACT BigFloat at its own width (never promoted at ambient precision, which
# would round the divisor and enclose the wrong quotient); the working
# precision is floored above both operands' widths.
@inline _divprec(prec::Int, S, extra::Int = 0) = max(prec, precision(_exactbig(S)) + extra + 8)

function _encl_div_scale(res::CarrierValue, S)
    Enclosure(prec -> begin
        p = _divprec(prec, S, precision(_exactbig(res)))
        setprecision(BigFloat, p) do
            b = _exactbig(res); s = _exactbig(S)            # both exact ⇒ one rounded op
            (setrounding(() -> b / s, BigFloat, RoundDown),
             setrounding(() -> b / s, BigFloat, RoundUp))
        end
    end)
end
function _encl_div_scale(res::Enclosure, S)
    Enclosure(prec -> begin
        p = _divprec(prec, S)
        d, u = res.f(p)
        setprecision(BigFloat, p) do
            s = _exactbig(S)
            if s > 0
                (setrounding(() -> d / s, BigFloat, RoundDown),
                 setrounding(() -> u / s, BigFloat, RoundUp))
            else
                (setrounding(() -> u / s, BigFloat, RoundDown),
                 setrounding(() -> d / s, BigFloat, RoundUp))
            end
        end
    end)
end

# one element of ωBlockProject: the draft's S-special rows, then ωDivide ∘ ωProject
function _bp_element(::Type{FR}, ρ::Projection, R::Int, res, Sdat) where {FR<:Binary}
    (isnan(Sdat) || _res_isnan(res)) && return rawvalue(FR, nan_code(FR))
    iszero(Sdat) && return project(FR, ρ, 0.0; R)
    if isinf(Sdat)
        # sgn(Xᵢ) · sgn(S) ∈ {−1, 0, +1}
        return project(FR, ρ, _res_sign(res) * Float64(sign(Sdat)); R)
    end
    if res isa Float64 && Sdat isa Float64
        isinf(res) && return project(FR, ρ, sign(Sdat) * res; R)   # ωDivide(±∞, finite)
        iszero(res) && return project(FR, ρ, 0.0; R)
        q = res / Sdat
        (isfinite(q) && fma(q, Sdat, -res) == 0.0) && return project(FR, ρ, q; R)
    elseif res isa Float128 && Sdat isa Float128
        isinf(res) && return project(FR, ρ, (signbit(res) ⊻ signbit(Sdat)) ? -Inf : Inf; R)
        iszero(res) && return project(FR, ρ, 0.0; R)
        q = _try_div128(res, Sdat)
        q === nothing || return project(FR, ρ, q; R)
    elseif res isa CarrierValue
        isinf(res) && return project(FR, ρ, (signbit(res) ⊻ signbit(Sdat)) ? -Inf : Inf; R)
        iszero(res) && return project(FR, ρ, 0.0; R)
    end
    project_interval(FR, ρ, _encl_div_scale(res, Sdat).f; R)
end

"""
    blockproject(FR, ρ, sr, Z; rng) -> Block

ωBlockProject (draft §5.1.2): each lane result in `Z` (a carrier value or an
enclosure) divided by the result scale `sr` and projected into `FR` under `ρ`;
the block returned carries `sr`. Not exported.
"""
function blockproject(::Type{FR}, ρ::Projection, sr::BinaryValue, Z::NTuple{B,Any};
                      rng::MaybeRNG = nothing) where {FR<:Binary, B}
    Sdat = decode(sr)
    rr = isstochastic(ρ) ? _resolve_rng(rng) : nothing
    elems = ntuple(i -> _bp_element(FR, ρ, _drawR(ρ, rr, nothing), Z[i], Sdat), Val(B))
    Block(sr, elems)
end
blockproject(::Type{FR}, ρ::Projection, sr, Z; kw...) where {FR<:BinaryValue} =
    blockproject(BinaryFormatOf(FR), ρ, sr, Z; kw...)
blockproject(FR::Binary, ρ::Projection, sr, Z; kw...) =
    blockproject(typeof(FR), ρ, sr, Z; kw...)

# ---- generated elementwise BlockOp / ScaledOp surface (draft §5.4 / §5.5) ---
#   BlockOp(FR, ρ, b1[, b2[, b3]], sr; rng)  — operand blocks, result scale sr
#   ScaledOp(FR, ρ, s1, x1[, s2, x2[, s3, x3]]; rng) — (scale, element) pairs,
#                                            unit result scale
for op in OP_REGISTRY
    op.name === :Convert && continue
    name = op.name
    bname = Symbol(:Block, name); sname = Symbol(:Scaled, name); V = Val{name}
    bs = [Symbol(:b, i) for i in 1:op.arity]
    Xs = [Symbol(:X, i) for i in 1:op.arity]
    block_params = [:($b::Block{B}) for b in bs]
    decode_lanes = [:($(Xs[i]) = blockdecode($(bs[i]))) for i in 1:op.arity]
    lane_i = [:($(Xs[i])[i]) for i in 1:op.arity]
    ss = [Symbol(:s, i) for i in 1:op.arity]
    xs = [Symbol(:x, i) for i in 1:op.arity]
    scaled_params = collect(Iterators.flatten((:($(ss[i])::BinaryValue), :($(xs[i])::BinaryValue))
                                              for i in 1:op.arity))
    Xa = [Symbol(:Xa, i) for i in 1:op.arity]
    scale_products = [:($(Xa[i]) = ωeval(Val(:Multiply), decode($(ss[i])), decode($(xs[i]))))
                      for i in 1:op.arity]
    unit_blocks = foldl((a, b) -> :($a && $b), [:(isone($(bs[i]).s)) for i in 1:op.arity])
    unit_scales = foldl((a, b) -> :($a && $b), [:(isone($(ss[i]))) for i in 1:op.arity])
    @eval begin
        function $bname(fr::Type{<:Binary}, ρ::Projection, $(block_params...), sr::BinaryValue;
                        rng::MaybeRNG = nothing) where {B}
            if isone(sr) && $unit_blocks
                rr = isstochastic(ρ) ? _resolve_rng(rng) : nothing
                elems = ntuple(i -> $name(fr, ρ, $((:($(bs[j]).x[i]) for j in 1:op.arity)...);
                                                  rng=rr), Val(B))
                return Block(sr, elems)
            end
            $(decode_lanes...)
            Z = ntuple(i -> _nosticky($V(), _samecarrier($(lane_i...))...), Val(B))
            blockproject(fr, ρ, sr, Z; rng)
        end
        @inline $bname(fr::Type{<:BinaryValue}, ρ::Projection, $(block_params...),
                       sr::BinaryValue; kw...) where {B} =
            $bname(BinaryFormatOf(fr), ρ, $(bs...), sr; kw...)
        @inline $bname(fr::Binary, ρ::Projection, $(block_params...),
                       sr::BinaryValue; kw...) where {B} =
            $bname(typeof(fr), ρ, $(bs...), sr; kw...)
        function $sname(fr::Type{<:Binary}, ρ::Projection, $(scaled_params...);
                        rng::MaybeRNG = nothing)
            $unit_scales && return $name(fr, ρ, $(xs...); rng)
            $(scale_products...)
            res = _nosticky($V(), _samecarrier($(Xa...))...)
            _bp_element(fr, ρ, _drawR(ρ, rng, nothing), res, 1.0)
        end
        @inline $sname(fr::Type{<:BinaryValue}, ρ::Projection, $(scaled_params...); kw...) =
            $sname(BinaryFormatOf(fr), ρ, $(ss[1]), $(xs[1]),
                   $((Iterators.flatten((ss[i], xs[i]) for i in 2:op.arity))...); kw...)
        @inline $sname(fr::Binary, ρ::Projection, $(scaled_params...); kw...) =
            $sname(typeof(fr), ρ, $(ss[1]), $(xs[1]),
                   $((Iterators.flatten((ss[i], xs[i]) for i in 2:op.arity))...); kw...)
        export $bname, $sname
    end
end

# ---- reductions (draft §5.3) -------------------------------------------------
# specials by the fold algebra, then an EXACT sum/product at a precision
# DERIVED from the block's formats and length — never a constant.
#   sums     — lanes span 2(B_S + B_E) binades and carry P_S + P_E bits each,
#              plus ⌈log₂ B⌉ carry bits
#   products — the exponent only shifts; the significand is the SUM over lanes
@inline _log2ceil(B::Int) = 8 * sizeof(Int) - leading_zeros(B - 1 > 0 ? B - 1 : 1)
@inline _lane_sum_prec(::Type{FS}, ::Type{FE}, B::Int) where {FS<:Binary, FE<:Binary} =
    2 * (ExponentBiasOf(FS) + ExponentBiasOf(FE) + Int(PrecisionOf(FS)) + Int(PrecisionOf(FE))) +
    64 + _log2ceil(B)
@inline _lane_prod_prec(::Type{FS}, ::Type{FE}, B::Int) where {FS<:Binary, FE<:Binary} =
    B * (Int(PrecisionOf(FS)) + Int(PrecisionOf(FE))) + 128

# ---- the exact accumulator ---------------------------------------------------
# `Dyadic` IS S::Int128 · 2^Q — the exact fixed-point accumulator these
# reductions want, with the alignment and width preconditions already derived
# and already covered by test-dyadic.jl. It is called here, not reimplemented.
#
# `add_dy` THROWS past its exact band, so this mirrors `add_dy_checked`'s
# preconditions and returns `nothing` instead, letting the caller fall back to
# the BigFloat path that stays live as the oracle. A wide spread is genuinely
# reachable — a K = 16, P = 1 element format has B = 32768.
@inline _dyadic_sum(::Tuple{}) = DYADIC_ZERO
function _dyadic_sum(X::NTuple{B,Float64}) where {B}
    acc = DYADIC_ZERO
    @inbounds for i in 1:B
        v = X[i]
        iszero(v) && continue
        d = Dyadic(v)                                  # exact for a finite Float64
        if iszero(acc.S)
            acc = d
            continue
        end
        hi, lo = acc.Q >= d.Q ? (acc, d) : (d, acc)
        Δ = Int(hi.Q - lo.Q)
        (Δ > DYADIC_ALIGN_MAX || nbits_dy(hi.S) + Δ > 126) && return nothing
        acc = add_dy(acc, d)
    end
    acc
end

@inline _exact_dyadic(x::Float64) = Dyadic(x)
@inline _exact_dyadic(x::Float128) = _dyadic128(x)
@inline _exact_dyadic(x::Dyadic) = x

# Exact finite block lanes for every carrier rung. A scale and datum contribute
# at most 16 significant bits each; the guarded product therefore starts at no
# more than 32 bits. Specials refuse to the existing fold algebra.
function _dyadic_lanes(b::Block{B}) where {B}
    s = decode(b.s)
    isfinite(s) || return nothing
    sd = _exact_dyadic(s)
    xs = ntuple(i -> decode(b.x[i]), Val(B))
    all(isfinite, xs) || return nothing
    ds = ntuple(i -> _exact_dyadic(xs[i]), Val(B))
    all(i -> nbits_dy(sd.S) + nbits_dy(ds[i].S) <= 96, 1:B) || return nothing
    ntuple(i -> mul_dy(sd, ds[i]), Val(B))
end

function _dyadic_sum(X::NTuple{B,Dyadic}) where {B}
    acc = DYADIC_ZERO
    @inbounds for i in 1:B
        d = X[i]
        iszero(d.S) && continue
        if iszero(acc.S)
            acc = d
            continue
        end
        hi, lo = acc.Q >= d.Q ? (acc, d) : (d, acc)
        Δ = Int(hi.Q - lo.Q)
        (Δ > DYADIC_ALIGN_MAX || nbits_dy(hi.S) + Δ > 126) && return nothing
        acc = add_dy(acc, d)
    end
    acc
end

# the B lane products, exact in Float64 and certified so, or nothing. The fma
# test is the same proof `_f64_lanes` uses for S·x; the magnitude floor is the
# same one ops/oracle.jl derives for FMA — below it a nonzero residual can
# itself underflow and certify an inexact product. Zero products normalize to
# +0, matching the draft's single zero.
function _exact_lane_products(X::NTuple{B,Float64}, Y::NTuple{B,Float64}) where {B}
    p = ntuple(i -> (q = X[i] * Y[i]; iszero(q) ? 0.0 : q), Val(B))
    ok = all(1:B) do i
        q = p[i]
        iszero(q) ||
            (isfinite(q) && abs(q) >= _FMA_EXACT_FLOOR && fma(X[i], Y[i], -q) == 0.0)
    end
    ok ? p : nothing
end

# The exact PRODUCT of finite nonzero Float64 lanes, or nothing. Mirrors
# `_dyadic_sum`, guarding `mul_dy`'s own precondition rather than throwing.
#
# float128use.md deferred this on the reasoning that "successive products
# consume the 113-bit significand quickly". THAT REASONING WAS WRONG, and
# instrumenting it (as the plan required) showed why: `Dyadic(v)` for a datum
# carries only that datum's SIGNIFICANT bits — at most P of them, not 53 — so
# sixteen P = 4 lanes reach 64 bits, comfortably inside `mul_dy`'s 96-bit
# precondition. Measured acceptance among blocks that actually reach here
# (all lanes finite and nonzero; the fold above peels the rest) is ~100% at
# B ≤ 16 for every scale/element pair tried, and still 99.6% at B = 32 with a
# P = 1 scale. The one configuration that falls off is a P = 3 scale times
# P = 4 elements at B = 32, at 24.1% — which the refusal below handles.
@inline _dyadic_prod(::Tuple{}) = DYADIC_ONE
function _dyadic_prod(X::NTuple{B,Float64}) where {B}
    acc = DYADIC_ONE
    @inbounds for i in 1:B
        d = Dyadic(X[i])                               # exact for a finite Float64
        nbits_dy(acc.S) + nbits_dy(d.S) <= 96 || return nothing
        acc = mul_dy(acc, d)
    end
    acc
end

function _dyadic_prod(X::NTuple{B,Dyadic}) where {B}
    acc = DYADIC_ONE
    @inbounds for i in 1:B
        d = X[i]
        nbits_dy(acc.S) + nbits_dy(d.S) <= 96 || return nothing
        acc = mul_dy(acc, d)
    end
    acc
end

function _reduce_add_value(X, prec::Int)
    any(isnan, X) && return _cnan(BigFloat)
    hasp = any(_isposinf, X); hasn = any(_isneginf, X)
    (hasp & hasn) && return _cnan(BigFloat)
    hasp && return _cinf(BigFloat)
    hasn && return _cninf(BigFloat)
    setprecision(BigFloat, prec) do
        acc = BigFloat(0)
        for v in X
            acc += _exactbig(v)                               # every partial exact by width
        end
        acc
    end
end

"""
    BlockReduceAdd(FR, ρ, b::Block; rng, R) -> BinaryValue

Draft §5.3.1: `project(reduce(ωAdd, [0, X…]))` over the block's decoded lanes —
the sum formed exactly, then projected once.
"""
function BlockReduceAdd(fr::Type{<:Binary}, ρ::Projection, b::Block{B,S,E};
                        rng::MaybeRNG = nothing, R::MaybeR = nothing) where {B,S,E}
    # exact Float64 lanes summed exactly in Dyadic: 10x the BigFloat path and
    # allocation-free. This deliberately does NOT go through `blockdecode` —
    # its return is a union, and merely crossing that boundary boxes the tuple.
    # `_dyadic_sum` declines when the lane spread leaves Dyadic's exact band.
    if _f64_block(S, E)
        lanes, ok = _f64_lanes(b)
        if ok
            d = _dyadic_sum(lanes)
            d === nothing || return _finish(fr, ρ, _drawR(ρ, rng, R), d)
        end
    else
        lanes = _dyadic_lanes(b)
        if lanes !== nothing
            d = _dyadic_sum(lanes)
            d === nothing || return _finish(fr, ρ, _drawR(ρ, rng, R), d)
        end
    end
    _finish(fr, ρ, _drawR(ρ, rng, R),
            _reduce_add_value(blockdecode(b),
                              _lane_sum_prec(BinaryFormatOf(S), BinaryFormatOf(E), B)))
end

"""
    BlockReduceMultiply(FR, ρ, b::Block; rng, R) -> BinaryValue

Draft §5.3.1: `project(reduce(ωMultiply, [1, X…]))` — the product formed
exactly, then projected once. `0 · ∞` anywhere in the fold is NaN.
"""
function BlockReduceMultiply(fr::Type{<:Binary}, ρ::Projection, b::Block{B,S,E};
                             rng::MaybeRNG = nothing, R::MaybeR = nothing) where {B,S,E}
    # `_f64_lanes` rather than `blockdecode`, for the reason BlockReduceAdd does
    # the same: crossing blockdecode's union return boxes the tuple. `ok` means
    # every lane is finite, so neither NaN nor ±∞ can be present and only the
    # zero row of the fold below can still apply.
    if _f64_block(S, E)
        lanes, ok = _f64_lanes(b)
        if ok
            any(iszero, lanes) && return _finish(fr, ρ, _drawR(ρ, rng, R), _czero(BigFloat))
            d = _dyadic_prod(lanes)
            d === nothing || return _finish(fr, ρ, _drawR(ρ, rng, R), d)
        end
    else
        lanes = _dyadic_lanes(b)
        if lanes !== nothing
            any(d -> iszero(d.S), lanes) &&
                return _finish(fr, ρ, _drawR(ρ, rng, R), DYADIC_ZERO)
            d = _dyadic_prod(lanes)
            d === nothing || return _finish(fr, ρ, _drawR(ρ, rng, R), d)
        end
    end
    X = blockdecode(b)
    res = if any(isnan, X) || (any(iszero, X) && any(isinf, X))
        _cnan(BigFloat)
    elseif any(isinf, X)
        isodd(count(signbit, X)) ? _cninf(BigFloat) : _cinf(BigFloat)
    elseif any(iszero, X)
        _czero(BigFloat)
    else
        setprecision(BigFloat, _lane_prod_prec(BinaryFormatOf(S), BinaryFormatOf(E), B)) do
            acc = BigFloat(1)
            for v in X
                acc *= _exactbig(v)
            end
            acc
        end
    end
    _finish(fr, ρ, _drawR(ρ, rng, R), res)
end

"""
    BlockDotProduct(FR, ρ, bx::Block{B}, by::Block{B}; rng, R) -> BinaryValue

Draft §5.3.2: the lane products and their sum formed exactly, the ∞/NaN fold
algebra resolved on the lane classifications first, then one projection.
"""
function BlockDotProduct(fr::Type{<:Binary}, ρ::Projection,
                         bx::Block{B,S1,E1}, by::Block{B,S2,E2};
                         rng::MaybeRNG = nothing, R::MaybeR = nothing) where {B,S1,E1,S2,E2}
    # the all-Float64 fast route, taken before `blockdecode` so the union its
    # return type carries is never crossed (crossing it boxes the tuple)
    if _f64_block(S1, E1) && _f64_block(S2, E2)
        lx, okx = _f64_lanes(bx)
        ly, oky = _f64_lanes(by)
        if okx & oky                       # both ok ⇒ every lane finite and exact
            p = _exact_lane_products(lx, ly)
            if p !== nothing
                d = _dyadic_sum(p)
                d === nothing || return _finish(fr, ρ, _drawR(ρ, rng, R), d)
            end
        end
    end
    X = blockdecode(bx); Y = blockdecode(by)
    # each term is a product of FOUR datums, so the span doubles relative to
    # the sum reduction; the sum of the two lane bounds covers it
    dotprec = _lane_sum_prec(BinaryFormatOf(S1), BinaryFormatOf(E1), B) +
              _lane_sum_prec(BinaryFormatOf(S2), BinaryFormatOf(E2), B)
    cls = ntuple(Val(B)) do i
        x, y = X[i], Y[i]
        (isnan(x) | isnan(y)) && return NaN
        ((iszero(x) && isinf(y)) || (isinf(x) && iszero(y))) && return NaN
        (isinf(x) || isinf(y)) && return ((signbit(x) ⊻ signbit(y)) ? -Inf : Inf)
        1.0                                                    # finite lane marker
    end
    res = if any(isnan, cls)
        _cnan(BigFloat)
    elseif any(isinf, cls)
        hasp = any(==(Inf), cls); hasn = any(==(-Inf), cls)
        (hasp & hasn) ? _cnan(BigFloat) : (hasp ? _cinf(BigFloat) : _cninf(BigFloat))
    else
        setprecision(BigFloat, dotprec) do
            acc = BigFloat(0)
            for i in 1:B
                acc += _exactbig(X[i]) * _exactbig(Y[i])       # exact products, exact sum
            end
            acc
        end
    end
    _finish(fr, ρ, _drawR(ρ, rng, R), res)
end

for f in (:BlockReduceAdd, :BlockReduceMultiply)
    @eval @inline $f(fr::Type{<:BinaryValue}, ρ::Projection, b::Block; kw...) =
        $f(BinaryFormatOf(fr), ρ, b; kw...)
end
for f in (:BlockReduceAdd, :BlockReduceMultiply)
    @eval @inline $f(fr::Binary, ρ::Projection, b::Block; kw...) =
        $f(typeof(fr), ρ, b; kw...)
end
@inline BlockDotProduct(fr::Type{<:BinaryValue}, ρ::Projection, bx::Block, by::Block; kw...) =
    BlockDotProduct(BinaryFormatOf(fr), ρ, bx, by; kw...)
@inline BlockDotProduct(fr::Binary, ρ::Projection, bx::Block, by::Block; kw...) =
    BlockDotProduct(typeof(fr), ρ, bx, by; kw...)

# ---- conversion family (draft §5.2) ------------------------------------------
"""
    ConvertFromBlock(FR, ρ, b::Block; rng) -> NTuple{B, BinaryValue}

Draft §5.2.1: decode the block and project each lane into `FR` — no scale
division; the scale is folded into the values.
"""
function ConvertFromBlock(fr::Type{<:Binary}, ρ::Projection, b::Block{B};
                          rng::MaybeRNG = nothing) where {B}
    X = blockdecode(b)
    rr = isstochastic(ρ) ? _resolve_rng(rng) : nothing
    ntuple(i -> project(fr, ρ, X[i]; R = _drawR(ρ, rr, nothing)), Val(B))
end

"""
    ConvertToBlock(FR, ρ, xs::NTuple{B, BinaryValue}, s::BinaryValue; rng) -> Block

Draft §5.2.2: the elements' values, block-projected against the supplied
scale `s` into element format `FR`.
"""
function ConvertToBlock(fr::Type{<:Binary}, ρ::Projection,
                        xs::NTuple{B, BinaryValue}, s::BinaryValue;
                        rng::MaybeRNG = nothing) where {B}
    blockproject(fr, ρ, s, map(decode, xs); rng)
end

"""
    ConvertToBlockMaxAbsFinite(FS, FR, ρs, ρ, xs::NTuple{B, BinaryValue}; rng) -> Block

Draft §5.2.3: the scale is `reduce(ωMaximumFinite, [NaN, |x₁| …])` projected
into `FS` under `ρs`; the elements are then block-projected against it into
`FR` under `ρ`. All-NaN input gives a NaN scale (and NaN elements); infinities
never set the scale but survive as ±Inf elements.
"""
function ConvertToBlockMaxAbsFinite(fs::Type{<:Binary}, fr::Type{<:Binary},
                                    ρs::Projection, ρ::Projection, xs::NTuple{B, BinaryValue};
                                    rng::MaybeRNG = nothing) where {B}
    X = map(decode, xs)
    # the fold runs on one carrier, seeded with THAT carrier's NaN: MaximumFinite's
    # whole contract is that a NaN seed loses to any finite operand.
    #
    # The carrier is the DECODED one, not BigFloat. `MaximumFinite` selects an
    # operand rather than combining significands, so the fold consumes no
    # precision and needs none added: lifting every lane through `_exactbig`
    # first cost 17.1 µs and 1067 allocations at B = 16 for a comparison chain
    # (float128use.md §6). A homogeneous decode folds in its own carrier; a
    # mixed Float64/Float128 tuple joins at Float128, which is exact; anything
    # else keeps the BigFloat fallback.
    M = map(x -> ωeval(Val(:Abs), x), X)
    S = _maxabs_fold(M)
    rr = isstochastic(ρs) || isstochastic(ρ) ? _resolve_rng(rng) : nothing
    s = project(fs, ρs, S; R = _drawR(ρs, rr, nothing))
    blockproject(fr, ρ, s, X; rng = rr)
end
for f in (:ConvertFromBlock,)
    @eval @inline $f(fr::Type{<:BinaryValue}, ρ::Projection, b::Block; kw...) =
        $f(BinaryFormatOf(fr), ρ, b; kw...)
end
@inline ConvertFromBlock(fr::Binary, ρ::Projection, b::Block; kw...) =
    ConvertFromBlock(typeof(fr), ρ, b; kw...)
@inline ConvertToBlock(fr::Type{<:BinaryValue}, ρ::Projection, xs::Tuple, s::BinaryValue; kw...) =
    ConvertToBlock(BinaryFormatOf(fr), ρ, xs, s; kw...)
@inline ConvertToBlock(fr::Binary, ρ::Projection, xs::Tuple, s::BinaryValue; kw...) =
    ConvertToBlock(typeof(fr), ρ, xs, s; kw...)
@inline ConvertToBlockMaxAbsFinite(fs::Type{<:BinaryValue}, fr::Type{<:BinaryValue},
                                   ρs::Projection, ρ::Projection, xs::Tuple; kw...) =
    ConvertToBlockMaxAbsFinite(BinaryFormatOf(fs), BinaryFormatOf(fr), ρs, ρ, xs; kw...)
@inline ConvertToBlockMaxAbsFinite(fs::BinarySpecifier, fr::BinarySpecifier,
                                   ρs::Projection, ρ::Projection, xs::Tuple; kw...) =
    ConvertToBlockMaxAbsFinite(_formattype(fs), _formattype(fr), ρs, ρ, xs; kw...)

# ---- SoA array-of-blocks container -----------------------------------------
"""
    BlockVector{B,S,E} <: AbstractVector{Block{B,S,E}}

Structure-of-arrays storage for blocks: `scales::Vector{S}` and
`elems::Matrix{E}` (`B × n`, column-major, so each block's elements are one
contiguous column). Build from a vector of blocks: `BlockVector(blocks)`.
"""
struct BlockVector{B, S<:BinaryValue, E<:BinaryValue} <: AbstractVector{Block{B,S,E}}
    scales::Vector{S}
    elems::Matrix{E}
    function BlockVector{B}(scales::Vector{S}, elems::Matrix{E}) where {B, S<:BinaryValue, E<:BinaryValue}
        B >= 1 || throw(ArgumentError("block size B must be ≥ 1"))
        size(elems, 1) == B || throw(DimensionMismatch("elems must be $(B)×n"))
        size(elems, 2) == length(scales) || throw(DimensionMismatch("one scale per block"))
        new{B,S,E}(scales, elems)
    end
end
BlockVector(blocks::AbstractVector{Block{B,S,E}}) where {B,S,E} =
    BlockVector{B}(S[b.s for b in blocks], E[blocks[j].x[i] for i in 1:B, j in eachindex(blocks)])
Base.size(bv::BlockVector) = (length(bv.scales),)
Base.IndexStyle(::Type{<:BlockVector}) = IndexLinear()
Base.@propagate_inbounds function Base.getindex(bv::BlockVector{B}, j::Int) where {B}
    @boundscheck checkbounds(bv, j)
    Block(bv.scales[j], ntuple(i -> @inbounds(bv.elems[i, j]), Val(B)))
end
Base.@propagate_inbounds function Base.setindex!(bv::BlockVector{B,S,E}, b::Block{B,S,E}, j::Int) where {B,S,E}
    @boundscheck checkbounds(bv, j)
    bv.scales[j] = b.s
    for i in 1:B
        bv.elems[i, j] = b.x[i]
    end
    bv
end
