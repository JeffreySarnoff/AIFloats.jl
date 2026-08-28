# ωDecode: code point → the value it denotes, on the format's datumcarrier
#
# Ground truth is _decode_compute; the K ≤ 8 formats additionally get a
# constant-tuple decode table (their datumcarrier is always Float64, and 2^K
# tuple entries fold at compile time). The special code points are imported
# from content/codepoints.jl, not re-derived: one definition of the layout.

# decode policy — dispatch, not a branch
struct TableDecode end
struct ComputeDecode end

"""
    decodepolicy(F)

`TableDecode()` for `UInt8`-coded formats (a `2^K` constant tuple), otherwise
`ComputeDecode()` — a 65,536-entry tuple literal is not a table, it is a
compile-time hazard. Not exported.
"""
decodepolicy(::Type{F}) where {F<:Binary} = _decodepolicy(CodeType(F))
_decodepolicy(::Type{UInt8}) = TableDecode()
_decodepolicy(::Type{UInt16}) = ComputeDecode()

# the ground-truth field split
@inline function _decode_compute(::Type{F}, c::Unsigned) where {F<:Binary}
    C = datumcarrier(F)
    # NaN FIRST: for unsigned formats the NaN code aliases the −Inf slot
    c == nan_code(F) && return _cnan(C)
    if is_extended(F)
        c == posinf_code(F) && return _cinf(C)
        is_signed(F) && c == neginf_code(F) && return _cninf(C)
    end
    P = Int(PrecisionOf(F))
    B = ExponentBiasOf(F)
    hidden = 1 << (P - 1)                     # implicit-bit weight
    tmask  = _cu(F, hidden - 1)
    neg    = is_signed(F) && (c >= signmask(F))
    m      = neg ? c - signmask(F) : c
    tsig   = m & tmask
    Eb     = Int(m >> (P - 1))                # biased exponent field
    sig    = Eb == 0 ? Int(tsig) : Int(tsig) + hidden
    e      = (Eb == 0 ? 1 : Eb) - B + (1 - P)
    # the single zero: the sign is dropped here — the datum set has no −0
    sig == 0 && return _czero(C)
    _finite_datum(CodeType(F), C, sig, e, neg)
end

# dispatched on the representation seam: bit assembly's licence is the small
# exponent range of the UInt8-coded (rung-1) formats; the generic row is ldexp,
# which is exact on every carrier.
@inline function _finite_datum(::Type{UInt8}, ::Type{Float64}, sig::Int, e::Int, neg::Bool)
    nb   = 64 - leading_zeros(UInt64(sig))
    mant = (UInt64(sig) << (53 - nb)) & ((UInt64(1) << 52) - 1)
    bits = (UInt64(e + nb - 1 + 1023) << 52) | mant
    neg && (bits |= UInt64(1) << 63)
    reinterpret(Float64, bits)
end
@inline function _finite_datum(::Type{UInt16}, ::Type{C}, sig::Int, e::Int, neg::Bool) where {C}
    d = ldexp(C(sig), e)
    neg ? -d : d
end

# the K ≤ 8 constant-tuple decode table
@generated function _decode_table(::Type{F}) where {F<:Binary}
    CodeType(F) === UInt8 || return :(throw(ArgumentError(
        "decode tables exist only for UInt8-coded formats; $(string(F)) computes")))
    vals = ntuple(i -> _decode_compute(F, UInt8(i - 1)), 1 << Int(BitwidthOf(F)))
    :($vals)
end

_decode(::TableDecode, x::BinaryValue) =
    @inbounds _decode_table(BinaryFormatOf(x))[Int(codepoint(x)) + 1]
_decode(::ComputeDecode, x::BinaryValue) =
    _decode_compute(BinaryFormatOf(x), codepoint(x))

"""
    decode(x::BinaryValue)

The value the datum denotes, on the format's datum carrier — `Float64` for
`UInt8`-coded formats, `Float64`/`Float128` (or the exact carrier at the widest
biases) above.

Exact by construction: every datum of every format is representable on its
carrier.

# Examples

```jldoctest
julia> decode(MaxFiniteOf(Binary(8, 4, SIGNED, FINITE)))
240.0

julia> decode(MinPositiveOf(Binary(8, 4, UNSIGNED, FINITE)))
3.814697265625e-6
```
"""
decode(x::BinaryValue) = _decode(decodepolicy(BinaryFormatOf(x)), x)

# integer-space canonical form of a code point: (kind, sign, S, Q) with
# kind ∈ (:finite, :nan, :posinf, :neginf) and value = sign · S · 2^Q for
# finite. The same field split as _decode_compute, kept in Int — this is what
# the encode round-trip and, later, the saturation range test consume.
function _canonical(::Type{F}, c::Unsigned) where {F<:Binary}
    c == nan_code(F) && return (:nan, 1, Int64(0), Int64(0))
    if is_extended(F)
        c == posinf_code(F) && return (:posinf, 1, Int64(0), Int64(0))
        is_signed(F) && c == neginf_code(F) && return (:neginf, -1, Int64(0), Int64(0))
    end
    P = Int(PrecisionOf(F))
    B = ExponentBiasOf(F)
    hidden = 1 << (P - 1)
    neg    = is_signed(F) && (c >= signmask(F))
    m      = neg ? c - signmask(F) : c
    tsig   = Int(m & _cu(F, hidden - 1))
    Eb     = Int(m >> (P - 1))
    S      = Int64(Eb == 0 ? tsig : tsig + hidden)
    Q      = Int64((Eb == 0 ? 1 : Eb) - B + (1 - P))
    S == 0 && return (:finite, 1, Int64(0), Int64(0))
    (:finite, neg ? -1 : 1, S, Q)
end