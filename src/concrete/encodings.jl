@inline function encoding_sequence(T::Type{<:AbstractAIFloat})
    nbits = nbits(T)
    n = 1 << nbits
    typ = typeforcode(nbits)
    codes = memalign_clear(typ, n)
    codes[:] = map(typ, 0:(n-1))
    codes
end

function encoding_sequence(::Type{T}, bits::Int) where {T<:Integer}
    n = 1 << bits
    codes = memalign_clear(T, n)
    codes[:] = map(T, 0:(n-1))
    codes
end

# cover instantiations for value sequence generation
for F in (:encoding_sequence,)
    @eval $F(x::T) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = $F(T)
end
