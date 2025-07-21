
# counts predicated on abstract [sub]type

nNaNs(@nospecialize(T::Type{<:AbstractAIFloat})) = 1
nZeros(@nospecialize(T::Type{<:AbstractAIFloat})) = 1

nInfs(@nospecialize(T::Type{<:AkoSignedFinite}))     = 0
nInfs(@nospecialize(T::Type{<:AkoUnsignedFinite}))   = 0
nInfs(@nospecialize(T::Type{<:AkoSignedExtended}))   = 2
nInfs(@nospecialize(T::Type{<:AkoUnsignedExtended})) = 1

nPosInfs(@nospecialize(T::Type{<:AbstractAIFloat}))  = (nInfs(T) + 1) >> 1
nNegInfs(@nospecialize(T::Type{<:AbstractSigned}))   = (nInfs(T) + 1) >> 1
nNegInfs(@nospecialize(T::Type{<:AbstractUnsigned})) = 0

# counts predicated on type defining parameters and type specifying qualities
# parameters: (bits, sigbits, exponent bias)
# qualities: (signedness [signed / unsigned], finiteness [finite / extended (has Inf[s])])

nbits(T::Type{<:AbstractAIFloat{Bits, SigBits}}) where {Bits, SigBits} = Bits
nbits_sig(T::Type{<:AbstractAIFloat{Bits, SigBits}}) where {Bits, SigBits} = SigBits

nbits_frac(@nospecialize(T::Type{<:AbstractAIFloat})) = nbits_sig(T) - 1

nbits_sign(@nospecialize(T::Type{<:AbstractSigned})) = 1
nbits_sign(@nospecialize(T::Type{<:AbstractUnsigned})) = 0

nbits_exp(@nospecialize(T::Type{<:AbstractSigned})) = nbits(T) - nbits_sig(T)
nbits_exp(@nospecialize(T::Type{<:AbstractUnsigned})) = nbits(T) - nbits_sig(T) + 1

nmags(T::Type{<:AbstractUnsigned}) = 2^(nbits(T)) - 1
nmags(T::Type{<:AbstractSigned})   = 2^(nbits(T)  - 1)

nmags_finite(T::Type{<:AbstractAIFloat}) = nmags(T) - nInfs(T)
nmags_nonzero(T::Type{<:AbstractAIFloat}) = nmags(T) - nZeros(T)
nmags_finite_nonzero(T::Type{<:AbstractAIFloat}) = nmags_finite(T) - nZeros(T)

nvalues(T::Type{<:AbstractAIFloat}) = 2^nbits(T)

nvalues_numeric(T::Type{<:AbstractAIFloat}) = nvalues(T) - nNaNs(T)
nvalues_numeric_nonzero(T::Type{<:AbstractAIFloat}) = nvalues_numeric(T) - nZeros(T)
nvalues_finite(T::Type{<:AbstractAIFloat}) = nvalues_numeric(T) - nInfs(T)
nvalues_finite_nonzero(T::Type{<:AbstractAIFloat}) = nvalues_finite(T) - nZeros(T)

#--->

nmags_sig(T::Type{<:AbstractAIFloat}) = 1 << nbits_sig(T)
nmags_sig_nonzero(T::Type{<:AbstractAIFloat}) = nmags_sig(T) - 1

nmags_frac(T::Type{<:AbstractAIFloat}) = 1 << nbits_frac(T)
nmags_frac_nonzero(T::Type{<:AbstractAIFloat}) = nmags_frac(T) - 1

nvalues_exp(T::Type{<:AbstractAIFloat}) = 1 << nbits_exp(T)
nvalues_exp_nonzero(T::Type{<:AbstractAIFloat}) = nvalues_exp(T) - 1

nvalues_nonneg(T::Type{<:AbstractAIFloat}) = nmags(T)
nvalues_positive(T::Type{<:AbstractAIFloat}) = nvalues_nonneg(T) - 1
nvalues_negative(T::Type{<:AbstractAIFloat}) = nvalues_numeric(T) - nvalues_nonneg(T)

nvalues_finite_nonneg(T::Type{<:AbstractAIFloat}) = nvalues_nonneg(T) - nPosInfs(T)
nvalues_finite_positive(T::Type{<:AbstractAIFloat}) = nvalues_positive(T) - nPosInfs(T)
nvalues_finite_negative(T::Type{<:AbstractAIFloat}) = nvalues_negative(T) - nNegInfs(T)

nmags_prenormal(T::Type{<:AbstractAIFloat}) = 2^(nbits_sig(T)-1) # 1 << (SigBits - 1)
nmags_subnormal(T::Type{<:AbstractAIFloat}) = nmags_prenormal(T) - 1

nvalues_prenormal(::Type{T}) where {Bits, SigBits, T<:AbstractSigned{Bits, SigBits}} = 2 * nmags_prenormal(T) - 1
nvalues_prenormal(::Type{T}) where {Bits, SigBits, T<:AbstractUnsigned{Bits, SigBits}} = nmags_prenormal(T)

nvalues_subnormal(T::Type{<:AbstractAIFloat}) = nvalues_prenormal(T) - 1

nmags_normal(T::Type{<:AbstractAIFloat}) = nmags_finite(T) - nmags_prenormal(T)
nvalues_normal(T::Type{<:AbstractAIFloat}) = nvalues_finite(T) - nvalues_prenormal(T)

nmags_normal_extended(T::Type{<:AbstractAIFloat}) =
    nmags_normal(T) + nPosInfs(T)

nvalues_normal_extended(T::Type{<:AbstractAIFloat}) =
    nmags_normal(T) + nInfs(T)

# support for instantiations
for F in (:nbits, :nbits_sig, :nbits_frac, :nbits_exp, :nbits_sign,
          :nNaNs, :nZeros, :nInfs, :nPosInfs, :nNegInfs,
          :nvalues, :nvalues_numeric, :nvalues_numeric_nonzero,
          :nmags_sig, :nmags_sig_nonzero, :nmags_frac, :nmags_frac_nonzero,
          :nmags, :nmags_nonzero,
          :nvalues_finite, :nvalues_finite_nonzero, :nmags_finite, :nmags_finite_nonzero,
          :nvalues_nonneg, :nvalues_positive, :nvalues_negative,
          :nvalues_finite_nonneg, :nvalues_finite_positive, :nvalues_finite_negative,
          :nmags_prenormal, :nmags_subnormal, :nvalues_prenormal, :nvalues_subnormal,
          :nmags_normal, :nvalues_normal, :nmags_normal_extended, :nvalues_normal_extended) 
    @eval $F(x::T) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = $F(T)
end
