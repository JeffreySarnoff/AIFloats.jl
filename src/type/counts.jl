
# counts predicated on abstract [sub]type

n_nans(@nospecialize(T::Type{<:AbstractAIFloat})) = 1
n_zeros(@nospecialize(T::Type{<:AbstractAIFloat})) = 1

n_inf(@nospecialize(T::Type{<:AkoSignedFinite}))     = 0
n_inf(@nospecialize(T::Type{<:AkoUnsignedFinite}))   = 0
n_inf(@nospecialize(T::Type{<:AkoSignedExtended}))   = 2
n_inf(@nospecialize(T::Type{<:AkoUnsignedExtended})) = 1

n_pos_inf(@nospecialize(T::Type{<:AbstractAIFloat}))  = (n_inf(T) + 1) >> 1
n_neg_inf(@nospecialize(T::Type{<:AbstractSigned}))   = (n_inf(T) + 1) >> 1
n_neg_inf(@nospecialize(T::Type{<:AbstractUnsigned})) = 0

# counts predicated on type defining parameters and type specifying qualities
# parameters: (bits, sigbits, exponent bias)
# qualities: (signedness [signed / unsigned], finiteness [finite / extended (has Inf[s])])

n_bits(T::Type{<:AbstractAIFloat{Bits, SigBits}}) where {Bits, SigBits} = Bits
n_sig_bits(T::Type{<:AbstractAIFloat{Bits, SigBits}}) where {Bits, SigBits} = SigBits

n_frac_bits(@nospecialize(T::Type{<:AbstractAIFloat})) = n_sig_bits(T) - 1

n_sign_bits(@nospecialize(T::Type{<:AbstractSigned})) = 1
n_sign_bits(@nospecialize(T::Type{<:AbstractUnsigned})) = 0

n_exp_bits(@nospecialize(T::Type{<:AbstractSigned})) = n_bits(T) - n_sig_bits(T)
n_exp_bits(@nospecialize(T::Type{<:AbstractUnsigned})) = n_bits(T) - n_sig_bits(T) + 1

nmags(T::Type{<:AbstractUnsigned}) = 2^(n_bits(T)) - 1
nmags(T::Type{<:AbstractSigned})   = 2^(n_bits(T)  - 1)

nmags_finite(T::Type{<:AbstractAIFloat}) = nmags(T) - n_inf(T)
nmags_nonzero(T::Type{<:AbstractAIFloat}) = nmags(T) - n_zeros(T)
nmags_finite_nonzero(T::Type{<:AbstractAIFloat}) = nmags_finite(T) - n_zeros(T)

nvalues(T::Type{<:AbstractAIFloat}) = 2^n_bits(T)

nvalues_numeric(T::Type{<:AbstractAIFloat}) = nvalues(T) - n_nans(T)
nvalues_numeric_nonzero(T::Type{<:AbstractAIFloat}) = nvalues_numeric(T) - n_zeros(T)
nvalues_finite(T::Type{<:AbstractAIFloat}) = nvalues_numeric(T) - n_inf(T)
nvalues_finite_nonzero(T::Type{<:AbstractAIFloat}) = nvalues_finite(T) - n_zeros(T)

#--->

nmags_sig(T::Type{<:AbstractAIFloat}) = 1 << n_sig_bits(T)
nmags_sig_nonzero(T::Type{<:AbstractAIFloat}) = nmags_sig(T) - 1

nmags_frac(T::Type{<:AbstractAIFloat}) = 1 << n_frac_bits(T)
nmags_frac_nonzero(T::Type{<:AbstractAIFloat}) = nmags_frac(T) - 1

nvalues_exp(T::Type{<:AbstractAIFloat}) = 1 << n_exp_bits(T)
nvalues_exp_nonzero(T::Type{<:AbstractAIFloat}) = nvalues_exp(T) - 1

nvalues_nonneg(T::Type{<:AbstractAIFloat}) = nmags(T)
nvalues_positive(T::Type{<:AbstractAIFloat}) = nvalues_nonneg(T) - 1
nvalues_negative(T::Type{<:AbstractAIFloat}) = nvalues_numeric(T) - nvalues_nonneg(T)

nvalues_finite_nonneg(T::Type{<:AbstractAIFloat}) = nvalues_nonneg(T) - n_pos_inf(T)
nvalues_finite_positive(T::Type{<:AbstractAIFloat}) = nvalues_positive(T) - n_pos_inf(T)
nvalues_finite_negative(T::Type{<:AbstractAIFloat}) = nvalues_negative(T) - n_neg_inf(T)

nmags_prenormal(T::Type{<:AbstractAIFloat}) = 2^(n_sig_bits(T)-1) # 1 << (SigBits - 1)
nmags_subnormal(T::Type{<:AbstractAIFloat}) = nmags_prenormal(T) - 1

nvalues_prenormal(::Type{T}) where {Bits, SigBits, T<:AbstractSigned{Bits, SigBits}} = 2 * nmags_prenormal(T) - 1
nvalues_prenormal(::Type{T}) where {Bits, SigBits, T<:AbstractUnsigned{Bits, SigBits}} = nmags_prenormal(T)

nvalues_subnormal(T::Type{<:AbstractAIFloat}) = nvalues_prenormal(T) - 1

nmags_normal(T::Type{<:AbstractAIFloat}) = nmags_finite(T) - nmags_prenormal(T)
nvalues_normal(T::Type{<:AbstractAIFloat}) = nvalues_finite(T) - nvalues_prenormal(T)

nmags_normal_extended(T::Type{<:AbstractAIFloat}) =
    nmags_normal(T) + n_pos_inf(T)

nvalues_normal_extended(T::Type{<:AbstractAIFloat}) =
    nmags_normal(T) + n_inf(T)

# support for instantiations
for F in (:nbits, :n_sig_bits, :n_frac_bits, :n_exp_bits, :n_sign_bits,
          :n_nans, :n_zeros, :n_inf, :n_pos_inf, :n_neg_inf,
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
