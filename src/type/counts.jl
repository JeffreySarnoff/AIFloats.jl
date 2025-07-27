
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

n_mags(T::Type{<:AbstractUnsigned}) = 2^(n_bits(T)) - 1
n_mags(T::Type{<:AbstractSigned})   = 2^(n_bits(T)  - 1)

n_finite_mags(T::Type{<:AbstractAIFloat}) = n_mags(T) - n_inf(T)
n_nonzero_mags(T::Type{<:AbstractAIFloat}) = n_mags(T) - n_zeros(T)
n_nonzero_finite_mags(T::Type{<:AbstractAIFloat}) = n_finite_mags(T) - n_zeros(T)

n_values(T::Type{<:AbstractAIFloat}) = 2^n_bits(T)

n_nums(T::Type{<:AbstractAIFloat}) = n_values(T) - n_nans(T)
n_nonzero_nums(T::Type{<:AbstractAIFloat}) = n_nums(T) - n_zeros(T)
n_finite_nums(T::Type{<:AbstractAIFloat}) = n_nums(T) - n_inf(T)
n_nonzero_finite_nums(T::Type{<:AbstractAIFloat}) = n_finite_nums(T) - n_zeros(T)

#--->

n_sig_mags(T::Type{<:AbstractAIFloat}) = 1 << n_sig_bits(T)
n_nonzero_sig_mags(T::Type{<:AbstractAIFloat}) = n_sig_mags(T) - 1

n_frac_mags(T::Type{<:AbstractAIFloat}) = 1 << n_frac_bits(T)
n_nonzero_frac_mags(T::Type{<:AbstractAIFloat}) = n_frac_mags(T) - 1

n_exp_nums(T::Type{<:AbstractAIFloat}) = 1 << n_exp_bits(T)
n_nonzero_exp_nums(T::Type{<:AbstractAIFloat}) = n_exp_nums(T) - 1

n_poz_nums(T::Type{<:AbstractAIFloat}) = n_mags(T)
n_pos_nums(T::Type{<:AbstractAIFloat}) = n_poz_nums(T) - 1
n_neg_nums(T::Type{<:AbstractAIFloat}) = n_nums(T) - n_poz_nums(T)

n_finite_nums_nonneg(T::Type{<:AbstractAIFloat}) = n_poz_nums(T) - n_pos_inf(T)
n_finite_nums_positive(T::Type{<:AbstractAIFloat}) = n_pos_nums(T) - n_pos_inf(T)
n_finite_nums_negative(T::Type{<:AbstractAIFloat}) = n_neg_nums(T) - n_neg_inf(T)

n_prenormal_mags(T::Type{<:AbstractAIFloat}) = 2^(n_sig_bits(T)-1) # 1 << (SigBits - 1)
n_subnormal_mags(T::Type{<:AbstractAIFloat}) = n_prenormal_mags(T) - 1

n_prenormal_nums(::Type{T}) where {Bits, SigBits, T<:AbstractSigned{Bits, SigBits}} = 2 * n_prenormal_mags(T) - 1
n_prenormal_nums(::Type{T}) where {Bits, SigBits, T<:AbstractUnsigned{Bits, SigBits}} = n_prenormal_mags(T)

n_subnormal_nums(T::Type{<:AbstractAIFloat}) = n_prenormal_nums(T) - 1

n_normal_mags(T::Type{<:AbstractAIFloat}) = n_finite_mags(T) - n_prenormal_mags(T)
n_normal_nums(T::Type{<:AbstractAIFloat}) = n_finite_nums(T) - n_prenormal_nums(T)

n_extended_normal_mags(T::Type{<:AbstractAIFloat}) =
    n_normal_mags(T) + n_pos_inf(T)

n_extended_normal_nums(T::Type{<:AbstractAIFloat}) =
    n_normal_mags(T) + n_inf(T)

# support for instantiations
for F in (:nbits, :n_sig_bits, :n_frac_bits, :n_exp_bits, :n_sign_bits,
          :n_nans, :n_zeros, :n_inf, :n_pos_inf, :n_neg_inf,
          :n_values, :n_nums, :n_nonzero_nums,
          :n_sig_mags, :n_nonzero_sig_mags, :n_frac_mags, :n_nonzero_frac_mags,
          :nmags, :n_nonzero_mags,
          :n_finite_nums, :n_nonzero_finite_nums, :n_finite_mags, :n_nonzero_finite_mags,
          :n_poz_nums, :n_pos_nums, :n_neg_nums,
          :n_finite_nums_nonneg, :n_finite_nums_positive, :n_finite_nums_negative,
          :n_prenormal_mags, :n_subnormal_mags, :n_prenormal_nums, :n_subnormal_nums,
          :n_normal_mags, :n_normal_nums, :n_extended_normal_mags, :n_extended_normal_nums) 
    @eval $F(x::T) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = $F(T)
end
