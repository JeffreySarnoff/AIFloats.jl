
# counts predicated on abstract [sub]type

n_nans(@nospecialize(T::Type{<:AbstractAIFloat})) = 1
n_zeros(@nospecialize(T::Type{<:AbstractAIFloat})) = 1

n_infs(@nospecialize(T::Type{<:AkoSignedFinite}))     = 0
n_infs(@nospecialize(T::Type{<:AkoUnsignedFinite}))   = 0
n_infs(@nospecialize(T::Type{<:AkoSignedExtended}))   = 2
n_infs(@nospecialize(T::Type{<:AkoUnsignedExtended})) = 1

n_pos_infs(@nospecialize(T::Type{<:AbstractAIFloat}))  = (n_infs(T) + 1) >> 1
n_neg_infs(@nospecialize(T::Type{<:AbstractSigned}))   = (n_infs(T) + 1) >> 1
n_neg_infs(@nospecialize(T::Type{<:AbstractUnsigned})) = 0

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

# a "mag" is a magnitude, a nonnegative value (aka a poz [positive or zero] value)
n_mags(T::Type{<:AbstractUnsigned}) = 2^(n_bits(T)) - 1
n_mags(T::Type{<:AbstractSigned})   = 2^(n_bits(T)  - 1)

n_finite_mags(T::Type{<:AbstractAIFloat}) = n_mags(T) - n_infs(T)
n_nonzero_mags(T::Typ0e{<:AbstractAIFloat}) = n_mags(T) - n_zeros(T)
n_finite_nonzero_mags(T::Type{<:AbstractAIFloat}) = n_finite_mags(T) - n_zeros(T)

# a value is either numeric or non-numeric (NaN)
n_vals(T::Type{<:AbstractAIFloat}) = 2^n_bits(T)

# a "num" is a numeric value
n_nums(T::Type{<:AbstractAIFloat}) = n_vals(T) - n_nans(T)
n_nonzero_nums(T::Type{<:AbstractAIFloat}) = n_nums(T) - n_zeros(T)
n_finite_nums(T::Type{<:AbstractAIFloat}) = n_nums(T) - n_infs(T)
n_finite_nonzero_nums(T::Type{<:AbstractAIFloat}) = n_finite_nums(T) - n_zeros(T)

n_sig_mags(T::Type{<:AbstractAIFloat}) = 1 << n_sig_bits(T)

n_frac_mags(T::Type{<:AbstractAIFloat}) = 1 << n_frac_bits(T)
n_frac_mags_nonzero(T::Type{<:AbstractAIFloat}) = n_frac_mags(T) - 1

n_exp_nums(T::Type{<:AbstractAIFloat}) = 1 << n_exp_bits(T)
n_nonzero_exp_nums(T::Type{<:AbstractAIFloat}) = n_exp_nums(T) - 1

n_poz_vals(T::Type{<:AbstractAIFloat}) = n_mags(T)
n_pos_vals(T::Type{<:AbstractAIFloat}) = n_poz_vals(T) - 1
n_neg_vals(T::Type{<:AbstractAIFloat}) = n_nums(T) - n_poz_vals(T)

n_poz_finite_vals(T::Type{<:AbstractAIFloat}) = n_poz_vals(T) - n_pos_infs(T)
n_pos_finite_vals(T::Type{<:AbstractAIFloat}) = n_pos_vals(T) - n_pos_infs(T)
n_neg_finite_vals(T::Type{<:AbstractAIFloat}) = n_neg_vals(T) - n_neg_infs(T)

n_prenormal_mags(T::Type{<:AbstractAIFloat}) = 2^(n_sig_bits(T)-1) # 1 << (SigBits - 1)
n_subnormal_mags(T::Type{<:AbstractAIFloat}) = n_prenormal_mags(T) - 1

n_prenormal_vals(::Type{T}) where {Bits, SigBits, T<:AbstractSigned{Bits, SigBits}} = 2 * n_prenormal_mags(T) - 1
n_prenormal_vals(::Type{T}) where {Bits, SigBits, T<:AbstractUnsigned{Bits, SigBits}} = n_prenormal_mags(T)

n_subnormal_vals(T::Type{<:AbstractAIFloat}) = n_prenormal_vals(T) - 1

n_normal_mags(T::Type{<:AbstractAIFloat}) = n_finite_mags(T) - n_prenormal_mags(T)
n_normal_vals(T::Type{<:AbstractAIFloat}) = n_finite_nums(T) - n_prenormal_vals(T)

n_extended_normal_mags(T::Type{<:AbstractAIFloat}) =
    n_normal_mags(T) + n_pos_infs(T)

n_extended_normal_vals(T::Type{<:AbstractAIFloat}) =
    n_normal_mags(T) + n_infs(T)

# support for instantiations
for F in (:n_bits, :n_sig_bits, :n_frac_bits, :n_exp_bits, :n_sign_bits,
          :n_nans, :n_zeros, :n_infs, :n_pos_infs, :n_neg_infs,
          :n_vals, :n_nums, :n_nonzero_nums,
          :n_sig_mags, :n_sig_mags_nonzero, :n_frac_mags, :n_frac_mags_nonzero,
          :n_mags, :n_nonzero_mags,
          :n_finite_nums, :n_finite_nonzero_nums, :n_finite_mags, :n_finite_nonzero_mags,
          :n_poz_vals, :n_pos_vals, :n_neg_vals,
          :n_poz_finite_vals, :n_pos_finite_vals, :n_neg_finite_vals,
          :n_prenormal_mags, :n_subnormal_mags, :n_prenormal_vals, :n_subnormal_vals,
          :n_normal_mags, :n_normal_vals, :n_extended_normal_mags, :n_extended_normal_vals) 
    @eval $F(x::T) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = $F(T)
end
