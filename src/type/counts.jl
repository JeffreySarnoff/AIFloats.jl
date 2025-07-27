
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

n_values(T::Type{<:AbstractAIFloat}) = 2^n_bits(T)

n_nums(T::Type{<:AbstractAIFloat}) = n_values(T) - n_nans(T)
n_nonzero_nums(T::Type{<:AbstractAIFloat}) = n_nums(T) - n_zeros(T)
n_finite_nums(T::Type{<:AbstractAIFloat}) = n_nums(T) - n_inf(T)
n_nonzero_finite_nums(T::Type{<:AbstractAIFloat}) = n_finite_nums(T) - n_zeros(T)

#--->

nmags_sig(T::Type{<:AbstractAIFloat}) = 1 << n_sig_bits(T)
nmags_sig_nonzero(T::Type{<:AbstractAIFloat}) = nmags_sig(T) - 1

nmags_frac(T::Type{<:AbstractAIFloat}) = 1 << n_frac_bits(T)
nmags_frac_nonzero(T::Type{<:AbstractAIFloat}) = nmags_frac(T) - 1

n_values_exp(T::Type{<:AbstractAIFloat}) = 1 << n_exp_bits(T)
n_values_exp_nonzero(T::Type{<:AbstractAIFloat}) = n_values_exp(T) - 1

n_values_nonneg(T::Type{<:AbstractAIFloat}) = nmags(T)
n_values_positive(T::Type{<:AbstractAIFloat}) = n_values_nonneg(T) - 1
n_values_negative(T::Type{<:AbstractAIFloat}) = n_nums(T) - n_values_nonneg(T)

n_finite_nums_nonneg(T::Type{<:AbstractAIFloat}) = n_values_nonneg(T) - n_pos_inf(T)
n_finite_nums_positive(T::Type{<:AbstractAIFloat}) = n_values_positive(T) - n_pos_inf(T)
n_finite_nums_negative(T::Type{<:AbstractAIFloat}) = n_values_negative(T) - n_neg_inf(T)

nmags_prenormal(T::Type{<:AbstractAIFloat}) = 2^(n_sig_bits(T)-1) # 1 << (SigBits - 1)
nmags_subnormal(T::Type{<:AbstractAIFloat}) = nmags_prenormal(T) - 1

n_values_prenormal(::Type{T}) where {Bits, SigBits, T<:AbstractSigned{Bits, SigBits}} = 2 * nmags_prenormal(T) - 1
n_values_prenormal(::Type{T}) where {Bits, SigBits, T<:AbstractUnsigned{Bits, SigBits}} = nmags_prenormal(T)

n_values_subnormal(T::Type{<:AbstractAIFloat}) = n_values_prenormal(T) - 1

nmags_normal(T::Type{<:AbstractAIFloat}) = nmags_finite(T) - nmags_prenormal(T)
n_values_normal(T::Type{<:AbstractAIFloat}) = n_finite_nums(T) - n_values_prenormal(T)

nmags_normal_extended(T::Type{<:AbstractAIFloat}) =
    nmags_normal(T) + n_pos_inf(T)

n_values_normal_extended(T::Type{<:AbstractAIFloat}) =
    nmags_normal(T) + n_inf(T)

# support for instantiations
for F in (:nbits, :n_sig_bits, :n_frac_bits, :n_exp_bits, :n_sign_bits,
          :n_nans, :n_zeros, :n_inf, :n_pos_inf, :n_neg_inf,
          :n_values, :n_nums, :n_nonzero_nums,
          :nmags_sig, :nmags_sig_nonzero, :nmags_frac, :nmags_frac_nonzero,
          :nmags, :nmags_nonzero,
          :n_finite_nums, :n_nonzero_finite_nums, :nmags_finite, :nmags_finite_nonzero,
          :n_values_nonneg, :n_values_positive, :n_values_negative,
          :n_finite_nums_nonneg, :n_finite_nums_positive, :n_finite_nums_negative,
          :nmags_prenormal, :nmags_subnormal, :n_values_prenormal, :n_values_subnormal,
          :nmags_normal, :n_values_normal, :nmags_normal_extended, :n_values_normal_extended) 
    @eval $F(x::T) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = $F(T)
end
