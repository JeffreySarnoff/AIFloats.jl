
# support for foundation mag sequence generation

#=
function mag_foundation_seq(::Type{T}) where {T<:AbstractAIFloat}
    significands = significand_mags(T)

    exp_values = map(two_pow, exp_unbiased_mag_strides(T))
    if iszero(exp_values[1])  
        exp_values = map(x->Float128(2)^x, map(Float128,exp_unbiased_mag_strides(T)))
        if iszero(exp_values[1])
            exp_values = map(x->BigFloat(2)^x, map(BigFloat,exp_unbiased_mag_strides(T)))
        end
    end
    significands .*= exp_values

    typ = typeforfloat(n_bits(T))
    mags = memalign_clear(typ, length(significands))
    mags[:] = map(typ, significands)
    mags
end
=#
function mag_foundation_seq(::Type{T}) where {T<:AbstractAIFloat}
    significands = significand_mags(T)

    exp_values = map(two_pow, exp_unbiased_mag_strides(T))
    if iszero(exp_values[1])  
        exp_values = map(x->Float128(2)^x, map(Float128,exp_unbiased_mag_strides(T)))
        if iszero(exp_values[1])
            exp_values = map(x->BigFloat(2)^x, map(BigFloat,exp_unbiased_mag_strides(T)))
        end
    end
    significands .*= exp_values

    typ = BigFloat
    mags = zeros(typ, length(significands))
    mags[:] = map(typ, significands)
    mags
end


function normal_exp_stride(T::Type{<:AbstractAIFloat})
    cld(nmags(T), nvalues_exp(T))
end

@inline function foundation_extremal_exps(T::Type{<:AbstractAIFloat})
    exp_max = fld(nmags_nonzero(T), nmags_prenormal(T))
    exp_min = -exp_max
    exp_min, exp_max
end

function foundation_exps(T::Type{<:AbstractAIFloat})
    exp
    exp_min, exp_max = foundation_extremal_exps(T)
    return exp_min:exp_max
end

@inline two_pow(x::Integer) = ldexp(1.0, x)

@inline function two_pow(x::F) where {F<:AbstractFloat}
    F(2)^x
end

function pow2_foundation_exps(T,res::Vector{Float32})
    expres =  foundation_exps(T)
    map(two_pow, expres)
end

function exp_unbiased_mag_strides(T::Type{<:AbstractAIFloat})
    append!(fill(exp_unbiased_subnormal(T), normal_exp_stride(T)), collect(Iterators.flatten((fill.(exp_unbiased_normal_seq(T), normal_exp_stride(T)))[:,1])))
end

# cover instantiations for value sequence generation
for F in (:prenormal_mag_steps, :normal_mag_steps, :normal_exp_stride,
          :foundation_extremal_exps, :foundation_exps, :exp_unbiased_mag_strides, :pow2_foundation_exps,
          :mag_foundation_seq, :foundation_values, :value_seq)
    @eval $F(x::T) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = $F(T)
end
