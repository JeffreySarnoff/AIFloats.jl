
# support for foundation magnitude sequence generation

function magnitude_foundation_seq(::Type{T}) where {T<:AbstractAIFloat}
    _significands = magnitude_significand_seq(T)
    exp_strides = magnitude_exp_unbiased_strides(T)
    
    workingtype = typeforkp(nbits(T), nbits_sig(T))
    twotyped = two(workingtype)

    twopow = x->twotyped^x
    
    significands = map(workingtype, _significands)
    exp_values = map(twopow, exp_strides)

    significands .*= exp_values

    if workingtype != BigFloat
        magnitudes = memalign_clear(workingtype, length(significands))
    else 
        magnitudes = Vector{workingtype}(undef, length(significands))   
    end
    magnitudes[:] .= significands
end

function exp_stride_normal(T::Type{<:AbstractAIFloat})
    cld(nmagnitudes(T), nvalues_exp(T))
end

@inline function exp_foundation_extremal(T::Type{<:AbstractAIFloat})
    exp_max = fld(nmagnitudes_nonzero(T), nmagnitudes_prenormal(T))
    exp_min = -exp_max
    exp_min, exp_max
end

function exp_foundation(T::Type{<:AbstractAIFloat})
    exp
    exp_min, exp_max = exp_foundation_extremal(T)
    return exp_min:exp_max
end

@inline two_pow(x::Integer) = ldexp(1.0, x)

@inline function two_pow(x::F) where {F<:AbstractFloat}
    F(2)^x
end

function exp_foundation_pow2(T,res::Vector{Float32})
    expres =  exp_foundation(T)
    map(two_pow, expres)
end

function magnitude_exp_unbiased_strides(T::Type{<:AbstractAIFloat})
    append!(fill(exp_unbiased_subnormal(T), exp_stride_normal(T)), collect(Iterators.flatten((fill.(exp_unbiased_normal_seq(T), exp_stride_normal(T)))[:,1])))
end

# cover instantiations for value sequence generation
for F in (:magnitude_steps_prenormal, :magnitude_steps_normal, :exp_stride_normal,
          :exp_foundation_extremal, :exp_foundation, :magnitude_exp_unbiased_strides, :exp_foundation_pow2,
          :magnitude_foundation_seq, :foundation_values, :value_seq)
    @eval $F(x::T) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = $F(T)
end
