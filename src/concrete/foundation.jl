
# support for foundation magnitude sequence generation

function foundation_magnitudes(T::Type{<:AbstractAIFloat})
    significands = collect(prenormal_magnitude_steps(T))
    nmagnitudes = nMagnitudes(T) - (is_signed(T) * nPrenormalMagnitudes(T))
    normal_cycles = fld(nmagnitudes, nPrenormalMagnitudes(T))
    normals = Iterators.flatten(fill(normal_magnitude_steps(T), normal_cycles))
    append!(significands, normals)

    exp_values = map(two_pow, exp_unbiased_magnitude_strides(T))
    if iszero(exp_values[1])  
        exp_values = map(x->Float128(2)^x, map(Float128,exp_unbiased_magnitude_strides(T)))
        if iszero(exp_values[1])
            exp_values = map(x->BigFloat(2)^x, map(BigFloat,exp_unbiased_magnitude_strides(T)))
        end
    end
    significands .*= exp_values

    typ = typeforfloat(nBits(T))
    magnitudes = memalign_clear(typ, length(significands))
    magnitudes[:] = map(typ, significands)
    magnitudes
end

@inline function prenormal_magnitude_steps(T::Type{<:AbstractAIFloat})
    return (0:nPrenormalMagnitudes(T)-1) ./ Float128(nPrenormalMagnitudes(T))
end

function normal_magnitude_steps(T::Type{<:AbstractAIFloat})
    nprenormals = nPrenormalMagnitudes(T)
    (nprenormals:(2*nprenormals-1)) ./ Float128(nprenormals)
end

function normal_exp_stride(T::Type{<:AbstractAIFloat})
    cld(nMagnitudes(T), nExpValues(T))
end

@inline function foundation_extremal_exps(T::Type{<:AbstractAIFloat})
    exp_max = fld(nNonzeroMagnitudes(T), nPrenormalMagnitudes(T))
    exp_min = -exp_max
    exp_min, exp_max
end

function foundation_exps(T::Type{<:AbstractAIFloat})
    exp_min, exp_max = foundation_extremal_exps(T)
    return exp_min:exp_max
end

@inline two_pow(x::Integer) = ldexp(1.0f0, x)

function pow2_foundation_exps(T,res::Vector{Float32})
    expres =  (foundation_exps(T))
    map(two_pow, expres)
end

function exp_unbiased_magnitude_strides(T::Type{<:AbstractAIFloat})
    append!(fill(expUnbiasedMin(T), normal_exp_stride(T)), collect(Iterators.flatten((fill.(expUnbiasedValues(T), normal_exp_stride(T)))[:,1])))
end

# cover instantiations for value sequence generation
for F in (:prenormal_magnitude_steps, :normal_magnitude_steps, :normal_exp_stride,
          :foundation_extremal_exps, :foundation_exps, :exp_unbiased_magnitude_strides, :pow2_foundation_exps,
          :foundation_magnitudes, :foundation_values, :value_sequence)
    @eval $F(x::T) where {Bits, SigBits, T<:AbstractAIFloat{Bits, SigBits}} = $F(T)
end
