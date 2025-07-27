
function significand_mags(T::Type{<:AbstractAIFloat})
    significands = collect(prenormal_mag_steps(T))
    n_mags = n_mags(T) - (is_signed(T) * n_prenormal_mags(T))
    normal_cycles = fld(n_mags, n_prenormal_mags(T))
    normals = Iterators.flatten(fill(normal_mag_steps(T), normal_cycles))
    append!(significands, normals)

    map(BigFloat, significands)
end

@inline function prenormal_mag_steps(T::Type{<:AbstractAIFloat})
    return (0:n_prenormal_mags(T)-1) ./ typeforfloat(T)(n_prenormal_mags(T))
end

function normal_mag_steps(T::Type{<:AbstractAIFloat})
    nprenormals = n_prenormal_mags(T)
    (nprenormals:(2*nprenormals-1)) ./ typeforfloat(T)(nprenormals)
end

significand_mags(x::T) where {T<:AbstractAIFloat} = significand_mags(T)
