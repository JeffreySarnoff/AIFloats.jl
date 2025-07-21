
function significand_mags(T::Type{<:AbstractAIFloat})
    significands = collect(prenormal_mag_steps(T))
    n_mags = nmags(T) - (is_signed(T) * nmags_prenormal(T))
    normal_cycles = fld(n_mags, nmags_prenormal(T))
    normals = Iterators.flatten(fill(normal_mag_steps(T), normal_cycles))
    append!(significands, normals)

    map(ArbReal, significands)
end

@inline function prenormal_mag_steps(T::Type{<:AbstractAIFloat})
    return (0:nmags_prenormal(T)-1) ./ typeforfloat(T)(nmags_prenormal(T))
end

function normal_mag_steps(T::Type{<:AbstractAIFloat})
    nprenormals = nmags_prenormal(T)
    (nprenormals:(2*nprenormals-1)) ./ typeforfloat(T)(nprenormals)
end

significand_mags(x::T) where {T<:AbstractAIFloat} = significand_mags(T)
