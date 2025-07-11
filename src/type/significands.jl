
function magnitude_significand_seq(T::Type{<:AbstractAIFloat})
    significands = collect(magnitude_prenormal_steps(T))
    n_magnitudes = nmagnitudes(T) - (is_signed(T) * nmagnitudes_prenormal(T))
    normal_cycles = fld(n_magnitudes, nmagnitudes_prenormal(T))
    normals = Iterators.flatten(fill(magnitude_normal_steps(T), normal_cycles))
    append!(significands, normals)

    significands
end

@inline function magnitude_prenormal_steps(T::Type{<:AbstractAIFloat})
    return (0:nmagnitudes_prenormal(T)-1) ./ typeforfloat(T)(nmagnitudes_prenormal(T))
end

function magnitude_normal_steps(T::Type{<:AbstractAIFloat})
    nprenormals = nmagnitudes_prenormal(T)
    (nprenormals:(2*nprenormals-1)) ./ typeforfloat(T)(nprenormals)
end

magnitude_significand_seq(x::T) where {T<:AbstractAIFloat} = magnitude_significand_seq(T)
