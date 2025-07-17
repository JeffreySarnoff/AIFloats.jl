
function significand_magnitudes(T::Type{<:AbstractAIFloat})
    significands = collect(prenormal_magnitude_steps(T))
    n_magnitudes = nmagnitudes(T) - (is_signed(T) * nmagnitudes_prenormal(T))
    normal_cycles = fld(n_magnitudes, nmagnitudes_prenormal(T))
    normals = Iterators.flatten(fill(normal_magnitude_steps(T), normal_cycles))
    append!(significands, normals)

    map(ArbReal, significands)
end

@inline function prenormal_magnitude_steps(T::Type{<:AbstractAIFloat})
    return (0:nmagnitudes_prenormal(T)-1) ./ typeforfloat(T)(nmagnitudes_prenormal(T))
end

function normal_magnitude_steps(T::Type{<:AbstractAIFloat})
    nprenormals = nmagnitudes_prenormal(T)
    (nprenormals:(2*nprenormals-1)) ./ typeforfloat(T)(nprenormals)
end

significand_magnitudes(x::T) where {T<:AbstractAIFloat} = significand_magnitudes(T)
