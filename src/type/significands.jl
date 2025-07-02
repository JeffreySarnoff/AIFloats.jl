function significand_magnitudes(T::Type{<:AbstractAIFloat})
    significands = collect(prenormal_magnitude_steps(T))
    nmagnitudes = nMagnitudes(T) - (is_signed(T) * nPrenormalMagnitudes(T))
    normal_cycles = fld(nmagnitudes, nPrenormalMagnitudes(T))
    normals = Iterators.flatten(fill(normal_magnitude_steps(T), normal_cycles))
    append!(significands, normals)
    significands
end
    
@inline function prenormal_magnitude_steps(T::Type{<:AbstractAIFloat})
    return (0:nPrenormalMagnitudes(T)-1) ./ typeforfloat(T)(nPrenormalMagnitudes(T))
end

function normal_magnitude_steps(T::Type{<:AbstractAIFloat})
    nprenormals = nPrenormalMagnitudes(T)
    (nprenormals:(2*nprenormals-1)) ./ typeforfloat(T)(nprenormals)
end

signficand_magnitudes(x::T) where {T<:AbstractAIFloat} = significand_magnitudes(T)
