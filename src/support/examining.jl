using Quadmath

nan_codepoint(T::Type{<:AbstractAIFloat}) = nmagitudes(T) + 0x01
nan_codepoint(x::T) where {T<:AbstractAIFloat} = nan_codepoint(T)

nonan(xs::AbstractVector) = filter(!isnan, xs)
finite(xs::AbstractVector) = filter(isfinite, xs)

Base.frexp(xs::AbstractVector{T}) where {T} = 
    map(Base.frexp, xs)

Base.ldexp(frxp::Tuple{F,I}) where {F,I} = ldexp(frxp...) 

Base.ldexp(frs::AbstractVector{T}, xps::AbstractVector{I}) where {T, I} = 
    map(Base.ldexp, frs, xps)

Base.ldexp(frxps::AbstractVector{<:Tuple{T,I}}) where {T, I} = 
    map(Base.ldexp, first.(frxps), last.(frxps))

"""
clean_frexp(xs) -> (fr, xp)

Returns a tuple of vectors containing the significands and exponents
of the input vector `xs`, significands cleaned-up.
"""
function clean_frexp(xs::AbstractVector{T}) where {T}
    idxnan  = findfirst(isnan , xs)
    if !isnothing(idxnan)
        ys = xs[1:(idxnan-1)]
        if idxnan < length(xs)
           ys2 = xs[(idxnan+1):end]
           append!(ys, ys2)
        end
    end
    frxp = frexp(ys)
    fr = map(Float64, first.(frxp))
    xp = last.(frxp)
    z = zip(fr, xp)
    zz = collect(z)
end

function clean_frexp(xs::Vector{Float128})
    idxnan  = findfirst(isnan , xs)
    if !isnothing(idxnan)
        ys = xs[1:(idxnan-1)]
        if idxnan < length(xs)
           ys2 = xs[(idxnan+1):end]
           append!(ys, ys2)
        end
    end
    frxp = frexp(ys)
    fr = map(Float64, first.(frxp))
    xp = last.(frxp)
    z = zip(fr, xp)
    zz = collect(z)
end


function clean_ldexp(xs::AbstractVector{T}) where {T}
    idxnan  = findfirst(isnan , xs)
    if !isnothing(idxnan)
        ys = xs[1:(idxnan-1)]
        if idxnan < length(xs)
           ys2 = xs[(idxnan+1):end]
           append!(ys, ys2)
        end
    else
        ys = xs
    end
    
    frxp = frexp(ys)
    fr = map(Float64, first.(frxp))
    xp = last.(frxp)
    z = zip(fr, xp)
    zz = collect(z)

    a = map(a->ldexp(a...), zz)
    a
end
