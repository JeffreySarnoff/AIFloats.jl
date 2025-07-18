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

function Base.ldexp(ld::Float64, xp::ArbReal{P}) where {P}
	px = round(Int, xp)
	ldexp(ld, px)
end

function Base.ldexp(ld::F1, xp::F2) where {F1<:AbstractFP, F2<:AbstractFP}
	px = round(Int, xp)
	ldexp(ld, px)
end

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

function clean_frexp(x::T) where {T<:AbstractFP}
	
	try
		fr, xp = frexp(x)
	catch
		fr1, xp1 = frexp(BigFloat(x))
		fr = T(fr1)
		xp = round(Int, xp1)
	finally
   	    (fr, xp)
   	end
end

using ArbNumerics
import Base: frexp, ldexp

# ldexp( x, n ) == x * 2^n

adjust(arbreal_precision) = arbreal_precision + 4

function Base.ldexp(x::X, y::Y) where {X<:AbstractFP, Y::AbstractFP}
    if isinteger(Y)
    	return ldexp(x, round(Int, y))
    end

    z = Y(2)^y
    x * z
end

function Base.ldexp(x::X, y::I) where {X<:AbstractFP, I<:Integer}
	z = (X(2))^y
	x * z
end

