import Base: precision, sort

const CodePoint  = Union{UInt8, UInt16}
const FloatValue = Union{Float32, Float64}

# UnsignedFiniteFloat{Bitwidth, Precision}, in encoding order
function uff_valuation(Bitwidth, Precision)
    values = simple_valuation(Bitwidth, Precision)
    values[end] = convert(eltype(values), NaN)
    values
end

# UnsignedInfiniteFloat{Bitwidth, Precision}, in encoding order
function uif_valuation(Bitwidth, Precision)
  values = uff_valuation(Bitwidth, Precision)
  values[end-1] = convert(eltype(values), Inf)
  values
end

# SignedFiniteFloat{Bitwidth, Precision}, in encoding order
function sff_valuation(Bitwidth, Precision)
  nonneg_values = simple_valuation(Bitwidth-1, Precision)
  neg_values = -1 .*  nonneg_values
  neg_values[1] = convert(eltype(nonneg_values), NaN)
  append!(nonneg_values, neg_values)
end

# SignedInfiniteFloat{Bitwidth, Precision}, in encoding order
function sif_valuation(Bitwidth, Precision)
  nonneg_values = simple_valuation(Bitwidth-1, Precision)
  nonneg_values[end] = convert(eltype(nonneg_values), Inf)
  neg_values = -1 .*  nonneg_values
  neg_values[1] = convert(eltype(nonneg_values), NaN)
  append!(nonneg_values, neg_values)
end

for (S,P,A,F) in (
    (:SignedInfiniteFloat, :SignedInfiniteFP, :AkoSignedInfiniteFloat, sif_valuation), 
    (:SignedFiniteFloat, :SignedFiniteFP,  :AkoSignedFiniteFloat, sff_valuation), 
    (:UnsignedInfiniteFloat, :UnsignedInfiniteFP, :AkoUnsignedInfiniteFloat, uif_valuation), 
    (:UnsignedFiniteFloat, :UnsignedFiniteFP, :AkoUnsignedFiniteFloat, uff_valuation), 
    )
  @eval begin

    struct $S{Bitwidth, Precision} <: $A{Bitwidth, Precision}
        codes::Vector{T} where {T<:Union{UInt8, UInt16}}
        floats::Vector{T} where {T<:Union{Float32, Float64}}

        function $S(Bitwidth, Precision)
            codes = encoding(Bitwidth, Precision)
            floats = $F(Bitwidth, Precision)
            new{Bitwidth, Precision}(codes, floats)
        end
    end

    $S(x::$S) = x
      
    struct $P{Bitwidth, Precision} <: $A{Bitwidth, Precision}
        codes::Vector{T} where {T<:Union{UInt8, UInt16}}
        floats::Vector{T} where {T<:Union{Float32, Float64}}

        function $P(Bitwidth, Precision)
            codes = encoding(Bitwidth, Precision)
            floats = $F(Bitwidth, Precision)

            perm = sortperm(floats)
            # there is a single NaN and it always compares as the most-negative value.
            nanidx = perm[end]
            perm[2:end] .= perm[1:end-1]
            perm[1] = nanidx

            sortedfloats = floats[perm]
            sortedcodes = codes[perm]  

            new{Bitwidth, Precision}(sortedcodes, sortedfloats)
        end
    end

    $P(x::$P) = x

  end
end

codes(@nospecialize(x::AbstractBinaryFloat))  = x.codes
floats(@nospecialize(x::AbstractBinaryFloat)) = x.floats
