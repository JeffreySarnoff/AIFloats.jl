struct BaseFloat{Bits, Precision} <: AkoBaseFloat{Bits, Precision}
    encoding::Vector{T} where {T<:Union{UInt8, UInt16}}
    values::Vector{T} where {T<:Union{Float32, Float64}}

    function BaseFloat(Bits, Precision)
        codes = encoding(Bits, Precision)
        vals = values(Bits, Precision)
        new{Bits, Precision}(codes, vals)
    end
end

encoding(x::BaseFloat) = x.encoding
Base.values(x::BaseFloat) = x.values

bits(::Type{BaseFloat{Bits, Precision}}) where {Bits, Precision} = Bits
Base.precision(::Type{BaseFloat{Bits, Precision}}) where {Bits, Precision} = Precision

bits(x::BaseFloat{Bits, Precision}) where {Bits, Precision} = bits(typeof(x))
Base.precision(x::BaseFloat{Bits, Precision}) where {Bits, Precision} = precision(typeof(x))

nbits(::Type{BaseFloat{Bits, Precision}}) where {Bits, Precision} = Bits
nfractionbits(::Type{BaseFloat{Bits, Precision}}) where {Bits, Precision} = Precision - 1
nexponentbits(::Type{BaseFloat{Bits, Precision}}) where {Bits, Precision} = Bits - Precision + 1
nvalues(::Type{T}) where {Bits, Precision, T<:BaseFloat{Bits, Precision}} = 2^nbits(T)
nfractions(::Type{T}) where {Bits, Precision, T<:BaseFloat{Bits, Precision}} = 2^nfractionbits(T)
nexponents(::Type{T}) where {Bits, Precision, T<:BaseFloat{Bits, Precision}} = 2^nexponentbits(T)
nfractioncycles(::Type{T}) where {Bits, Precision, T<:BaseFloat{Bits, Precision}} = nexponents(T)
nexponentcycles(::Type{T}) where {Bits, Precision, T<:BaseFloat{Bits, Precision}} = nfractions(T)

for F in (:nbits, :nfractionbits, :nexponentbits, :nvalues, 
          :nfractions, :nexponents, :nfractioncycles, :nexponentcycles)
    @eval $F(x::T) where {T<:BaseFloat} = $F(T)
end
