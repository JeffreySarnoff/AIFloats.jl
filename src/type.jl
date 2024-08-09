struct BaseMicroFloat{Bitwidth, Precision} <: AkoBaseMicroFloat{Bitwidth, Precision}
    encoding::Vector{T} where {T<:Union{UInt8, UInt16}}
    values::Vector{T} where {T<:Union{Float32, Float64}}

    function BaseMicroFloat(Bitwidth, Precision)
        codes = encoding(Bitwidth, Precision)
        vals = values(Bitwidth, Precision)
        new{Bitwidth, Precision}(codes, vals)
    end
end

encoding(x::BaseMicroFloat) = x.encoding
Base.values(x::BaseMicroFloat) = x.values

bitwidth(::Type{BaseMicroFloat{Bitwidth, Precision}}) where {Bitwidth, Precision} = Bitwidth
Base.precision(::Type{BaseMicroFloat{Bitwidth, Precision}}) where {Bitwidth, Precision} = Precision

bitwidth(x::BaseMicroFloat{Bitwidth, Precision}) where {Bitwidth, Precision} = bitwidth(typeof(x))
Base.precision(x::BaseMicroFloat{Bitwidth, Precision}) where {Bitwidth, Precision} = precision(typeof(x))

nbits(::Type{BaseMicroFloat{Bitwidth, Precision}}) where {Bitwidth, Precision} = Bitwidth
nfractionbits(::Type{BaseMicroFloat{Bitwidth, Precision}}) where {Bitwidth, Precision} = Precision - 1
nexponentbits(::Type{BaseMicroFloat{Bitwidth, Precision}}) where {Bitwidth, Precision} = Bitwidth - Precision + 1
nvalues(::Type{T}) where {Bitwidth, Precision, T<:BaseMicroFloat{Bitwidth, Precision}} = 2^nbits(T)
nfractions(::Type{T}) where {Bitwidth, Precision, T<:BaseMicroFloat{Bitwidth, Precision}} = 2^nfractionbits(T)
nexponents(::Type{T}) where {Bitwidth, Precision, T<:BaseMicroFloat{Bitwidth, Precision}} = 2^nexponentbits(T)
nfractioncycles(::Type{T}) where {Bitwidth, Precision, T<:BaseMicroFloat{Bitwidth, Precision}} = nexponents(T)
nexponentcycles(::Type{T}) where {Bitwidth, Precision, T<:BaseMicroFloat{Bitwidth, Precision}} = nfractions(T)

for F in (:nbits, :nfractionbits, :nexponentbits, :nvalues, 
          :nfractions, :nexponents, :nfractioncycles, :nexponentcycles)
    @eval $F(x::T) where {T<:BaseMicroFloat} = $F(T)
end
