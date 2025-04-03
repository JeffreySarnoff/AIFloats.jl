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

n_bits(::Type{BaseFloat{Bits, Precision}}) where {Bits, Precision} = Bits
n_fracbits(::Type{BaseFloat{Bits, Precision}}) where {Bits, Precision} = Precision - 1
n_expbits(::Type{BaseFloat{Bits, Precision}}) where {Bits, Precision} = Bits - Precision + 1
n_values(::Type{T}) where {Bits, Precision, T<:BaseFloat{Bits, Precision}} = 2^n_bits(T)
n_fractions(::Type{T}) where {Bits, Precision, T<:BaseFloat{Bits, Precision}} = 2^n_fracbits(T)
n_exponents(::Type{T}) where {Bits, Precision, T<:BaseFloat{Bits, Precision}} = 2^n_expbits(T)
n_fraction_cycles(::Type{T}) where {Bits, Precision, T<:BaseFloat{Bits, Precision}} = n_exponents(T)
n_exponent_cycles(::Type{T}) where {Bits, Precision, T<:BaseFloat{Bits, Precision}} = n_fractions(T)

for F in (:n_bits, :n_fracbits, :n_expbits, :n_values, 
          :n_fractions, :n_exponents, :n_fraction_cycles, :n_exponent_cycles)
    @eval $F(x::T) where {T<:BaseFloat} = $F(T)
end
