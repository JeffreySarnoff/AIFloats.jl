Base.promote_rule(x::ArbReal{P}, y::BigFloat) where {P} = 
    precision(BigFloat) > P ? BigFloat : ArbReal{P}

ArbNumerics.ArbReal{P}(x) where {P} = ArbReal{P}(BigFloat(x))

function ArbNumerics.ArbReal{P}(x::Float128) where {P}
    xx = round(BigFloat(x); base=2, sigdigits=P)       
    ArbReal{128}(xx)
end

function Base.convert(::Type{ArbReal{128}}, x::Float128)
    xx = round(BigFloat(x); base=2, sigdigits=128)
    ArbReal{128}(xx)
end


function Float128(s::String)
    Float128(BigFloat(s))
end

function Float128(x::ArbReal{P}) where {P}
    Float128(string(x))
end

function Base.convert(::Type{ArbReal{P}}, x::Float128) where {P}
    xx = round(BigFloat(x); base=2, sigdigits=128)
    ArbReal{P}(xx)
end

function Base.convert(::Type{Float128}, x::ArbReal{P}) where {P}
    xx = round(BigFloat(x); base=2, sigdigits=128)
    Float128(xx)
end
