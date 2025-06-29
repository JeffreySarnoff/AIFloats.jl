#=
   const MaybeBool = Union{Missing, Bool}
=#

differ(x::Bool, y::Bool)       = xor(x, y)

differ(x::Bool, y::Missing)    = true
differ(x::Missing, y::Bool)    = true
differ(x::Missing, y::Missing) = true               # this relation is necessary

Base.convert(::Type{Bool}, x::Missing) = false      # the conversion logic promulgates consistency
Base.convert(::Type{Missing}, x::Bool) = missing    # 

