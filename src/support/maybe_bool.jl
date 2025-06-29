#=
   const MaybeBool = Union{Nothing, Bool}
=#

differ(x::Bool, y::Bool)       = xor(x, y)

differ(x::Bool, y::Nothing)    = true
differ(x::Nothing, y::Bool)    = true
differ(x::Nothing, y::Nothing) = true               # this relation is necessary

Base.convert(::Type{Bool}, x::Nothing) = false      # the conversion logic promulgates consistency
Base.convert(::Type{Nothing}, x::Bool) = nothing    # 
