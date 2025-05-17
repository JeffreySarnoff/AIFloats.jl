using AlignedAllocs, FloatsForML, Test
# AbstractAIFloat{K,P}
include("test_inits.jl")
using .TestInits

include("test_abstract.jl")

include("test_absuais.jl")
include("test_abssais.jl")

include("test_absufais.jl")
include("test_abssfais.jl")

include("test_absueais.jl")
include("test_absseais.jl")
