using Test
using AIFloats, AlignedAllocs
using Aqua

# Test organization following Julia best practices
@testset "AIFloats.jl Tests" begin
    # Code quality tests
    @testset "Code Quality" begin
        Aqua.test_all(AIFloats)
    end
    
    # Include all test files
    include("test_constants.jl")
    include("test_abstract.jl")
    include("test_predicates.jl")
    include("test_counts.jl")
    include("test_exponents.jl")
    include("test_significands.jl")
    include("test_encodings.jl")
    include("test_extrema.jl")
    include("test_foundation.jl")
    include("test_unsigned.jl")
    include("test_signed.jl")
    include("test_rounding.jl")
    include("test_indices.jl")
    include("test_aifloats_main.jl")
end