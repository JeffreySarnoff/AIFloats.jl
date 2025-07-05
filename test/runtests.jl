using Test
using AIFloats

# Test organization following Julia best practices
@testset "AIFloats.jl Tests" begin
    # Code quality tests
    @testset "Code Quality" begin
#        Aqua.test_all(AIFloats)
    end
    # Create some test types for predicate testing
    struct TestSignedFinite{Bits, SigBits} <: AbsSignedFiniteFloat{Bits, SigBits} end
    struct TestSignedExtended{Bits, SigBits} <: AbsSignedExtendedFloat{Bits, SigBits} end
    struct TestUnsignedFinite{Bits, SigBits} <: AbsUnsignedFiniteFloat{Bits, SigBits} end
    struct TestUnsignedExtended{Bits, SigBits} <: AbsUnsignedExtendedFloat{Bits, SigBits} end

    # Include all test files
    include("test_constants.jl")        # ok
    include("test_abstract.jl")         # ok
    include("test_predicates.jl")       # ok
    include("test_counts.jl")           # ok
    include("test_exponents.jl")        # ok
    include("test_significands.jl")     # ok
    include("test_encodings.jl")        # ok
    include("test_extrema.jl")          # ok
    include("test_foundation.jl")       # ok
    include("test_unsigned.jl")         # ok
    include("test_signed.jl")           # ok
    include("test_indices.jl")          # ok
    include("test_rounding.jl")         # ok
    include("test_aifloats_main.jl")    # ok
end

