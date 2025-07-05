@testset "Abstract Type Tests" begin
    @testset "Type Hierarchy" begin
        # Test basic type hierarchy
        @test AbstractAIFloat <: AbstractFloat
        @test AbsSignedFloat <: AbstractAIFloat
        @test AbsUnsignedFloat <: AbstractAIFloat
        
        # Test finite/extended hierarchy
        @test AbsSignedFiniteFloat <: AbsSignedFloat
        @test AbsSignedExtendedFloat <: AbsSignedFloat
        @test AbsUnsignedFiniteFloat <: AbsUnsignedFloat
        @test AbsUnsignedExtendedFloat <: AbsUnsignedFloat
    end
    
    @testset "Type Parameters" begin
        # Test that abstract types can be parameterized
        TestSignedFinite = AbsSignedFiniteFloat{8, 4}
        TestUnsignedExtended = AbsUnsignedExtendedFloat{6, 3}
        
        @test TestSignedFinite <: AbsSignedFiniteFloat
        @test TestUnsignedExtended <: AbsUnsignedExtendedFloat
        
        # Test parameter extraction would work with concrete types
        @test TestSignedFinite <: AbstractAIFloat{8, 4}
        @test TestUnsignedExtended <: AbstractAIFloat{6, 3}
    end
    
    @testset "Type Relationships" begin
        # Test disjoint unions
        @test !(AbsSignedFloat <: AbsUnsignedFloat)
        @test !(AbsUnsignedFloat <: AbsSignedFloat)
        @test !(AbsSignedFiniteFloat <: AbsSignedExtendedFloat)
        @test !(AbsSignedExtendedFloat <: AbsSignedFiniteFloat)
        @test !(AbsUnsignedFiniteFloat <: AbsUnsignedExtendedFloat)
        @test !(AbsUnsignedExtendedFloat <: AbsUnsignedFiniteFloat)
    end
    
    @testset "Common Supertype" begin
        # Test common supertypes
        @test typejoin(AbsSignedFloat, AbsUnsignedFloat) == AbstractAIFloat
        @test typejoin(AbsSignedFiniteFloat, AbsSignedExtendedFloat) == AbsSignedFloat
        @test typejoin(AbsUnsignedFiniteFloat, AbsUnsignedExtendedFloat) == AbsUnsignedFloat
    end
end

