@testset "Abstract Type Tests" begin
    @testset "Type Hierarchy" begin
        # Test basic type hierarchy
        @test AbstractAIFloat <: AbstractFloat
        @test AbstractSignedFloat <: AbstractAIFloat
        @test AbstractUnsignedFloat <: AbstractAIFloat
        
        # Test finite/extended hierarchy
        @test AbstractSignedFinite <: AbstractSignedFloat
        @test AbstractSignedExtended <: AbstractSignedFloat
        @test AbstractUnsignedFinite <: AbstractUnsignedFloat
        @test AbstractUnsignedExtended <: AbstractUnsignedFloat
    end
    
    @testset "Type Parameters" begin
        # Test that abstract types can be parameterized
        TestSignedFinite = AbstractSignedFinite{8, 4}
        TestUnsignedExtended = AbstractUnsignedExtended{6, 3}
        
        @test TestSignedFinite <: AbstractSignedFinite
        @test TestUnsignedExtended <: AbstractUnsignedExtended
        
        # Test parameter extraction would work with concrete types
        @test TestSignedFinite <: AbstractAIFloat{8, 4}
        @test TestUnsignedExtended <: AbstractAIFloat{6, 3}
    end
    
    @testset "Type Relationships" begin
        # Test disjoint unions
        @test !(AbstractSignedFloat <: AbstractUnsignedFloat)
        @test !(AbstractUnsignedFloat <: AbstractSignedFloat)
        @test !(AbstractSignedFinite <: AbstractSignedExtended)
        @test !(AbstractSignedExtended <: AbstractSignedFinite)
        @test !(AbstractUnsignedFinite <: AbstractUnsignedExtended)
        @test !(AbstractUnsignedExtended <: AbstractUnsignedFinite)
    end
    
    @testset "Common Supertype" begin
        # Test common supertypes
        @test typejoin(AbstractSignedFloat, AbstractUnsignedFloat) == AbstractAIFloat
        @test typejoin(AbstractSignedFinite, AbstractSignedExtended) == AbstractSignedFloat
        @test typejoin(AbstractUnsignedFinite, AbstractUnsignedExtended) == AbstractUnsignedFloat
    end
end

