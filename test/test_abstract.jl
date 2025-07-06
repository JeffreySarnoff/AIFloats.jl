@testset "Abstract Type Tests" begin
    @testset "Type Hierarchy" begin
        # Test basic type hierarchy
        @test AbstractAIFloat <: AbstractFloat
        @test AbstractSigned <: AbstractAIFloat
        @test AbstractUnsigned <: AbstractAIFloat
        
        # Test finite/extended hierarchy
        @test AbstractSignedFinite <: AbstractSigned
        @test AbstractSignedExtended <: AbstractSigned
        @test AbstractUnsignedFinite <: AbstractUnsigned
        @test AbstractUnsignedExtended <: AbstractUnsigned
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
        @test !(AbstractSigned <: AbstractUnsigned)
        @test !(AbstractUnsigned <: AbstractSigned)
        @test !(AbstractSignedFinite <: AbstractSignedExtended)
        @test !(AbstractSignedExtended <: AbstractSignedFinite)
        @test !(AbstractUnsignedFinite <: AbstractUnsignedExtended)
        @test !(AbstractUnsignedExtended <: AbstractUnsignedFinite)
    end
    
    @testset "Common Supertype" begin
        # Test common supertypes
        @test typejoin(AbstractSigned, AbstractUnsigned) == AbstractAIFloat
        @test typejoin(AbstractSignedFinite, AbstractSignedExtended) == AbstractSigned
        @test typejoin(AbstractUnsignedFinite, AbstractUnsignedExtended) == AbstractUnsigned
    end
end

