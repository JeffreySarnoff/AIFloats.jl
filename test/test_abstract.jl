@testset "Abstract Type Tests" begin
    @testset "Type Hierarchy" begin
        # Test basic type hierarchy
        @test AbstractAIFloat <: AbstractFloat
        @test AbstractSigned <: AbstractAIFloat
        @test AbstractUnsigned <: AbstractAIFloat
        
        # Test finite/extended hierarchy
        @test AkoSignedFinite <: AbstractSigned
        @test AkoSignedExtended <: AbstractSigned
        @test AkoUnsignedFinite <: AbstractUnsigned
        @test AkoUnsignedExtended <: AbstractUnsigned
    end
    
    @testset "Type Parameters" begin
        # Test that abstract types can be parameterized
        TestSignedFinite = AkoSignedFinite{8, 4}
        TestUnsignedExtended = AkoUnsignedExtended{6, 3}
        
        @test TestSignedFinite <: AkoSignedFinite
        @test TestUnsignedExtended <: AkoUnsignedExtended
        
        # Test parameter extraction would work with concrete types
        @test TestSignedFinite <: AbstractAIFloat{8, 4}
        @test TestUnsignedExtended <: AbstractAIFloat{6, 3}
    end
    
    @testset "Type Relationships" begin
        # Test disjoint unions
        @test !(AbstractSigned <: AbstractUnsigned)
        @test !(AbstractUnsigned <: AbstractSigned)
        @test !(AkoSignedFinite <: AkoSignedExtended)
        @test !(AkoSignedExtended <: AkoSignedFinite)
        @test !(AkoUnsignedFinite <: AkoUnsignedExtended)
        @test !(AkoUnsignedExtended <: AkoUnsignedFinite)
    end
    
    @testset "Common Supertype" begin
        # Test common supertypes
        @test typejoin(AbstractSigned, AbstractUnsigned) == AbstractAIFloat
        @test typejoin(AkoSignedFinite, AkoSignedExtended) == AbstractSigned
        @test typejoin(AkoUnsignedFinite, AkoUnsignedExtended) == AbstractUnsigned
    end
end

