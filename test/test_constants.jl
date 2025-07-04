using Test
using AIFloats, Quadmath
using Static
using AIFloats: BitsSmallMin, BitsSmallMax, BitsLargeMin, BitsLargeMax, BitsTop,
      typeforcode, typeforfloat

@testset "Constants Tests" begin
    @testset "Bit Range Constants" begin
        @test AIFloats.BitsSmallMin == 2
        @test AIFloats.BitsSmallMax == 8
        @test AIFloats.BitsLargeMin == 11
        @test AIFloats.BitsLargeMax == 15
        @test AIFloats.BitsTop == 16
    end
    
    @testset "Type Constants" begin
        @test AIFloats.CODE_TYPES == (UInt8, UInt16)
        @test AIFloats.FLOAT_TYPES == (Float64, Float64, Float128)
        @test AIFloats.CODE == Union{UInt8, UInt16}
        @test AIFloats.FLOAT == Union{Float64, Float128}
    end
        
    @testset "Type Selection Functions" begin
        # Test typeforcode
        @test AIFloats.typeforcode(4) == UInt8
        @test AIFloats.typeforcode(8) == UInt8
        @test AIFloats.typeforcode(9) == UInt16
        @test AIFloats.typeforcode(15) == UInt16
        @test AIFloats.typeforcode(static(4)) == UInt8
        @test AIFloats.typeforcode(static(12)) == UInt16
        
        # Test typeforfloat  
        @test AIFloats.typeforfloat(4) == Float64
        @test AIFloats.typeforfloat(8) == Float64
        @test AIFloats.typeforfloat(11) == Float128
        @test AIFloats.typeforfloat(15) == Float128
        @test AIFloats.typeforfloat(static(6)) == Float64
        @test AIFloats.typeforfloat(static(13)) == Float128
    end
    
    @testset "Type Selection Edge Cases" begin
        # Boundary testing
        @test AIFloats.typeforcode(AIFloats.BitsSmallMax) == UInt8
        @test AIFloats.typeforcode(AIFloats.BitsSmallMax + 1) == UInt16
        
        @test AIFloats.typeforfloat(AIFloats.BitsSmallMax) == Float64
        @test AIFloats.typeforfloat(AIFloats.BitsLargeMin) == Float128
    end
end

