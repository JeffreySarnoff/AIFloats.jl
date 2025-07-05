using Test
using AIFloats
using AIFloats: AbsSignedFiniteFloat, AbsUnsignedFiniteFloat,
                  is_aifloat, is_signed, is_unsigned, is_finite, is_extended,
                  has_subnormals

@testset "Predicates Tests" begin
    @testset "is_aifloat" begin
        @test is_aifloat(TestSignedFinite{8, 4}) === true
        @test is_aifloat(TestUnsignedExtended{6, 3}) === true
        @test is_aifloat(Float64) === false
        @test is_aifloat(Int32) === false
        
        # Test with instances (should also work via dispatch)
        test_instance = TestSignedFinite{8, 4}()
        @test is_aifloat(test_instance) === true
    end
    
    @testset "is_signed and is_unsigned" begin
        @test is_signed(TestSignedFinite{8, 4}) === true
        @test is_signed(TestSignedExtended{6, 3}) === true
        @test is_signed(TestUnsignedFinite{8, 4}) === false
        @test is_signed(TestUnsignedExtended{6, 3}) === false
        
        @test is_unsigned(TestSignedFinite{8, 4}) === false
        @test is_unsigned(TestSignedExtended{6, 3}) === false
        @test is_unsigned(TestUnsignedFinite{8, 4}) === true
        @test is_unsigned(TestUnsignedExtended{6, 3}) === true
        
        # Test complementary nature
        @test is_signed(TestSignedFinite{8, 4}) != is_unsigned(TestSignedFinite{8, 4})
        @test is_signed(TestUnsignedFinite{8, 4}) != is_unsigned(TestUnsignedFinite{8, 4})
    end
    
    @testset "is_finite and is_extended" begin
        @test is_finite(TestSignedFinite{8, 4}) === true
        @test is_finite(TestUnsignedFinite{6, 3}) === true
        @test is_finite(TestSignedExtended{8, 4}) === false
        @test is_finite(TestUnsignedExtended{6, 3}) === false
        
        @test is_extended(TestSignedFinite{8, 4}) === false
        @test is_extended(TestUnsignedFinite{6, 3}) === false
        @test is_extended(TestSignedExtended{8, 4}) === true
        @test is_extended(TestUnsignedExtended{6, 3}) === true
        
        # Test complementary nature
        @test is_finite(TestSignedFinite{8, 4}) != is_extended(TestSignedFinite{8, 4})
        @test is_finite(TestSignedExtended{8, 4}) != is_extended(TestSignedExtended{8, 4})
    end
    
    @testset "has_subnormals" begin
        # Test that precision 1 formats don't have subnormals
        @test has_subnormals(TestSignedFinite{3, 1}) === false
        @test has_subnormals(TestUnsignedFinite{2, 1}) === false
        
        # Test that precision > 1 formats have subnormals
        @test has_subnormals(TestSignedFinite{8, 4}) === true
        @test has_subnormals(TestUnsignedExtended{6, 3}) === true
        @test has_subnormals(TestSignedExtended{5, 2}) === true
    end
    
    @testset "Predicate Consistency" begin
        # Test that all predicates are consistent across type variations
        for Bits in 4:8, SigBits in 2:(Bits-1)
            SF = TestSignedFinite{Bits, SigBits}
            SE = TestSignedExtended{Bits, SigBits}
            UF = TestUnsignedFinite{Bits, SigBits}
            UE = TestUnsignedExtended{Bits, SigBits}
            
            # All should be AIFloats
            @test is_aifloat(SF) && is_aifloat(SE) && is_aifloat(UF) && is_aifloat(UE)
            
            # Signedness should be consistent
            @test is_signed(SF) && is_signed(SE) && !is_signed(UF) && !is_signed(UE)
            @test !is_unsigned(SF) && !is_unsigned(SE) && is_unsigned(UF) && is_unsigned(UE)
            
            # Finiteness should be consistent
            @test is_finite(SF) && !is_finite(SE) && is_finite(UF) && !is_finite(UE)
            @test !is_extended(SF) && is_extended(SE) && !is_extended(UF) && is_extended(UE)
        end
    end
    
    @testset "Instance vs Type Predicates" begin
        # Test that predicates work both on types and instances
        test_type = TestSignedFinite{8, 4}
        test_instance = test_type()
        
        @test is_aifloat(test_type) === is_aifloat(test_instance)
        @test is_signed(test_type) === is_signed(test_instance)
        @test is_unsigned(test_type) === is_unsigned(test_instance)
        @test is_finite(test_type) === is_finite(test_instance)
        @test is_extended(test_type) === is_extended(test_instance)
        @test has_subnormals(test_type) === has_subnormals(test_instance)
    end
end

