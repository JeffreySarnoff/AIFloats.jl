using Test
using AIFloats
using AIFloats: AbsSignedFiniteFloat, AbsUnsignedFiniteFloat, expBias, expMin, expMax,
                expFieldMax, expMinValue, expMaxValue, expSubnormalValue, expUnbiasedNormalMin,
                expUnbiasedNormalMax, expUnbiasedSubnormal, expUnbiasedNormals,
                expUnbiasedValues, expNormalValues, expValues

# Create test types for exponent testing
struct TestSignedFinite{Bits, SigBits} <: AbsSignedFiniteFloat{Bits, SigBits} end
struct TestUnsignedFinite{Bits, SigBits} <: AbsUnsignedFiniteFloat{Bits, SigBits} end

@testset "Exponents Tests" begin
    @testset "Exponent Bias" begin
        # Signed types: bias = 2^(Bits - SigBits - 1)
        @test expBias(TestSignedFinite{8, 4}) == 8   # 2^(8-4-1) = 2^3 = 8
        @test expBias(TestSignedFinite{6, 3}) == 4   # 2^(6-3-1) = 2^2 = 4
        
        # Unsigned types: bias = 2^(Bits - SigBits)  
        @test expBias(TestUnsignedFinite{8, 4}) == 16  # 2^(8-4) = 2^4 = 16
        @test expBias(TestUnsignedFinite{6, 3}) == 8   # 2^(6-3) = 2^3 = 8
        
        # Test with instances
        test_instance = TestSignedFinite{8, 4}()
        @test expBias(test_instance) == 8
    end
    
    @testset "Exponent Field Characteristics" begin
        T = TestSignedFinite{8, 4}
        
        # Field max is based on number of exponent values
        @test expFieldMax(T) == nExpValues(T) - 1
        
        # Test unbiased normal range
        bias = expBias(T)
        field_max = expFieldMax(T)
        
        @test expUnbiasedNormalMax(T) == field_max - bias
        @test expUnbiasedNormalMin(T) == -(field_max - bias)
        @test expUnbiasedSubnormal(T) == expUnbiasedNormalMin(T)
    end
    
    @testset "Exponent Values and Ranges" begin
        T = TestSignedFinite{8, 4}
        
        # Basic exponent range
        exp_min = expMin(T)
        exp_max = expMax(T)
        @test exp_min == expUnbiasedNormalMin(T)
        @test exp_max == expUnbiasedNormalMax(T)
        @test exp_min < 0 < exp_max  # Should span zero
        
        # Subnormal exponent
        @test expSubnormal(T) == expUnbiasedSubnormal(T)
        @test expSubnormal(T) == exp_min
        
        # Test exponent value conversion
        @test expMinValue(T) isa AbstractFloat
        @test expMaxValue(T) isa AbstractFloat
        @test expMinValue(T) < expMaxValue(T)
        @test expSubnormalValue(T) == expMinValue(T)
    end
    
    @testset "Exponent Collections" begin
        T = TestSignedFinite{6, 3}
        
        # Test unbiased normals
        unbiased_normals = expUnbiasedNormals(T)
        @test isa(unbiased_normals, Vector)
        @test length(unbiased_normals) > 0
        @test minimum(unbiased_normals) == expUnbiasedNormalMin(T)
        @test maximum(unbiased_normals) == expUnbiasedNormalMax(T)
        
        # Test unbiased values (includes subnormal)
        unbiased_values = expUnbiasedValues(T)
        @test length(unbiased_values) == length(unbiased_normals) + 1
        @test unbiased_values[1] == expUnbiasedSubnormal(T)
        
        # Test normal values (powers of 2)
        normal_values = expNormalValues(T)
        @test isa(normal_values, Vector{<:AbstractFloat})
        @test length(normal_values) == length(unbiased_normals)
        @test all(v -> v > 0, normal_values)  # All positive
        
        # Test exp values (includes subnormal value)
        exp_vals = expValues(T)
        @test length(exp_vals) == length(normal_values) + 1
        @test exp_vals[1] == expSubnormalValue(T)
    end
    
    @testset "Exponent Consistency" begin
        for Bits in 4:8
            for SigBits in 2:(Bits-1)
                T = TestSignedFinite{Bits, SigBits}
                
                # Test basic relationships
                @test expUnbiasedNormalMin(T) <= 0
                @test expUnbiasedNormalMax(T) >= 0
                @test expUnbiasedNormalMin(T) == -expUnbiasedNormalMax(T)
                @test expUnbiasedSubnormal(T) == expUnbiasedNormalMin(T)
                
                # Test value relationships
                @test expSubnormalValue(T) == expMinValue(T)
                @test expMinValue(T) <= expMaxValue(T)
                
                # Test collection sizes
                normals = expUnbiasedNormals(T)
                @test length(normals) == 2 * expUnbiasedNormalMax(T) + 1
                
                # Test that exponent values are powers of 2
                normal_vals = expNormalValues(T)
                subval = expSubnormalValue(T)
                @test all(map(v -> v ≈ 2.0^log2(v), normal_vals))
                @test subval ≈ 2.0^log2(subval)
            end
        end
    end
    
    @testset "Type Differences" begin
        # Compare signed vs unsigned exponent characteristics
        TS = TestSignedFinite{8, 4}
        TU = TestUnsignedFinite{8, 4}
        
        # Unsigned should have larger bias
        @test expBias(TU) > expBias(TS)
        
        # Both should have valid exponent ranges
        @test expUnbiasedNormalMax(TS) > 0
        @test expUnbiasedNormalMax(TU) > 0
        @test expUnbiasedNormalMin(TS) < 0
        @test expUnbiasedNormalMin(TU) < 0
    end
    
    @testset "Edge Cases" begin
        # Test minimal configuration
        T_min = TestSignedFinite{3, 2}
        @test expBias(T_min) == 1  # 2^(3-2-1) = 2^0 = 1
        @test expUnbiasedNormalMax(T_min) >= 0
        @test expUnbiasedNormalMin(T_min) <= 0
        
        # Test that all functions return reasonable values
        @test expMinValue(T_min) > 0
        @test expMaxValue(T_min) >= expMinValue(T_min)
        @test expSubnormalValue(T_min) == expMinValue(T_min)
    end
    
    @testset "Instance vs Type Functions" begin
        # Test that exponent functions work on both types and instances
        test_type = TestSignedFinite{8, 4}
        test_instance = test_type()
        
        @test expBias(test_type) == expBias(test_instance)
        @test expMin(test_type) == expMin(test_instance)
        @test expMax(test_type) == expMax(test_instance)
        @test expMinValue(test_type) == expMinValue(test_instance)
        @test expMaxValue(test_type) == expMaxValue(test_instance)
        @test expSubnormalValue(test_type) == expSubnormalValue(test_instance)
    end
end

