using Test
using AIFloats
using AIFloats: AbsSignedFiniteFloat, AbsUnsignedFiniteFloat,
                  foundation_magnitudes, two_pow, foundation_extremal_exps,
                  foundation_exps, normal_exp_stride, exp_unbiased_magnitude_strides,
                  significand_magnitudes, nBits, typeforfloat, nMagnitudes, nExpValues,
                  expUnbiasedSubnormal, expUnbiasedNormals
using Quadmath

@testset "Foundation Tests" begin
    @testset "Foundation Magnitudes" begin
        T = TestSignedFinite{6, 3}
        
        magnitudes = foundation_magnitudes(T)
        @test isa(magnitudes, Vector)
        @test length(magnitudes) > 0
        
        # Should be monotonically increasing
        @test issorted(magnitudes)
        
        # First element should be zero
        @test magnitudes[1] == 0
        
        # All subsequent elements should be positive
        @test all(x -> x > 0, magnitudes[2:end])
        
        # Should use the correct float type
        expected_type = typeforfloat(nBits(T))
        @test eltype(magnitudes) == expected_type
    end
    
    @testset "Two Power Function" begin
        # Test basic powers of 2
        @test two_pow(0) ≈ 1.0
        @test two_pow(1) ≈ 2.0
        @test two_pow(3) ≈ 8.0
        @test two_pow(-1) ≈ 0.5
        @test two_pow(-3) ≈ 0.125
        
        # Test with floating-point inputs
        @test two_pow(0.0) ≈ 1.0
        @test two_pow(2.5) ≈ 2.0^2.5
        @test two_pow(-1.5) ≈ 2.0^(-1.5)
        
        # Test edge cases
        @test two_pow(0.5) ≈ sqrt(2.0)
        @test two_pow(0.25) ≈ 2.0^0.25
    end
    
    @testset "Foundation Exponents" begin
        T = TestSignedFinite{6, 3}
        
        exp_min, exp_max = foundation_extremal_exps(T)
        @test exp_min < 0 < exp_max
        @test exp_min == -exp_max  # Should be symmetric
        
        exps = foundation_exps(T)
        @test isa(exps, AbstractRange)
        @test minimum(exps) == exp_min
        @test maximum(exps) == exp_max
        @test exp_min in exps
        @test exp_max in exps
        @test 0 in exps  # Should include zero exponent
    end
    
    @testset "Exponent Stride Calculation" begin
        T = TestSignedFinite{8, 4}
        
        stride = normal_exp_stride(T)
        @test stride > 0
        @test isa(stride, Integer)
        
        # Should be ceiling division of magnitudes by exponent values
        expected = cld(nMagnitudes(T), nExpValues(T))
        @test stride == expected
    end
    
    @testset "Unbiased Magnitude Strides" begin
        T = TestSignedFinite{6, 3}
        
        strides = exp_unbiased_magnitude_strides(T)
        @test isa(strides, Vector)
        @test length(strides) > 0
        
        # Should contain subnormal exponent values
        subnormal_exp = expUnbiasedSubnormal(T)
        @test any(x -> x ≈ subnormal_exp, strides)
        
        # Should contain normal exponent values
        normal_exps = expUnbiasedNormals(T)
        for exp in normal_exps
            @test any(x -> x ≈ exp, strides)
        end
    end
    
    @testset "Foundation Magnitude Structure" begin
        T = TestSignedFinite{7, 3}
        
        magnitudes = foundation_magnitudes(T)
        
        # Should start with significand pattern
        significands = significand_magnitudes(T)
        @test length(magnitudes) >= length(significands)
        
        # Should incorporate exponent scaling
        exp_strides = exp_unbiased_magnitude_strides(T)
        @test length(exp_strides) > 0
        
        # Values should be reasonable magnitudes
        @test all(x -> x >= 0, magnitudes)
        @test magnitudes[1] == 0  # Zero should be first
    end
    
    @testset "Power-of-2 Foundation Exponents" begin
        T = TestSignedFinite{6, 3}
        
        # Test that we can compute powers of foundation exponents
        exps = foundation_exps(T)
        powers = map(two_pow, exps)
        
        @test isa(powers, Vector)
        @test length(powers) == length(exps)
        @test all(x -> x > 0, powers)  # All should be positive
        
        # Should be in ascending order for positive exponents
        pos_exps = filter(x -> x >= 0, exps)
        pos_powers = map(two_pow, pos_exps)
        @test issorted(pos_powers)
    end
    
    @testset "Foundation Consistency" begin
        # Test that foundation magnitudes are consistent across different types
        for Bits in 4:7
            for SigBits in 2:(Bits-1)
                T = TestSignedFinite{Bits, SigBits}
                
                magnitudes = foundation_magnitudes(T)
                
                # Basic sanity checks
                @test length(magnitudes) > 0
                @test magnitudes[1] == 0
                @test issorted(magnitudes)
                @test all(x -> x >= 0, magnitudes)
                @test all(isfinite, magnitudes)
                
                # Should have reasonable range
                @test maximum(magnitudes) > minimum(magnitudes)
            end
        end
    end
    
    @testset "High Precision Handling" begin
        T = TestSignedFinite{12, 6}  # Larger precision
        
        magnitudes = foundation_magnitudes(T)
        
        # Should handle larger ranges gracefully
        @test length(magnitudes) > 0
        @test issorted(magnitudes)
        @test eltype(magnitudes) == typeforfloat(nBits(T))
        
        # Should not overflow or underflow
        @test all(isfinite, magnitudes)
        @test !any(iszero, magnitudes[2:end])  # Only first should be zero
    end
    
    @testset "Instance vs Type Functions" begin
        # Test that foundation functions work on both types and instances
        test_type = TestSignedFinite{6, 3}
        test_instance = test_type()
        
        @test foundation_magnitudes(test_type) == foundation_magnitudes(test_instance)
        @test foundation_extremal_exps(test_type) == foundation_extremal_exps(test_instance)
        @test foundation_exps(test_type) == foundation_exps(test_instance)
        @test normal_exp_stride(test_type) == normal_exp_stride(test_instance)
        @test exp_unbiased_magnitude_strides(test_type) == exp_unbiased_magnitude_strides(test_instance)
    end
    
    @testset "Edge Cases" begin
        # Test minimal configuration
        T_min = TestSignedFinite{3, 2}
        
        magnitudes = foundation_magnitudes(T_min)
        @test length(magnitudes) >= 2  # At least zero and something positive
        @test magnitudes[1] == 0
        
        exps = foundation_exps(T_min)
        @test length(exps) > 0
        
        stride = normal_exp_stride(T_min)
        @test stride > 0
    end
    
    @testset "Numerical Accuracy" begin
        T = TestSignedFinite{8, 4}
        
        # Test that two_pow gives accurate results
        for exp in -5:5
            computed = two_pow(exp)
            expected = 2.0^exp
            @test computed ≈ expected
        end
        
        # Test with fractional exponents
        for exp in [-2.5, -1.5, -0.5, 0.5, 1.5, 2.5]
            computed = two_pow(exp)
            expected = 2.0^exp
            @test computed ≈ expected # rtol=1e-14
        end
    end
    
    @testset "Memory and Performance" begin
        T = TestSignedFinite{8, 4}
        
        # Foundation magnitudes should be efficiently allocated
        @test @allocated(foundation_magnitudes(T)) > 0
        
        magnitudes = foundation_magnitudes(T)
        @test isa(magnitudes, Vector)
        
        # Should be reasonable size
        @test length(magnitudes) <= 2^nBits(T)
        @test length(magnitudes) >= nPrenormalMagnitudes(T)
    end
    
    @testset "Type Correctness" begin
        # Test that appropriate types are used for different bit widths
        T_small = TestSignedFinite{6, 3}
        T_large = TestSignedFinite{12, 6}
        
        magnitudes_small = foundation_magnitudes(T_small)
        magnitudes_large = foundation_magnitudes(T_large)
        
        @test eltype(magnitudes_small) == typeforfloat(6)
        @test eltype(magnitudes_large) == typeforfloat(12)
        
        # Both should work correctly
        @test issorted(magnitudes_small)
        @test issorted(magnitudes_large)
    end
end


