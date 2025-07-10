@testset "Exponents Tests" begin
    @testset "Exponent Bias" begin
        # Signed types: bias = 2^(Bits - SigBits - 1)
        @test exp_bias(TestSignedFinite{8, 4}) == 8   # 2^(8-4-1) = 2^3 = 8
        @test exp_bias(TestSignedFinite{6, 3}) == 4   # 2^(6-3-1) = 2^2 = 4
        
        # Unsigned types: bias = 2^(Bits - SigBits)  
        @test exp_bias(TestUnsignedFinite{8, 4}) == 16  # 2^(8-4) = 2^4 = 16
        @test exp_bias(TestUnsignedFinite{6, 3}) == 8   # 2^(6-3) = 2^3 = 8
        
        # Test with instances
        test_instance = TestSignedFinite{8, 4}()
        @test exp_bias(test_instance) == 8
    end
    
    @testset "Exponent Field Characteristics" begin
        T = TestSignedFinite{8, 4}
        
        # Field max is based on number of exponent values
        @test exp_field_max(T) == nvalues_exp(T) - 1
        
        # Test unbiased normal range
        bias = exp_bias(T)
        field_max = exp_field_max(T)
        
        @test exp_unbiased_normal_max(T) == field_max - bias
        @test exp_unbiased_normal_min(T) == -(field_max - bias)
        @test exp_unbiased_subnormal(T) == exp_unbiased_normal_min(T)
    end
    
    @testset "Exponent Values and Ranges" begin
        T = TestSignedFinite{8, 4}
        
        # Basic exponent range
        exp_min = exp_unbiased_min(T)
        exp_max = exp_unbiased_max(T)
        @test exp_min == exp_unbiased_normal_min(T)
        @test exp_max == exp_unbiased_normal_max(T)
        @test exp_min < 0 < exp_max  # Should span zero
        
        # Subnormal exponent
        @test expSubnormal(T) == exp_unbiased_subnormal(T)
        @test expSubnormal(T) == exp_min
        
        # Test exponent value conversion
        @test exp_value_min(T) isa AbstractFloat
        @test exp_value_max(T) isa AbstractFloat
        @test exp_value_min(T) < exp_value_max(T)
        @test exp_subnormal_value(T) == exp_value_min(T)
    end
    
    @testset "Exponent Collections" begin
        T = TestSignedFinite{6, 3}
        
        # Test unbiased normals
        unbiased_normals = exp_unbiased_normal_seq(T)
        @test isa(unbiased_normals, Vector)
        @test length(unbiased_normals) > 0
        @test minimum(unbiased_normals) == exp_unbiased_normal_min(T)
        @test maximum(unbiased_normals) == exp_unbiased_normal_max(T)
        
        # Test unbiased values (includes subnormal)
        unbiased_values = exp_unbiased_seq(T)
        @test length(unbiased_values) == length(unbiased_normals) + 1
        @test unbiased_values[1] == exp_unbiased_subnormal(T)
        
        # Test normal values (powers of 2)
        normal_values = exp_normal_value_seq(T)
        @test isa(normal_values, Vector{<:AbstractFloat})
        @test length(normal_values) == length(unbiased_normals)
        @test all(v -> v > 0, normal_values)  # All positive
        
        # Test exp values (includes subnormal value)
        exp_vals = exp_value_seq(T)
        @test length(exp_vals) == length(normal_values) + 1
        @test exp_vals[1] == exp_subnormal_value(T)
    end
    
    @testset "Exponent Consistency" begin
        for Bits in 4:8
            for SigBits in 2:(Bits-1)
                T = TestSignedFinite{Bits, SigBits}
                
                # Test basic relationships
                @test exp_unbiased_normal_min(T) <= 0
                @test exp_unbiased_normal_max(T) >= 0
                @test exp_unbiased_normal_min(T) == -exp_unbiased_normal_max(T)
                @test exp_unbiased_subnormal(T) == exp_unbiased_normal_min(T)
                
                # Test value relationships
                @test exp_subnormal_value(T) == exp_value_min(T)
                @test exp_value_min(T) <= exp_value_max(T)
                
                # Test collection sizes
                normals = exp_unbiased_normal_seq(T)
                @test length(normals) == 2 * exp_unbiased_normal_max(T) + 1
                
                # Test that exponent values are powers of 2
                normal_vals = exp_normal_value_seq(T)
                subval = exp_subnormal_value(T)
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
        @test exp_bias(TU) > exp_bias(TS)
        
        # Both should have valid exponent ranges
        @test exp_unbiased_normal_max(TS) > 0
        @test exp_unbiased_normal_max(TU) > 0
        @test exp_unbiased_normal_min(TS) < 0
        @test exp_unbiased_normal_min(TU) < 0
    end
    
    @testset "Edge Cases" begin
        # Test minimal configuration
        T_min = TestSignedFinite{3, 2}
        @test exp_bias(T_min) == 1  # 2^(3-2-1) = 2^0 = 1
        @test exp_unbiased_normal_max(T_min) >= 0
        @test exp_unbiased_normal_min(T_min) <= 0
        
        # Test that all functions return reasonable values
        @test exp_value_min(T_min) > 0
        @test exp_value_max(T_min) >= exp_value_min(T_min)
        @test exp_subnormal_value(T_min) == exp_value_min(T_min)
    end
    
    @testset "Instance vs Type Functions" begin
        # Test that exponent functions work on both types and instances
        test_type = TestSignedFinite{8, 4}
        test_instance = test_type()
        
        @test exp_bias(test_type) == exp_bias(test_instance)
        @test exp_unbiased_min(test_type) == exp_unbiased_min(test_instance)
        @test exp_unbiased_max(test_type) == exp_unbiased_max(test_instance)
        @test exp_value_min(test_type) == exp_value_min(test_instance)
        @test exp_value_max(test_type) == exp_value_max(test_instance)
        @test exp_subnormal_value(test_type) == exp_subnormal_value(test_instance)
    end
end

