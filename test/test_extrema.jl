@testset "Extrema Tests" begin
    @testset "Prenormal Magnitude Bounds" begin
        T = TestSignedFinite{8, 4}
        
        first_nonzero = firstNonzeroPrenormalMagnitude(T)
        last_prenormal = lastPrenormalMagnitude(T)
        
        @test first_nonzero > 0
        @test last_prenormal > first_nonzero
        @test last_prenormal < 1.0
        
        # Test relationship to nmagnitudes_prenormal
        nprenormals = nmagnitudes_prenormal(T)
        @test first_nonzero ≈ 1.0 / nprenormals
        @test last_prenormal ≈ (nprenormals - 1) / nprenormals
    end
    
    @testset "Subnormal Magnitude Bounds" begin
        # Test types with subnormals
        T_with_sub = TestSignedFinite{8, 4}
        @test has_subnormals(T_with_sub)
        
        sub_min = magnitude_subnormal_min(T_with_sub)
        sub_max = magnitude_subnormal_max(T_with_sub)
        
        @test sub_min !== nothing
        @test sub_max !== nothing
        @test sub_min > 0
        @test sub_max > sub_min
        
        # Should be scaled by subnormal exponent value
        expected_min = firstNonzeroPrenormalMagnitude(T_with_sub) * exp_subnormal_value(T_with_sub)
        expected_max = lastPrenormalMagnitude(T_with_sub) * exp_subnormal_value(T_with_sub)
        @test sub_min ≈ expected_min
        @test sub_max ≈ expected_max
        
        # Test types without subnormals (precision = 1)
        T_no_sub = TestSignedFinite{3, 1}
        @test !has_subnormals(T_no_sub)
        @test magnitude_subnormal_min(T_no_sub) === nothing
        @test magnitude_subnormal_max(T_no_sub) === nothing
    end
    
    @testset "Normal Magnitude Bounds" begin
        # Test signed types
        TS = TestSignedFinite{8, 4}
        norm_min_s = magnitude_normal_min(TS)
        norm_max_s = magnitude_normal_max(TS)
        
        @test norm_min_s > 0
        @test norm_max_s > norm_min_s
        @test norm_min_s ≈ exp_value_min(TS)
        
        # Test unsigned types
        TU = TestUnsignedFinite{8, 4}
        norm_min_u = magnitude_normal_min(TU)
        norm_max_u = magnitude_normal_max(TU)
        
        @test norm_min_u > 0
        @test norm_max_u > norm_min_u
        @test norm_min_u ≈ exp_value_min(TU)
        
        # Compare signed vs unsigned max values
        # Unsigned should be slightly larger (no negative Inf slot)
        @test norm_max_u >= norm_max_s
    end
    
    @testset "Normal Maximum Calculations" begin
        # Test the formula for normal magnitude max
        T = TestSignedFinite{6, 3}
        norm_max = magnitude_normal_max(T)
        
        nprenormals = nmagnitudes_prenormal(T)
        exp_max_val = exp_value_max(T)
        
        # For signed finite: exp_max * (1 + (nprenormals - 1 - 1) / nprenormals)
        expected = exp_max_val * (1 + (nprenormals - 1 - is_extended(T)) / nprenormals)
        @test norm_max ≈ expected
        
        # Test unsigned finite
        TU = TestUnsignedFinite{6, 3}
        norm_max_u = magnitude_normal_max(TU)
        expected_u = exp_value_max(TU) * (1 + (nprenormals - 1 - 1) / nprenormals)
        @test norm_max_u ≈ expected_u
    end
    
    @testset "Extended vs Finite Differences" begin
        # Test that extended types account for infinity slots
        TS_finite = TestSignedFinite{8, 4}
        TS_extended = TestSignedExtended{8, 4}
        
        norm_max_finite = magnitude_normal_max(TS_finite)
        norm_max_extended = magnitude_normal_max(TS_extended)
        
        # Extended should have smaller normal max (infinity takes a slot)
        @test norm_max_extended < norm_max_finite
        
        # Test unsigned
        TU_finite = TestUnsignedFinite{8, 4}
        TU_extended = TestUnsignedExtended{8, 4}
        
        norm_max_u_finite = magnitude_normal_max(TU_finite)
        norm_max_u_extended = magnitude_normal_max(TU_extended)
        
        @test norm_max_u_extended < norm_max_u_finite
    end
    
    @testset "Subnormal vs Normal Relationship" begin
        T = TestSignedFinite{8, 4}
        
        # If subnormals exist, subnormal max should be less than normal min
        if has_subnormals(T)
            sub_max = magnitude_subnormal_max(T)
            norm_min = magnitude_normal_min(T)
            @test sub_max < norm_min
        end
    end
    
    @testset "Instance vs Type Functions" begin
        # Test that extrema functions work on both types and instances
        test_type = TestSignedFinite{8, 4}
        test_instance = test_type()
        
        @test magnitude_subnormal_min(test_type) == magnitude_subnormal_min(test_instance)
        @test magnitude_subnormal_max(test_type) == magnitude_subnormal_max(test_instance)
        @test magnitude_normal_min(test_type) == magnitude_normal_min(test_instance)
        @test magnitude_normal_max(test_type) == magnitude_normal_max(test_instance)
    end
    
    @testset "Edge Cases" begin
        # Test minimal configuration
        T_min = TestSignedFinite{3, 2}
        
        # Should still produce valid bounds
        norm_min = magnitude_normal_min(T_min)
        norm_max = magnitude_normal_max(T_min)
        @test norm_min > 0
        @test norm_max > norm_min
        
        # Test with subnormals
        if has_subnormals(T_min)
            sub_min = magnitude_subnormal_min(T_min)
            sub_max = magnitude_subnormal_max(T_min)
            @test sub_min !== nothing && sub_min > 0
            if nmagnitudes_subnormal(T_min) > 1
                @test sub_max !== nothing && sub_max > sub_min
            else
                @test sub_max !== nothing && sub_max >= sub_min
            end
            @test sub_max < norm_min
        end
    end
    
    @testset "Magnitude Ordering" begin
        # Test that all magnitude bounds are properly ordered
        for Bits in 4:8
            for SigBits in 2:(Bits-1)
                T = TestSignedFinite{Bits, SigBits}
                
                norm_min = magnitude_normal_min(T)
                norm_max = magnitude_normal_max(T)
                
                @test 0 < norm_min < norm_max
                
                if has_subnormals(T)
                    sub_min = magnitude_subnormal_min(T)
                    sub_max = magnitude_subnormal_max(T)
                    
                    @test sub_min !== nothing && sub_max !== nothing
                    if nmagnitudes_subnormal(T) > 1
                        @test 0 < sub_min < sub_max < norm_min < norm_max
                    else
                        @test 0 < sub_min <= sub_max < norm_min < norm_max
                    end
                end
            end
        end
    end
    
    @testset "Consistency with Other Functions" begin
        T = TestSignedFinite{7, 3}
        
        # Normal bounds should be consistent with exponent values
        @test magnitude_normal_min(T) ≈ exp_value_min(T)
        
        # Subnormal bounds should use subnormal exponent
        if has_subnormals(T)
            sub_min = magnitude_subnormal_min(T)
            expected_factor = exp_subnormal_value(T)
            first_prenormal = firstNonzeroPrenormalMagnitude(T)
            @test sub_min ≈ first_prenormal * expected_factor
        end
    end
    
    @testset "Type Stability" begin
        # Test that functions return appropriate floating-point types
        T = TestSignedFinite{8, 4}
        
        @test firstNonzeroPrenormalMagnitude(T) isa AbstractFloat
        @test lastPrenormalMagnitude(T) isa AbstractFloat
        @test magnitude_normal_min(T) isa AbstractFloat
        @test magnitude_normal_max(T) isa AbstractFloat
        
        if has_subnormals(T)
            sub_min = magnitude_subnormal_min(T)
            sub_max = magnitude_subnormal_max(T)
            @test sub_min isa AbstractFloat
            @test sub_max isa AbstractFloat
        end
    end
end

