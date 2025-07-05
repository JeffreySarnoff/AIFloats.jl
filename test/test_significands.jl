using Test
using AIFloats
using AIFloats: AbsSignedFiniteFloat, AbsUnsignedFiniteFloat,
                  prenormal_magnitude_steps, normal_magnitude_steps,
                  significand_magnitudes, nPrenormalMagnitudes,
                  firstNonzeroPrenormalMagnitude, lastPrenormalMagnitude

@testset "Significands Tests" begin
    @testset "Prenormal Magnitude Steps" begin
        T = TestSignedFinite{8, 4}
        
        steps = prenormal_magnitude_steps(T)
        @test isa(steps, AbstractVector)
        @test length(steps) == nPrenormalMagnitudes(T)
        
        # Should start at 0 and end just before 1
        @test steps[1] == 0.0
        @test steps[end] < 1.0
        
        # Should be evenly spaced
        expected_step = 1.0 / nPrenormalMagnitudes(T)
        for i in 1:length(steps)
            @test steps[i] ≈ (i-1) * expected_step
        end
        
        # Test with different configurations
        T2 = TestUnsignedFinite{6, 3}
        steps2 = prenormal_magnitude_steps(T2)
        @test length(steps2) == nPrenormalMagnitudes(T2)
        @test steps2[1] == 0.0
        @test steps2[end] == (nPrenormalMagnitudes(T2) - 1) / nPrenormalMagnitudes(T2)
    end
    
    @testset "Normal Magnitude Steps" begin
        T = TestSignedFinite{8, 4}
        
        steps = normal_magnitude_steps(T)
        @test isa(steps, AbstractVector)
        
        nprenormals = nPrenormalMagnitudes(T)
        @test length(steps) == nprenormals
        
        # Should start at 1 and go to just before 2
        @test steps[1] ≈ 1.0
        @test steps[end] < 2.0
        
        # Should be evenly spaced starting from nprenormals/nprenormals = 1
        expected_step = 1.0 / nprenormals
        for i in 1:length(steps)
            expected_val = (nprenormals + i - 1) / nprenormals
            @test steps[i] ≈ expected_val
        end
    end
    
    @testset "Significand Magnitudes" begin
        T = TestSignedFinite{6, 3}
        
        magnitudes = significand_magnitudes(T)
        @test isa(magnitudes, Vector)
        @test length(magnitudes) > 0
        
        # Should start with prenormal steps
        prenormals = prenormal_magnitude_steps(T)
        @test magnitudes[1:length(prenormals)] ≈ prenormals
        
        # First value should be 0, but subsequent should be positive
        @test magnitudes[1] == 0.0
        @test all(x -> x > 0, magnitudes[2:end])
    end
    
    @testset "Significand Structure" begin
        # Test different bit/sigbit combinations
        for Bits in 4:7
            for SigBits in 2:(Bits-1)
                T = TestSignedFinite{Bits, SigBits}
                
                prenormals = prenormal_magnitude_steps(T)
                normals = normal_magnitude_steps(T)
                magnitudes = significand_magnitudes(T)
                
                # Basic structure tests
                @test length(prenormals) == nPrenormalMagnitudes(T)
                @test length(normals) == nPrenormalMagnitudes(T)
                @test length(magnitudes) >= length(prenormals)
                
                # Range tests
                @test 0.0 <= minimum(prenormals) < maximum(prenormals) < 1.0
                @test 1.0 <= minimum(normals) < maximum(normals) < 2.0
                
                # Continuity test
                @test prenormals[end] < normals[1]
            end
        end
    end
    
    @testset "Magnitude Precision" begin
        T = TestSignedFinite{8, 4}
        
        prenormals = prenormal_magnitude_steps(T)
        normals = normal_magnitude_steps(T)
        
        # Test that steps have the correct precision
        nprenormals = nPrenormalMagnitudes(T)
        
        # Prenormal step size
        prenormal_step = 1.0 / nprenormals
        for i in 2:length(prenormals)
            @test prenormals[i] - prenormals[i-1] ≈ prenormal_step
        end
        
        # Normal step size (same as prenormal)
        normal_step = 1.0 / nprenormals  
        for i in 2:length(normals)
            @test normals[i] - normals[i-1] ≈ normal_step
        end
    end
    
    @testset "Instance vs Type Functions" begin
        # Test that significand functions work on both types and instances
        test_type = TestSignedFinite{8, 4}
        test_instance = test_type()
        
        @test significand_magnitudes(test_type) == significand_magnitudes(test_instance)
        @test prenormal_magnitude_steps(test_type) == prenormal_magnitude_steps(test_instance)
        @test normal_magnitude_steps(test_type) == normal_magnitude_steps(test_instance)
    end
    
    @testset "Edge Cases" begin
        # Test minimal precision
        T_min = TestSignedFinite{3, 2}
        
        prenormals = prenormal_magnitude_steps(T_min)
        normals = normal_magnitude_steps(T_min)
        
        @test length(prenormals) == 2  # 2^(2-1) = 2
        @test length(normals) == 2
        @test prenormals == [0.0, 0.5]
        @test normals ≈ [1.0, 1.5]
        
        magnitudes = significand_magnitudes(T_min)
        @test length(magnitudes) >= 2
        @test magnitudes[1] == 0.0
        @test magnitudes[2] == 0.5
    end
    
    @testset "Type Consistency" begin
        # Test that signed and unsigned types produce similar significand patterns
        TS = TestSignedFinite{8, 4}
        TU = TestUnsignedFinite{8, 4}
        
        prenormals_s = prenormal_magnitude_steps(TS)
        prenormals_u = prenormal_magnitude_steps(TU)
        @test prenormals_s ≈ prenormals_u
        
        normals_s = normal_magnitude_steps(TS)
        normals_u = normal_magnitude_steps(TU)
        @test normals_s ≈ normals_u
    end
    
    @testset "Mathematical Properties" begin
        T = TestSignedFinite{7, 3}
        
        magnitudes = significand_magnitudes(T)
        
        # Test that all values are in reasonable range
        @test all(x -> 0.0 <= x < 2.0, magnitudes)
        
        # Test specific boundary values
        @test 0.0 in magnitudes
        @test any(x -> x ≈ 1.0, magnitudes)
    end
end

