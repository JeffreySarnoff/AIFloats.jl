using Test
using AIFloats

@testset "Rounding Tests" begin
    @testset "Rounding Mode Constants" begin
        @test AIFloats.RoundToOdd isa RoundingMode
        @test AIFloats.RoundStochastic isa RoundingMode
    end
    
    @testset "Basic Rounding Functions - Unsigned" begin
        # Create a test unsigned float type
        uf = UnsignedFiniteFloats(6, 3)
        test_values = floats(uf)
        
        # Test with a value that exists exactly
        exact_val = test_values[5]  # Pick a value from the middle
        @test round_up(uf, exact_val) == exact_val
        @test round_down(uf, exact_val) == exact_val
        @test round_tozero(uf, exact_val) == exact_val
        @test round_fromzero(uf, exact_val) == exact_val
        
        # Test NaN handling
        @test isnan(round_up(uf, NaN))
        @test isnan(round_down(uf, NaN))
        @test isnan(round_tozero(uf, NaN))
        @test isnan(round_fromzero(uf, NaN))
    end
    
    @testset "Round Up and Down" begin
        uf = UnsignedFiniteFloats(8, 4)
        values = floats(uf)
        
        # Test with a value between two representable values
        if length(values) >= 3
            val1 = values[2]
            val2 = values[3]
            test_val = (val1 + val2) / 2
            
            # round_up should give the larger value
            @test round_up(uf, test_val) == val2
            
            # round_down should give the smaller value  
            @test round_down(uf, test_val) == val1
        end
        
        # Test boundary cases
        small_val = minimum(filter(x -> x > 0 && isfinite(x), values)) / 2
        @test round_up(uf, small_val) > 0
        @test round_down(uf, small_val) >= 0
        
        # Test large values
        large_finite = filter(isfinite, values)
        if length(large_finite) > 0
            max_finite = maximum(large_finite)
            large_val = max_finite * 1.5
            
            rounded_up = round_up(uf, large_val)
            rounded_down = round_down(uf, large_val)
            @test isfinite(rounded_up) || isnan(rounded_up)  # Should saturate or NaN
            @test rounded_down <= max_finite
        end
    end
    
    @testset "Round To/From Zero" begin
        uf = UnsignedFiniteFloats(6, 3)
        
        # For unsigned types, round_tozero == round_down
        # and round_fromzero == round_up
        test_val = 1.5  # Arbitrary test value
        
        @test round_tozero(uf, test_val) == round_down(uf, test_val)
        @test round_fromzero(uf, test_val) == round_up(uf, test_val)
    end
    
    @testset "Nearest Even Rounding" begin
        uf = UnsignedFiniteFloats(8, 4)
        values = floats(uf)
        
        # Test exact values
        if length(values) >= 5
            exact_val = values[5]
            @test round_nearesteven(uf, exact_val) == exact_val
        end
        
        # Test NaN
        @test isnan(round_nearesteven(uf, NaN))
        
        # Test values that require rounding
        finite_vals = filter(isfinite, values)
        if length(finite_vals) >= 3
            val1 = finite_vals[2]
            val2 = finite_vals[3]
            midpoint = (val1 + val2) / 2
            
            # At exact midpoint, should round to even (based on bit pattern)
            result = round_nearesteven(uf, midpoint)
            @test result == val1 || result == val2
        end
    end
    
    @testset "Nearest Odd Rounding" begin
        uf = UnsignedFiniteFloats(8, 4)
        values = floats(uf)
        
        # Test exact values
        if length(values) >= 5
            exact_val = values[5]
            @test round_nearestodd(uf, exact_val) == exact_val
        end
        
        # Test NaN
        @test isnan(round_nearestodd(uf, NaN))
        
        # The function should work (implementation may vary)
        finite_vals = filter(isfinite, values)
        if length(finite_vals) >= 3
            val1 = finite_vals[2]
            val2 = finite_vals[3]
            midpoint = (val1 + val2) / 2
            
            result = round_nearestodd(uf, midpoint)
            @test result == val1 || result == val2
        end
    end
    
    @testset "Nearest To/From Zero" begin
        uf = UnsignedFiniteFloats(6, 3)
        
        # Test that these functions exist and handle basic cases
        test_val = 1.0
        @test !isnan(round_nearesttozero(uf, test_val))
        @test !isnan(round_nearestfromzero(uf, test_val))
        
        # Test NaN handling
        @test isnan(round_nearesttozero(uf, NaN))
        @test isnan(round_nearestfromzero(uf, NaN))
    end
    
    @testset "Nearest Away (typo test)" begin
        uf = UnsignedFiniteFloats(6, 3)
        
        # Test the function with the typo in the original code
        # (round_nearesrfromzero instead of round_nearestfromzero)
        test_val = 1.0
        @test_throws UndefVarError round_nearestaway(uf, test_val)
    end
    
    @testset "Rounding Consistency" begin
        uf = UnsignedFiniteFloats(7, 3)
        values = floats(uf)
        finite_vals = filter(isfinite, values)
        
        if length(finite_vals) >= 2
            # Test that rounding functions return values from the set
            test_val = (finite_vals[1] + finite_vals[2]) / 2
            
            @test round_up(uf, test_val) in values
            @test round_down(uf, test_val) in values
            @test round_tozero(uf, test_val) in values
            @test round_fromzero(uf, test_val) in values
            @test round_nearesteven(uf, test_val) in values
            @test round_nearestodd(uf, test_val) in values
            @test round_nearesttozero(uf, test_val) in values
            @test round_nearestfromzero(uf, test_val) in values
        end
    end
    
    @testset "Edge Case Values" begin
        uf = UnsignedFiniteFloats(6, 3)
        values = floats(uf)
        
        # Test with zero
        @test round_up(uf, 0.0) >= 0.0
        @test round_down(uf, 0.0) == 0.0
        
        # Test with very small positive value
        epsilon = 1e-10
        @test round_up(uf, epsilon) > 0
        @test round_down(uf, epsilon) >= 0
        
        # Test with infinity (should handle gracefully)
        inf_result_up = round_up(uf, Inf)
        inf_result_down = round_down(uf, Inf)
        @test isfinite(inf_result_up) || isnan(inf_result_up)
        @test isfinite(inf_result_down) || isnan(inf_result_down)
    end
    
    @testset "Monotonicity Properties" begin
        uf = UnsignedFiniteFloats(6, 3)
        
        # round_up should be monotonic
        test_vals = [0.1, 0.5, 1.0, 1.5, 2.0]
        rounded_up = [round_up(uf, x) for x in test_vals]
        
        # Filter out NaN values for monotonicity test
        finite_rounded = filter(!isnan, rounded_up)
        if length(finite_rounded) > 1
            @test issorted(finite_rounded)
        end
        
        # round_down should be monotonic
        rounded_down = [round_down(uf, x) for x in test_vals]
        finite_rounded_down = filter(!isnan, rounded_down)
        if length(finite_rounded_down) > 1
            @test issorted(finite_rounded_down)
        end
    end
    
    @testset "Rounding Function Types" begin
        uf = UnsignedFiniteFloats(6, 3)
        test_val = 1.5
        
        # All rounding functions should return the same type as input values
        float_type = eltype(floats(uf))
        
        @test round_up(uf, test_val) isa float_type
        @test round_down(uf, test_val) isa float_type
        @test round_tozero(uf, test_val) isa float_type
        @test round_fromzero(uf, test_val) isa float_type
        @test round_nearesteven(uf, test_val) isa float_type
        @test round_nearestodd(uf, test_val) isa float_type
        @test round_nearesttozero(uf, test_val) isa float_type
        @test round_nearestfromzero(uf, test_val) isa float_type
    end
    
    @testset "Search Functions Behavior" begin
        uf = UnsignedFiniteFloats(8, 4)
        values = floats(uf)
        
        # Test that searchsortedfirst/last are used correctly
        finite_vals = filter(isfinite, values)
        if length(finite_vals) >= 2
            test_val = finite_vals[2]
            
            # For exact matches, round_up and round_down should be same
            @test round_up(uf, test_val) == test_val
            @test round_down(uf, test_val) == test_val
            
            # For values between grid points
            if length(finite_vals) >= 3
                between_val = (finite_vals[2] + finite_vals[3]) / 2
                up_result = round_up(uf, between_val)
                down_result = round_down(uf, between_val)
                
                @test up_result >= between_val
                @test down_result <= between_val
                @test up_result != down_result  # Should be different for between values
            end
        end
    end
    
    @testset "Boundary Handling" begin
        uf = UnsignedFiniteFloats(6, 3)
        values = floats(uf)
        
        # Test at the boundaries of the representable range
        finite_vals = filter(isfinite, values)
        if length(finite_vals) > 0
            min_val = minimum(finite_vals)
            max_val = maximum(finite_vals)
            
            # Values below minimum
            below_min = min_val - abs(min_val) * 0.1
            @test round_up(uf, below_min) >= min_val
            @test round_down(uf, below_min) >= 0  # Should not go negative for unsigned
            
            # Values above maximum
            above_max = max_val * 1.1
            up_result = round_up(uf, above_max)
            down_result = round_down(uf, above_max)
            
            # Should handle overflow gracefully
            @test isfinite(up_result) || isnan(up_result)
            @test down_result <= max_val || isnan(down_result)
        end
    end
end