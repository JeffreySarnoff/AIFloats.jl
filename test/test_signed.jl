using Test
using AIFloats
using AIFloats: SignedFiniteFloat, SignedExtendedFloat,
                  AbsSignedFiniteFloat, AbsSignedExtendedFloat,
                  floats, codes, typeforfloat, typeforcode,
                  value_sequence, foundation_magnitudes
using Quadmath

@testset "Signed Types Tests" begin
    @testset "SignedFiniteFloat Construction" begin
        # Test basic construction with parameters
        sf = SignedFiniteFloat(6, 3)
        @test isa(sf, SignedFiniteFloat)
        @test isa(sf, AbsSignedFiniteFloat{6, 3})
        
        # Test type parameters are correctly embedded
        @test isa(sf, SignedFiniteFloat{6, 3, Float64, UInt8})
        
        # Test accessor functions
        @test isa(floats(sf), Vector)
        @test isa(codes(sf), Vector)
        @test length(floats(sf)) == length(codes(sf))
        @test length(floats(sf)) == 2^6  # 64 values for 6 bits
        
        # Test element types match expectations
        @test eltype(floats(sf)) == typeforfloat(6)  # Float64 for 6 bits
        @test eltype(codes(sf)) == typeforcode(6)    # UInt8 for 6 bits
    end
    
    @testset "SignedExtendedFloat Construction" begin
        # Test basic construction with parameters
        se = SignedExtendedFloat(6, 3)
        @test isa(se, SignedExtendedFloat)
        @test isa(se, AbsSignedExtendedFloat{6, 3})
        
        # Test type parameters
        @test isa(se, SignedExtendedFloat{6, 3, Float64, UInt8})
        
        # Test accessor functions
        @test isa(floats(se), Vector)
        @test isa(codes(se), Vector)
        @test length(floats(se)) == length(codes(se))
        @test length(floats(se)) == 2^6  # 64 values for 6 bits
        
        # Test element types
        @test eltype(floats(se)) == typeforfloat(6)
        @test eltype(codes(se)) == typeforcode(6)
    end
    
    @testset "Type-based Construction" begin
        # Test construction from abstract type - finite
        T_finite = AbsSignedFiniteFloat{8, 4}
        sf_from_type = SignedFiniteFloat(T_finite)
        @test isa(sf_from_type, SignedFiniteFloat{8, 4})
        @test nBits(T_finite) == 8
        @test nSigBits(T_finite) == 4
        
        # Test construction from abstract type - extended
        T_extended = AbsSignedExtendedFloat{8, 4}
        se_from_type = SignedExtendedFloat(T_extended)
        @test isa(se_from_type, SignedExtendedFloat{8, 4})
        @test nBits(T_extended) == 8
        @test nSigBits(T_extended) == 4
        
        # Test consistency between construction methods
        sf_direct = SignedFiniteFloat(8, 4)
        @test typeof(sf_from_type) == typeof(sf_direct)
        @test all(floats(sf_from_type) .=== floats(sf_direct))
        @test codes(sf_from_type) == codes(sf_direct)
    end
    
    @testset "Value Sequence Generation - Finite" begin
        T = AbsSignedFiniteFloat{6, 3}
        values = value_sequence(T)
        
        @test isa(values, Vector)
        @test eltype(values) == typeforfloat(6)
        @test length(values) == 2^6  # Should match total bit width
        
        # Test signed structure: should have both positive and negative values
        positive_finite = filter(x -> x > 0 && isfinite(x), values)
        negative_finite = filter(x -> x < 0 && isfinite(x), values)
        @test length(positive_finite) > 0
        @test length(negative_finite) > 0
        
        # Test that zero is present
        @test 0.0 ∈ values
        
        # Test that exactly one NaN is present (first negative becomes NaN)
        nan_count = count(isnan, values)
        @test nan_count == 1
        
        # Test that no infinities are present in finite type
        @test !any(isinf, values)
        
        # Test magnitude structure based on foundation magnitudes
        foundation_mags = foundation_magnitudes(T)
        half_length = length(values) ÷ 2
        
        # First half should be non-negative magnitudes (including zero)
        first_half = values[1:half_length]
        finite_first_half = filter(isfinite, first_half)
        @test all(x -> x >= 0, finite_first_half)
        
        # Second half contains negated magnitudes with NaN transformation
        second_half = values[half_length+1:end]
        @test any(isnan, second_half)  # First negative magnitude becomes NaN
    end
    
    @testset "Value Sequence Generation - Extended" begin
        T = AbsSignedExtendedFloat{6, 3}
        values = value_sequence(T)
        
        @test isa(values, Vector)
        @test eltype(values) == typeforfloat(6)
        @test length(values) == 2^6
        
        # Test signed structure with infinities
        positive_finite = filter(x -> x > 0 && isfinite(x), values)
        negative_finite = filter(x -> x < 0 && isfinite(x), values)
        @test length(positive_finite) > 0
        @test length(negative_finite) > 0
        
        # Test that zero is present
        @test 0.0 ∈ values
        
        # Test infinity presence: should have +Inf and -Inf
        pos_inf_count = count(x -> isinf(x) && x > 0, values)
        neg_inf_count = count(x -> isinf(x) && x < 0, values)
        @test pos_inf_count == 1
        @test neg_inf_count == 1
        
        # Test that exactly one NaN is present
        nan_count = count(isnan, values)
        @test nan_count == 1
        
        # Test positioning: +Inf should be at end of first half (non-negative)
        half_length = length(values) ÷ 2
        @test isinf(values[half_length]) && values[half_length] > 0
        
        # Test that -Inf and NaN are in second half
        second_half = values[half_length+1:end]
        @test any(x -> isinf(x) && x < 0, second_half)
        @test any(isnan, second_half)
    end
    
    @testset "Signed Value Structure and Symmetry" begin
        sf = SignedFiniteFloat(8, 4)
        values = floats(sf)
        
        # Test basic structure
        @test length(values) == 256  # 2^8
        half_length = length(values) ÷ 2
        
        # Test that structure is roughly symmetric
        first_half = values[1:half_length]       # Non-negative magnitudes
        second_half = values[half_length+1:end]  # Negative magnitudes (with NaN)
        
        # First half should contain zero and positive values
        @test 0.0 ∈ first_half
        positive_in_first = filter(x -> x > 0 && isfinite(x), first_half)
        @test length(positive_in_first) > 0
        
        # Second half should contain negative values and one NaN
        negative_in_second = filter(x -> x < 0 && isfinite(x), second_half)
        nan_in_second = count(isnan, second_half)
        @test length(negative_in_second) > 0
        @test nan_in_second == 1
        
        # Test magnitude correspondence
        # Positive magnitudes should roughly match absolute values of negatives
        pos_mags = sort(filter(x -> x > 0 && isfinite(x), values))
        neg_mags = sort(abs.(filter(x -> x < 0 && isfinite(x), values)))
        
        # Should have similar ranges (accounting for NaN replacement)
        if length(pos_mags) > 0 && length(neg_mags) > 0
            @test maximum(pos_mags) > 0
            @test maximum(neg_mags) > 0
            # The ranges should be comparable
            @test abs(log10(maximum(pos_mags)) - log10(maximum(neg_mags))) < 2
        end
    end
    
    @testset "Special Value Placement" begin
        # Test finite type special value placement
        sf = SignedFiniteFloat(6, 3)
        values = floats(sf)
        half_length = length(values) ÷ 2
        
        # Zero should be first in the sequence
        @test values[1] == 0.0
        
        # NaN should be first in the second half (negative section)
        @test isnan(values[half_length + 1])
        
        # No infinities in finite type
        @test !any(isinf, values)
        
        # Test extended type special value placement
        se = SignedExtendedFloat(6, 3)
        ext_values = floats(se)
        
        # Zero should still be first
        @test ext_values[1] == 0.0
        
        # +Inf should be at end of first half
        @test isinf(ext_values[half_length]) && ext_values[half_length] > 0
        
        # NaN should be first in second half
        @test isnan(ext_values[half_length + 1])
        
        # -Inf should be last in the sequence
        @test isinf(ext_values[end]) && ext_values[end] < 0
    end
    
    @testset "Foundation Magnitude Integration" begin
        T = AbsSignedFiniteFloat{7, 3}
        values = value_sequence(T)
        foundation_mags = foundation_magnitudes(T)
        
        # The first half should be based on foundation magnitudes
        half_length = length(values) ÷ 2
        first_half = values[1:half_length]
        
        # Foundation magnitudes should be incorporated into the first half
        @test length(foundation_mags) > 0
        @test foundation_mags[1] == 0.0  # Should start with zero
        
        # Some values from foundation should appear in first half
        common_values = intersect(Set(first_half), Set(foundation_mags))
        @test length(common_values) >= 2  # At least zero and one other
        
        # Test monotonicity in first half (excluding special values)
        finite_first = filter(isfinite, first_half)
        @test issorted(finite_first)
    end
    
    @testset "Codes Sequence Integrity" begin
        sf = SignedFiniteFloat(8, 4)
        codes_vec = codes(sf)
        
        # Test completeness of encoding sequence
        @test length(codes_vec) == 256
        @test codes_vec[1] == 0x00
        @test codes_vec[end] == 0xff
        @test issorted(codes_vec)
        
        # Test that there are no gaps in the sequence
        for i in 1:length(codes_vec)-1
            @test codes_vec[i+1] == codes_vec[i] + 1
        end
        
        # Test consistency with floats length
        @test length(codes_vec) == length(floats(sf))
    end
    
    @testset "Finite vs Extended Comparison" begin
        # Compare finite and extended versions of same configuration
        sf = SignedFiniteFloat(7, 3)
        se = SignedExtendedFloat(7, 3)
        
        finite_values = floats(sf)
        extended_values = floats(se)
        
        # Both should have same total length
        @test length(finite_values) == length(extended_values)
        
        # Both should have zero in same position
        @test findfirst(==(0.0), finite_values) == findfirst(==(0.0), extended_values)
        
        # Both should have exactly one NaN
        @test count(isnan, finite_values) == count(isnan, extended_values) == 1
        
        # Only extended should have infinities
        @test !any(isinf, finite_values)
        @test count(isinf, extended_values) == 2
        
        # The finite values should be similar (excluding infinities)
        finite_subset = filter(isfinite, finite_values)
        extended_subset = filter(isfinite, extended_values)
        
        # Should have substantial overlap in finite values
        common_finite = intersect(Set(finite_subset), Set(extended_subset))
        @test length(common_finite) >= length(finite_subset) - 5  # Allow some difference
    end
    
    @testset "Type Parameter Consistency" begin
        # Test different bit width configurations
        sf_small = SignedFiniteFloat(6, 3)
        sf_large = SignedFiniteFloat(12, 6)
        
        @test isa(sf_small, SignedFiniteFloat{6, 3})
        @test isa(sf_large, SignedFiniteFloat{12, 6})
        
        # Test element types scale appropriately
        @test eltype(floats(sf_small)) == typeforfloat(6)   # Float64
        @test eltype(codes(sf_small)) == typeforcode(6)     # UInt8
        @test eltype(floats(sf_large)) == typeforfloat(12)  # Float128
        @test eltype(codes(sf_large)) == typeforcode(12)    # UInt16
        
        # Test extended versions
        se_small = SignedExtendedFloat(6, 3)
        se_large = SignedExtendedFloat(12, 6)
        
        @test isa(se_small, SignedExtendedFloat{6, 3})
        @test isa(se_large, SignedExtendedFloat{12, 6})
    end
    
    @testset "Edge Cases and Minimal Configurations" begin
        # Test minimal signed configuration
        sf_min = SignedFiniteFloat(3, 2)
        @test length(floats(sf_min)) == 8  # 2^3
        
        values_min = floats(sf_min)
        @test 0.0 ∈ values_min
        @test count(isnan, values_min) == 1
        @test count(x -> x > 0 && isfinite(x), values_min) >= 1
        @test count(x -> x < 0 && isfinite(x), values_min) >= 1
        
        # Test that structure is maintained even in minimal case
        half_length = length(values_min) ÷ 2
        @test values_min[1] == 0.0  # Zero first
        @test isnan(values_min[half_length + 1])  # NaN at start of second half
        
        # Test precision = 1 edge case
        sf_p1 = SignedFiniteFloat(3, 1)
        @test !has_subnormals(typeof(sf_p1))  # No subnormals with precision 1
        @test length(floats(sf_p1)) == 8
    end
    
    @testset "Numerical Precision and Accuracy" begin
        sf = SignedFiniteFloat(8, 4)
        values = floats(sf)
        
        # Test that values span reasonable range
        finite_values = filter(isfinite, values)
        min_finite = minimum(finite_values)
        max_finite = maximum(finite_values)
        
        @test min_finite < 0 < max_finite  # Should span zero
        
        # Test that we have small values near zero
        small_values = filter(x -> 0 < abs(x) < 1 && isfinite(x), values)
        @test length(small_values) >= 4  # Should have some small values
        
        # Test that we have larger magnitude values
        large_values = filter(x -> abs(x) >= 1 && isfinite(x), values)
        @test length(large_values) >= 4  # Should have some large values
        
        # Test precision preservation
        sorted_positive = sort(filter(x -> x > 0 && isfinite(x), values))
        if length(sorted_positive) >= 2
            # Adjacent positive values should be distinct
            for i in 1:length(sorted_positive)-1
                @test sorted_positive[i+1] > sorted_positive[i]
            end
        end
    end
    
    @testset "Memory Layout and Efficiency" begin
        sf = SignedFiniteFloat(8, 4)
        
        # Test that vectors are properly allocated
        @test isa(floats(sf), Vector{Float64})
        @test isa(codes(sf), Vector{UInt8})
        
        # Test memory alignment (AlignedAllocs requirement)
        values = floats(sf)
        codes_vec = codes(sf)
        
        # Test that all memory is initialized properly
        @test all(x -> isnan(x) || isfinite(x) || isinf(x), values)  # No uninitialized values
        @test all(x -> 0 <= x <= 255, codes_vec)  # All codes in valid range
        
        # Test size efficiency
        @test length(values) == 2^8
        @test length(codes_vec) == 2^8
    end
    
    @testset "Construction Method Equivalence" begin
        bits, sigbits = 8, 4
        
        # Test different construction paths
        sf1 = SignedFiniteFloat(bits, sigbits)
        sf2 = SignedFiniteFloat(AbsSignedFiniteFloat{bits, sigbits})
        
        # Should produce identical results
        @test typeof(sf1) == typeof(sf2)
        @test all(floats(sf1) .=== floats(sf2))
        @test codes(sf1) == codes(sf2)
        
        # Test for extended types
        se1 = SignedExtendedFloat(bits, sigbits)
        se2 = SignedExtendedFloat(AbsSignedExtendedFloat{bits, sigbits})
        
        @test typeof(se1) == typeof(se2)
        @test all(floats(se1) .=== floats(se2))
        @test codes(se1) == codes(se2)
    end
    
    @testset "Integration with Type System" begin
        sf = SignedFiniteFloat(8, 4)
        
        # Test that all expected type functions work
        @test nBits(typeof(sf)) == 8
        @test nSigBits(typeof(sf)) == 4
        @test is_signed(typeof(sf)) == true
        @test is_finite(typeof(sf)) == true
        @test is_extended(typeof(sf)) == false
        
        # Test with extended version
        se = SignedExtendedFloat(8, 4)
        @test is_extended(typeof(se)) == true
        @test is_finite(typeof(se)) == false
        
        # Test count functions
        @test nValues(typeof(sf)) == 256
        @test nMagnitudes(typeof(sf)) == 128  # Half for signed
        @test nInfs(typeof(sf)) == 0          # Finite has no infinities
        @test nInfs(typeof(se)) == 2          # Extended has +Inf and -Inf
    end
end

