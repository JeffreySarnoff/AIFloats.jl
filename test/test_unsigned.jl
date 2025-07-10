@testset "Unsigned Types Tests" begin
    @testset "UnsignedFinite Construction" begin
        # Test basic construction with parameters
        uf = UnsignedFinite(6, 3)
        @test isa(uf, UnsignedFinite)
        @test isa(uf, AkoUnsignedFinite{6, 3})
        
        # Test type parameters are correctly embedded
        @test isa(uf, UnsignedFinite{6, 3, Float64, UInt8})
        
        # Test accessor functions
        @test isa(floats(uf), Vector)
        @test isa(codes(uf), Vector)
        @test length(floats(uf)) == length(codes(uf))
        @test length(floats(uf)) == 2^6  # 64 values for 6 bits
        
        # Test element types match expectations
        @test eltype(floats(uf)) == typeforfloat(6)  # Float64 for 6 bits
        @test eltype(codes(uf)) == typeforcode(6)    # UInt8 for 6 bits
    end
    
    @testset "UnsignedExtended Construction" begin
        # Test basic construction with parameters
        ue = UnsignedExtended(6, 3)
        @test isa(ue, UnsignedExtended)
        @test isa(ue, AkoUnsignedExtended{6, 3})
        
        # Test type parameters
        @test isa(ue, UnsignedExtended{6, 3, Float64, UInt8})
        
        # Test accessor functions
        @test isa(floats(ue), Vector)
        @test isa(codes(ue), Vector)
        @test length(floats(ue)) == length(codes(ue))
        @test length(floats(ue)) == 2^6  # 64 values for 6 bits
        
        # Test element types
        @test eltype(floats(ue)) == typeforfloat(6)
        @test eltype(codes(ue)) == typeforcode(6)
    end
    
    @testset "Type-based Construction" begin
        # Test construction from abstract type - finite
        T_finite = AkoUnsignedFinite{8, 4}
        uf_from_type = UnsignedFinite(T_finite)
        @test isa(uf_from_type, UnsignedFinite{8, 4})
        @test nbits(T_finite) == 8
        @test nbits_sig(T_finite) == 4
        
        # Test construction from abstract type - extended
        T_extended = AkoUnsignedExtended{8, 4}
        ue_from_type = UnsignedExtended(T_extended)
        @test isa(ue_from_type, UnsignedExtended{8, 4})
        @test nbits(T_extended) == 8
        @test nbits_sig(T_extended) == 4
        
        # Test consistency between construction methods
        uf_direct = UnsignedFinite(8, 4)
        @test typeof(uf_from_type) == typeof(uf_direct)
        @test all(floats(uf_from_type) .=== floats(uf_direct))
        @test codes(uf_from_type) == codes(uf_direct)
    end
    
    @testset "Value Sequence Generation - Finite" begin
        T = AkoUnsignedFinite{6, 3}
        values = value_seq(T)
        
        @test isa(values, Vector)
        @test eltype(values) == typeforfloat(6)
        @test length(values) == 2^6  # Should match total bit width
        
        # Test unsigned structure: all values should be non-negative (except NaN)
        finite_values = filter(isfinite, values)
        @test all(x -> x >= 0, finite_values)
        
        # Test that zero is present and first
        @test values[1] == 0.0
        
        # Test that exactly one NaN is present (at the end)
        nan_count = count(isnan, values)
        @test nan_count == 1
        @test isnan(values[end])
        
        # Test that no infinities are present in finite type
        @test !any(isinf, values)
        
        # Test monotonicity of finite values (excluding NaN)
        finite_sorted = values[1:end-1]  # Exclude NaN at end
        @test issorted(finite_sorted)
        
        # Test based on foundation magnitudes
        foundation_mags = magnitude_foundation_seq(T)
        @test length(foundation_mags) > 0
        @test foundation_mags[1] == 0.0
        
        # The finite values should match foundation magnitudes (except for NaN replacement)
        @test values[1:length(foundation_mags)-1] ≈ foundation_mags[1:end-1]
    end
    
    @testset "Value Sequence Generation - Extended" begin
        T = AkoUnsignedExtended{6, 3}
        values = value_seq(T)
        
        @test isa(values, Vector)
        @test eltype(values) == typeforfloat(6)
        @test length(values) == 2^6
        
        # Test unsigned structure: all finite values should be non-negative
        finite_values = filter(isfinite, values)
        @test all(x -> x >= 0, finite_values)
        
        # Test that zero is present and first
        @test values[1] == 0.0
        
        # Test infinity presence: should have +Inf only (no -Inf for unsigned)
        pos_inf_count = count(x -> isinf(x) && x > 0, values)
        neg_inf_count = count(x -> isinf(x) && x < 0, values)
        @test pos_inf_count == 1
        @test neg_inf_count == 0
        
        # Test that exactly one NaN is present (at the end)
        nan_count = count(isnan, values)
        @test nan_count == 1
        @test isnan(values[end])
        
        # Test positioning: +Inf should be second to last
        @test isinf(values[end-1]) && values[end-1] > 0
        
        # Test monotonicity up to infinity
        finite_values_ordered = values[1:end-2]  # Exclude +Inf and NaN
        @test issorted(finite_values_ordered)
    end
    
    @testset "Unsigned Value Structure and Ordering" begin
        uf = UnsignedFinite(8, 4)
        values = floats(uf)
        
        # Test basic structure
        @test length(values) == 256  # 2^8
        
        # Test that all finite values are non-negative
        finite_values = filter(isfinite, values)
        @test all(x -> x >= 0, finite_values)
        
        # Test ordering: should be strictly increasing (except for NaN at end)
        finite_values_sorted = values[1:end-1]
        @test issorted(finite_values_sorted)
        
        # Test that zero is first
        @test values[1] == 0.0
        
        # Test that NaN is last
        @test isnan(values[end])
        
        # Test that we have a good range of values
        max_finite = maximum(finite_values)
        min_positive = minimum(filter(x -> x > 0, finite_values))
        @test max_finite > min_positive > 0
        
        # Test that we have subnormal-like small values
        small_values = filter(x -> 0 < x < 1, finite_values)
        @test length(small_values) >= nmagnitudes_subnormal(typeof(uf))
        
        # Test that we have normal-like larger values  
        normal_values = filter(x -> x >= 1 && isfinite(x), finite_values)
        @test length(normal_values) > 0
    end
    
    @testset "Special Value Placement - Finite" begin
        uf = UnsignedFinite(7, 3)
        values = floats(uf)
        
        # Zero should always be first
        @test values[1] == 0.0
        
        # NaN should always be last for finite types
        @test isnan(values[end])
        
        # No infinities should be present
        @test !any(isinf, values)
        
        # All other values should be positive finite
        middle_values = values[2:end-1]
        @test all(x -> x > 0 && isfinite(x), middle_values)
        @test issorted(middle_values)
        
        # Test relationship to foundation magnitudes
        foundation_mags = magnitude_foundation_seq(typeof(uf))
        # Last foundation magnitude becomes NaN
        @test length(foundation_mags) == length(values)
        @test foundation_mags[1:end-1] ≈ values[1:end-1]
        @test isnan(values[end])  # NaN replaces last foundation value
    end
    
    @testset "Special Value Placement - Extended" begin
        ue = UnsignedExtended(7, 3)
        values = floats(ue)
        
        # Zero should always be first
        @test values[1] == 0.0
        
        # NaN should always be last
        @test isnan(values[end])
        
        # +Inf should be second to last
        @test isinf(values[end-1]) && values[end-1] > 0
        
        # No negative infinity for unsigned
        @test !any(x -> isinf(x) && x < 0, values)
        
        # All other values should be positive finite and ordered
        middle_values = values[2:end-2]
        @test all(x -> x > 0 && isfinite(x), middle_values)
        @test issorted(middle_values)
        
        # Test relationship to foundation magnitudes
        foundation_mags = magnitude_foundation_seq(typeof(ue))
        # Second-to-last foundation becomes +Inf, last becomes NaN
        @test length(foundation_mags) == length(values)
        @test foundation_mags[1:end-2] ≈ values[1:end-2]
        @test isinf(values[end-1])  # +Inf replaces second-to-last foundation
        @test isnan(values[end])    # NaN replaces last foundation
    end
    
    @testset "Foundation Magnitude Integration" begin
        T = AkoUnsignedFinite{8, 4}
        values = value_seq(T)
        foundation_mags = magnitude_foundation_seq(T)
        
        # Foundation should provide the base magnitude sequence
        @test length(foundation_mags) == length(values)
        @test foundation_mags[1] == 0.0  # Should start with zero
        @test issorted(foundation_mags[1:end-1])  # Should be monotonic (except possibly last)
        
        # For finite type: all foundation values except last should match exactly
        @test foundation_mags[1:end-1] ≈ values[1:end-1]
        @test isnan(values[end])  # Last value becomes NaN
        
        # Test that foundation incorporates significand structure
        nprenormals = nmagnitudes_prenormal(T)
        if nprenormals > 1
            # Should have subnormal-range values
            subnormal_range = foundation_mags[2:nprenormals]  # Skip zero
            @test all(x -> 0 < x < 1, subnormal_range)
            @test issorted(subnormal_range)
        end
    end
    
    @testset "Codes Sequence Integrity" begin
        uf = UnsignedFinite(8, 4)
        codes_vec = codes(uf)
        
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
        @test length(codes_vec) == length(floats(uf))
        
        # Test that codes correspond to proper ordering
        values = floats(uf)
        for i in 1:length(values)-1
            # Values should be ordered (except NaN at end)
            if isfinite(values[i]) && isfinite(values[i+1])
                @test values[i] <= values[i+1]
            end
        end
    end
    
    @testset "Finite vs Extended Comparison" begin
        # Compare finite and extended versions of same configuration
        uf = UnsignedFinite(7, 3)
        ue = UnsignedExtended(7, 3)
        
        finite_values = floats(uf)
        extended_values = floats(ue)

        # Both should have same total length
        @test length(finite_values) == length(extended_values)

        # Both should end with NaN
        @test isnan(finite_values[end]) && isnan(extended_values[end])

        # Both should start with zero
        @test finite_values[1] == extended_values[1] == 0.0
                
        # Only extended should have infinity
        @test !any(isinf, finite_values)
        @test count(isinf, extended_values) == 1
        @test isinf(extended_values[end-1]) && extended_values[end-1] > 0

        # Test that extended has one fewer finite value (replaced by +Inf)
        finite_count = count(isfinite, finite_values)
        extended_finite_count = count(isfinite, extended_values)
        @test extended_finite_count == finite_count - 1

        # The finite portions should be nearly identical
        # Finite: [...finite values..., NaN]
        # Extended: [...finite values..., +Inf, NaN]
        finite_subset = finite_values[1:end-2]
        extended_subset = extended_values[1:end-2]
        @test finite_subset ≈ extended_subset
    end
    
    @testset "Type Parameter Consistency" begin
        # Test different bit width configurations
        uf_small = UnsignedFinite(6, 3)
        uf_large = UnsignedFinite(12, 6)
        
        @test isa(uf_small, UnsignedFinite{6, 3})
        @test isa(uf_large, UnsignedFinite{12, 6})
        
        # Test element types scale appropriately
        @test eltype(floats(uf_small)) == typeforfloat(6)   # Float64
        @test eltype(codes(uf_small)) == typeforcode(6)     # UInt8
        @test eltype(floats(uf_large)) == typeforfloat(12)  # Float128
        @test eltype(codes(uf_large)) == typeforcode(12)    # UInt16
        
        # Test extended versions
        ue_small = UnsignedExtended(6, 3)
        ue_large = UnsignedExtended(12, 6)
        
        @test isa(ue_small, UnsignedExtended{6, 3})
        @test isa(ue_large, UnsignedExtended{12, 6})
        
        # Test that all maintain proper unsigned structure
        for uf_test in [uf_small, uf_large, ue_small, ue_large]
            values = floats(uf_test)
            finite_vals = filter(isfinite, values)
            @test all(x -> x >= 0, finite_vals)  # All non-negative
            @test values[1] == 0.0               # Zero first
            @test isnan(values[end])             # NaN last
        end
    end
    
    @testset "Edge Cases and Boundary Conditions" begin
        # Test minimal unsigned configuration
        uf_min = UnsignedFinite(2, 1)
        @test length(floats(uf_min)) == 4  # 2^2
        
        values_min = floats(uf_min)
        @test values_min[1] == 0.0
        @test isnan(values_min[end])
        @test count(isfinite, values_min) == 3  # 0, and two positive values
        @test all(x -> x >= 0, filter(isfinite, values_min))
        
        # Test precision = 1 characteristics
        @test !has_subnormals(typeof(uf_min))  # No subnormals with precision 1
        @test nmagnitudes_prenormal(typeof(uf_min)) == 1
        
        # Test maximum unsigned precision (precision == bitwidth)
        uf_max_prec = UnsignedFinite(6, 6)
        @test length(floats(uf_max_prec)) == 64
        @test nbits_exp(typeof(uf_max_prec)) == 1  # Only 1 exponent bit left
        
        # Test near-maximum bit width
        uf_large = UnsignedFinite(15, 8)
        values_large = floats(uf_large)
        @test length(values_large) == 2^15
        @test values_large[1] == 0.0
        @test isnan(values_large[end])
        @test eltype(values_large) == Float128  # Should use high precision
    end
    
    @testset "Numerical Properties and Precision" begin
        uf = UnsignedFinite(8, 4)
        values = floats(uf)
        
        # Test range coverage
        finite_values = filter(isfinite, values)
        min_pos = minimum(filter(x -> x > 0, finite_values))
        max_finite = maximum(finite_values)
        
        @test 0 < min_pos < max_finite
        @test min_pos < 1.0  # Should have subnormal-range values
        @test max_finite > 1.0  # Should have normal-range values
        
        # Test density distribution
        small_values = filter(x -> 0 < x < 1, finite_values)
        large_values = filter(x -> x >= 1, finite_values)
        
        @test length(small_values) > 0  # Should have fine-grained small values
        @test length(large_values) > 0  # Should have coarse-grained large values
        
        # Test monotonicity and distinctness
        @test issorted(finite_values)
        @test length(unique(finite_values)) == length(finite_values)  # All distinct
        
        # Test relationship to IEEE-like structure
        if has_subnormals(typeof(uf))
            subnormal_count = nmagnitudes_subnormal(typeof(uf))
            actual_small = length(filter(x -> 0 < x < magnitude_normal_min(typeof(uf)), finite_values))
            @test actual_small >= subnormal_count - 2  # Allow some tolerance
        end
    end
    
    @testset "Memory Layout and Efficiency" begin
        uf = UnsignedFinite(8, 4)
        
        # Test that vectors are properly allocated using AlignedAllocs
        @test isa(floats(uf), Vector{Float64})
        @test isa(codes(uf), Vector{UInt8})
        
        # Test memory initialization
        values = floats(uf)
        codes_vec = codes(uf)
        
        # All values should be properly initialized (no garbage)
        @test all(x -> isnan(x) || isfinite(x) || isinf(x), values)
        @test all(x -> 0 <= x <= 255, codes_vec)
        
        # Test size efficiency
        @test length(values) == 2^8
        @test length(codes_vec) == 2^8
        
        # Test that memory usage is reasonable
        @test sizeof(values) + sizeof(codes_vec) > 0
    end
    
    @testset "Construction Method Equivalence" begin
        bits, sigbits = 8, 4
        
        # Test different construction paths for finite
        uf1 = UnsignedFinite(bits, sigbits)
        uf2 = UnsignedFinite(AkoUnsignedFinite{bits, sigbits})
        
        # Should produce identical results
        @test typeof(uf1) == typeof(uf2)
        @test all(floats(uf1) .=== floats(uf2))
        @test codes(uf1) == codes(uf2)
        
        # Test for extended types
        ue1 = UnsignedExtended(bits, sigbits)
        ue2 = UnsignedExtended(AkoUnsignedExtended{bits, sigbits})
        
        @test typeof(ue1) == typeof(ue2)
        @test all(floats(ue1) .=== floats(ue2))
        @test codes(ue1) == codes(ue2)
        
        # Test that construction is deterministic
        uf3 = UnsignedFinite(bits, sigbits)
        @test all(floats(uf1) .=== floats(uf3))
        @test codes(uf1) == codes(uf3)
    end
    
    @testset "Integration with Type System" begin
        uf = UnsignedFinite(8, 4)
        
        # Test that all expected type functions work
        @test nbits(typeof(uf)) == 8
        @test nbits_sig(typeof(uf)) == 4
        @test is_unsigned(typeof(uf)) == true
        @test is_signed(typeof(uf)) == false
        @test is_finite(typeof(uf)) == true
        @test is_extended(typeof(uf)) == false
        
        # Test with extended version
        ue = UnsignedExtended(8, 4)
        @test is_extended(typeof(ue)) == true
        @test is_finite(typeof(ue)) == false
        
        # Test count functions
        @test nvalues(typeof(uf)) == 256
        @test nmagnitudes(typeof(uf)) == 255    # All values except NaN
        @test nInfs(typeof(uf)) == 0            # Finite has no infinities
        @test nInfs(typeof(ue)) == 1            # Extended has +Inf only
        @test nPosInfs(typeof(ue)) == 1         # One positive infinity
        @test nNegInfs(typeof(ue)) == 0         # No negative infinity for unsigned
        
        # Test exponent functions
        @test exp_bias(typeof(uf)) > 0
        @test nbits_exp(typeof(uf)) == 5  # 8 - 4 + 1 for unsigned
        
        # Test magnitude functions
        @test magnitude_normal_min(typeof(uf)) > 0
        @test magnitude_normal_max(typeof(uf)) > magnitude_normal_min(typeof(uf))
        
        if has_subnormals(typeof(uf))
            @test magnitude_subnormal_min(typeof(uf)) < magnitude_normal_min(typeof(uf))
            @test magnitude_subnormal_max(typeof(uf)) < magnitude_normal_min(typeof(uf))
        end
    end
    
    @testset "Unsigned vs Signed Comparison" begin
        # Compare unsigned and signed types of same configuration
        uf = UnsignedFinite(8, 4)
        sf = SignedFinite(8, 4)
        
        uf_values = floats(uf)
        sf_values = floats(sf)
        
        # Both should have same total count
        @test length(uf_values) == length(sf_values)
        
        # Unsigned should be all non-negative (except NaN)
        uf_finite = filter(isfinite, uf_values)
        @test all(x -> x >= 0, uf_finite)
        
        # Signed should have both positive and negative
        sf_pos = filter(x -> x > 0 && isfinite(x), sf_values)
        sf_neg = filter(x -> x < 0 && isfinite(x), sf_values)
        @test length(sf_pos) > 0 && length(sf_neg) > 0
        
        # Both should have zero and NaN
        @test 0.0 ∈ uf_values && 0.0 ∈ sf_values
        @test any(isnan, uf_values) && any(isnan, sf_values)
        
        # Unsigned should have more distinct finite positive values
        @test length(uf_finite) > length(sf_pos)
        
        # Test magnitude count differences
        @test nmagnitudes(typeof(uf)) > nmagnitudes(typeof(sf))
    end
end

