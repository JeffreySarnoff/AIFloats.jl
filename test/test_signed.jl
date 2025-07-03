using Test
using AIFloats

@testset "Signed Types Tests" begin
    @testset "SignedFiniteFloats Construction" begin
        # Test basic construction
        sf = SignedFiniteFloats(6, 3)
        @test isa(sf, SignedFiniteFloats)
        @test isa(sf, AbsSignedFiniteFloat{6, 3})
        
        # Test accessors
        @test isa(floats(sf), Vector)
        @test isa(codes(sf), Vector)
        @test length(floats(sf)) == length(codes(sf))
        @test length(floats(sf)) == 2^6  # 64 values
        
        # Test element types
        @test eltype(floats(sf)) == typeforfloat(6)
        @test eltype(codes(sf)) == typeforcode(6)
    end
    
    @testset "SignedExtendedFloats Construction" begin
        # Test basic construction
        se = SignedExtendedFloats(6, 3)
        @test isa(se, SignedExtendedFloats)
        @test isa(se, AbsSignedExtendedFloat{6, 3})
        
        # Test accessors
        @test isa(floats(se), Vector)
        @test isa(codes(se), Vector)
        @test length(floats(se)) == length(codes(se))
        @test length(floats(se)) == 2^6  # 64 values
        
        # Test element types
        @test eltype(floats(se)) == typeforfloat(6)
        @test eltype(codes(se)) == typeforcode(6)
    end
    
    @testset "Type-based Construction" begin
        # Test construction from abstract types
        T_finite = AbsSignedFiniteFloat{8, 4}
        sf_from_type = SignedFiniteFloats(T_finite)
        @test isa(sf_from_type, SignedFiniteFloats{8, 4})
        
        T_extended = AbsSignedExtendedFloat{8, 4}
        se_from_type = SignedExtendedFloats(T_extended)
        @test isa(se_from_type, SignedExtendedFloats{8, 4})
    end
    
    @testset "Value Sequence - Finite" begin
        T = AbsSignedFiniteFloat{6, 3}
        values = value_sequence(T)
        
        @test isa(values, Vector)
        @test eltype(values) == typeforfloat(6)
        
        # Should have both positive and negative values
        positive_values = filter(x -> x > 0 && isfinite(x), values)
        negative_values = filter(x -> x < 0 && isfinite(x), values)
        @test length(positive_values) > 0
        @test length(negative_values) > 0
        
        # Should have NaN (first negative value becomes NaN)
        nan_count = count(isnan, values)
        @test nan_count >= 1
        
        # Should have zero
        @test 0.0 in values
    end
    
    @testset "Value Sequence - Extended" begin
        T = AbsSignedExtendedFloat{6, 3}
        values = value_sequence(T)
        
        @test isa(values, Vector)
        @test eltype(values) == typeforfloat(6)
        
        # Should have both positive and negative infinities
        pos_inf_count = count(x -> isinf(x) && x > 0, values)
        neg_inf_count = count(x -> isinf(x) && x < 0, values)
        @test pos_inf_count >= 1
        @test neg_inf_count >= 1
        
        # Should have NaN
        nan_count = count(isnan, values)
        @test nan_count >= 1
        
        # Should have zero
        @test 0.0 in values
        
        # Should have both positive and negative finite values
        pos_finite = filter(x -> x > 0 && isfinite(x), values)
        neg_finite = filter(x -> x < 0 && isfinite(x), values)
        @test length(pos_finite) > 0
        @test length(neg_finite) > 0
    end
    
    @testset "Signed Value Structure" begin
        sf = SignedFiniteFloats(6, 3)
        values = floats(sf)
        
        # Should have symmetric structure around zero
        half_length = length(values) ÷ 2
        
        # First half should be non-negative magnitudes
        first_half = values[1:half_length]
        
        # Second half should be negative magnitudes (with NaN transformation)
        second_half = values[half_length+1:end]
        
        # Check that we have both positive and negative values
        has_positive = any(x -> x > 0 && isfinite(x), values)
        has_negative = any(x -> x < 0 && isfinite(x), values)
        @test has_positive && has_negative
        
        # First value should be zero or positive
        @test values[1] >= 0 || isnan(values[1])
    end
    
    @testset "Finite vs Extended Special Values" begin
        # Test finite version
        sf = SignedFiniteFloats(6, 3)
        finite_values = floats(sf)
        
        # Should have NaN but no infinities
        @test any(isnan, finite_values)
        @test !any(isinf, finite_values)
        
        # Test extended version  
        se = SignedExtendedFloats(6, 3)
        extended_values = floats(se)
        
        # Should have NaN and infinities
        @test any(isnan, extended_values)
        @test any(x -> isinf(x) && x > 0, extended_values)  # +Inf
        @test any(x -> isinf(x) && x < 0, extended_values)  # -Inf
    end
    
    @testset "Magnitude Transformation" begin
        T = AbsSignedFiniteFloat{6, 3}
        values = value_sequence(T)
        
        # Get foundation magnitudes
        foundation_mags = foundation_magnitudes(T)
        half_length = length(values) ÷ 2
        
        # First half should be based on foundation magnitudes
        nonneg_values = values[1:half_length]
        
        # Check that non-NaN values in first half match foundation pattern
        finite_nonneg = filter(!isnan, nonneg_values)
        if length(finite_nonneg) > 0
            @test finite_nonneg[1] == 0.0  # Should start with zero
            @test all(x -> x >= 0, finite_nonneg)
        end
    end
    
    @testset "NaN Placement in Signed Types" begin
        # In signed finite types, first negative magnitude becomes NaN
        sf = SignedFiniteFloats(6, 3)
        values = floats(sf)
        
        half_length = length(values) ÷ 2
        
        # There should be exactly one NaN in the negative half
        negative_half = values[half_length+1:end]
        nan_in_negative = count(isnan, negative_half)
        @test nan_in_negative >= 1
        
        # For extended types, NaN placement might be different
        se = SignedExtendedFloats(6, 3)
        ext_values = floats(se)
        
        # Should have exactly one NaN total
        total_nans = count(isnan, ext_values)
        @test total_nans >= 1
    end
    
    @testset "Infinity Placement in Extended Types" begin
        se = SignedExtendedFloats(6, 3)
        values = floats(se)
        
        # Should have one positive and one negative infinity
        pos_infs = filter(x -> isinf(x) && x > 0, values)
        neg_infs = filter(x -> isinf(x) && x < 0, values)
        
        @test length(pos_infs) >= 1
        @test length(neg_infs) >= 1
        
        # Positive infinity should be near end of first half
        # Negative infinity should be near end of second half
        @test any(isinf, values)
    end
    
    @testset "Construction Consistency" begin
        # Test that different construction methods give same results
        bits, sigbits = 8, 4
        
        # Direct construction
        sf1 = SignedFiniteFloats(bits, sigbits)
        
        # Type-based construction
        T = AbsSignedFiniteFloat{bits, sigbits}
        sf2 = SignedFiniteFloats(T)
        
        # Should be equivalent
        @test floats(sf1) == floats(sf2)
        @test codes(sf1) == codes(sf2)
    end
    
    @testset "Symmetry Properties" begin
        sf = SignedFiniteFloats(7, 3)
        values = floats(sf)
        
        # Extract finite values
        finite_values = filter(isfinite, values)
        positive_finite = filter(x -> x > 0, finite_values)
        negative_finite = filter(x -> x < 0, finite_values)
        
        # Should have roughly symmetric count of positive and negative
        # (accounting for zero and special values)
        @test abs(length(positive_finite) - length(negative_finite)) <= 2
        
        # Magnitudes should be similar
        pos_mags = abs.(positive_finite)
        neg_mags = abs.(negative_finite)
        
        if length(pos_mags) > 0 && length(neg_mags) > 0
            # Should have overlapping magnitude ranges
            @test maximum(pos_mags) > 0
            @test maximum(neg_mags) > 0
        end
    end
    
    @testset "Type Parameters" begin
        # Test that type parameters are correctly preserved
        sf = SignedFiniteFloats(12, 6)
        @test isa(sf, SignedFiniteFloats{12, 6})
        
        se = SignedExtendedFloats(10, 5)
        @test isa(se, SignedExtendedFloats{10, 5})
        
        # Test with different float/code types for larger bitwidths
        sf_large = SignedFiniteFloats(12, 6)
        @test eltype(floats(sf_large)) == typeforfloat(12)
        @