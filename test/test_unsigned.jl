using Test
using AIFloats

@testset "Unsigned Types Tests" begin
    @testset "UnsignedFiniteFloats Construction" begin
        # Test basic construction
        uf = UnsignedFiniteFloats(6, 3)
        @test isa(uf, UnsignedFiniteFloats)
        @test isa(uf, AbsUnsignedFiniteFloat{6, 3})
        
        # Test accessors
        @test isa(floats(uf), Vector)
        @test isa(codes(uf), Vector)
        @test length(floats(uf)) == length(codes(uf))
        @test length(floats(uf)) == 2^6  # 64 values
        
        # Test element types
        @test eltype(floats(uf)) == typeforfloat(6)
        @test eltype(codes(uf)) == typeforcode(6)
    end
    
    @testset "UnsignedExtendedFloats Construction" begin
        # Test basic construction
        ue = UnsignedExtendedFloats(6, 3)
        @test isa(ue, UnsignedExtendedFloats)
        @test isa(ue, AbsUnsignedExtendedFloat{6, 3})
        
        # Test accessors
        @test isa(floats(ue), Vector)
        @test isa(codes(ue), Vector)
        @test length(floats(ue)) == length(codes(ue))
        @test length(floats(ue)) == 2^6  # 64 values
        
        # Test element types
        @test eltype(floats(ue)) == typeforfloat(6)
        @test eltype(codes(ue)) == typeforcode(6)
    end
    
    @testset "Type-based Construction" begin
        # Test construction from abstract types
        T_finite = AbsUnsignedFiniteFloat{8, 4}
        uf_from_type = UnsignedFiniteFloats(T_finite)
        @test isa(uf_from_type, UnsignedFiniteFloats{8, 4})
        
        T_extended = AbsUnsignedExtendedFloat{8, 4}
        ue_from_type = UnsignedExtendedFloats(T_extended)
        @test isa(ue_from_type, UnsignedExtendedFloats{8, 4})
    end
    
    @testset "Value Sequence - Finite" begin
        T = AbsUnsignedFiniteFloat{6, 3}
        values = value_sequence(T)
        
        @test isa(values, Vector)
        @test eltype(values) == typeforfloat(6)
        
        # Should be based on foundation magnitudes
        foundation_mags = foundation_magnitudes(T)
        @test length(values) >= length(foundation_mags)
        
        # Last value should be NaN for finite unsigned types
        @test isnan(values[end])
        
        # All other values should be finite and non-negative
        finite_values = values[1:end-1]
        @test all(isfinite, finite_values)
        @test all(x -> x >= 0, finite_values)
        
        # Should start with zero
        @test values[1] == 0.0
    end
    
    @testset "Value Sequence - Extended" begin
        T = AbsUnsignedExtendedFloat{6, 3}
        values = value_sequence(T)
        
        @test isa(values, Vector)
        @test eltype(values) == typeforfloat(6)
        
        # Last value should be NaN
        @test isnan(values[end])
        
        # Second to last should be +Inf for extended types
        @test isinf(values[end-1]) && values[end-1] > 0
        
        # All other values should be finite and non-negative
        finite_values = values[1:end-2]
        @test all(isfinite, finite_values)
        @test all(x -> x >= 0, finite_values)
        
        # Should start with zero
        @test values[1] == 0.0
    end
    
    @testset "Codes Sequence" begin
        uf = UnsignedFiniteFloats(8, 4)
        codes_vec = codes(uf)
        
        # Should be complete sequence from 0 to 2^bits - 1
        @test length(codes_vec) == 256
        @test codes_vec[1] == 0
        @test codes_vec[end] == 255
        @test issorted(codes_vec)
        
        # Should have no gaps
        for i in 1:length(codes_vec)-1
            @test codes_vec[i+1] == codes_vec[i] + 1
        end
    end
    
    @testset "Finite vs Extended Differences" begin
        # Compare finite and extended versions
        uf = UnsignedFiniteFloats(6, 3)
        ue = UnsignedExtendedFloats(6, 3)
        
        finite_floats = floats(uf)
        extended_floats = floats(ue)
        
        # Should have same length
        @test length(finite_floats) == length(extended_floats)
        
        # Both end with NaN
        @test isnan(finite_floats[end])
        @test isnan(extended_floats[end])
        
        # Extended has +Inf as second-to-last
        @test !isinf(finite_floats[end-1])  # Finite doesn't have Inf
        @test isinf(extended_floats[end-1]) && extended_floats[end-1] > 0
        
        # Earlier values should be similar (magnitude sequences)
        n_compare = length(finite_floats) - 3  # Compare most values
        @test finite_floats[1:n_compare] ≈ extended_floats[1:n_compare] rtol=1e-10
    end
    
    @testset "Construction Consistency" begin
        # Test that different construction methods give same results
        bits, sigbits = 8, 4
        
        # Direct construction
        uf1 = UnsignedFiniteFloats(bits, sigbits)
        
        # Type-based construction
        T = AbsUnsignedFiniteFloat{bits, sigbits}
        uf2 = UnsignedFiniteFloats(T)
        
        # Should be equivalent
        @test floats(uf1) == floats(uf2)
        @test codes(uf1) == codes(uf2)
    end
    
    @testset "Value Properties" begin
        uf = UnsignedFiniteFloats(7, 3)
        values = floats(uf)
        
        # Test monotonicity (except for NaN at end)
        non_nan_values = values[1:end-1]
        @test issorted(non_nan_values)
        
        # Test that we have zero
        @test 0.0 in values
        
        # Test that we have some small positive values
        small_positive = filter(x -> 0 < x < 1, values)
        @test length(small_positive) > 0
        
        # Test that we have some values >= 1
        large_values = filter(x -> x >= 1 && isfinite(x), values)
        @test length(large_values) > 0
        
        # No negative values for unsigned
        finite_values = filter(isfinite, values)
        @test all(x -> x >= 0, finite_values)
    end
    
    @testset "Special Values Placement" begin
        # Test finite type special values
        uf = UnsignedFiniteFloats(6, 3)
        values = floats(uf)
        
        @test values[1] == 0.0  # Zero first
        @test isnan(values[end])  # NaN last
        @test !any(isinf, values[1:end-1])  # No infinities in finite
        
        # Test extended type special values
        ue = UnsignedExtendedFloats(6, 3)
        values_ext = floats(ue)
        
        @test values_ext[1] == 0.0  # Zero first
        @test isnan(values_ext[end])  # NaN last
        @test isinf(values_ext[end-1])  # +Inf second to last
        @test values_ext[end-1] > 0  # Positive infinity
    end
    
    @testset "Type Parameters" begin
        # Test that type parameters are correctly preserved
        uf = UnsignedFiniteFloats(12, 6)
        @test isa(uf, UnsignedFiniteFloats{12, 6})
        
        ue = UnsignedExtendedFloats(10, 5)
        @test isa(ue, UnsignedExtendedFloats{10, 5})
        
        # Test with different float/code types for larger bitwidths
        uf_large = UnsignedFiniteFloats(12, 6)
        @test eltype(floats(uf_large)) == typeforfloat(12)
        @test eltype(codes(uf_large)) == typeforcode(12)
    end
    
    @testset "Edge Cases" begin
        # Test minimal configuration
        uf_min = UnsignedFiniteFloats(2, 1)
        @test length(floats(uf_min)) == 4  # 2^2
        @test floats(uf_min)[1] == 0.0
        @test isnan(floats(uf_min)[end])
        
        # Test near-maximum configuration
        uf_large = UnsignedFiniteFloats(8, 7)
        @test length(floats(uf_large)) == 256
        @test floats(uf_large)[1] == 0.0
        @test isnan(floats(uf_large)[end])
    end
    
    @testset "Memory Layout" begin
        uf = UnsignedFiniteFloats(8, 4)
        
        # Test that vectors are properly allocated
        @test isa(floats(uf), Vector)
        @test isa(codes(uf), Vector)
        
        # Test correct sizes
        @test length(floats(uf)) == 2^8
        @test length(codes(uf)) == 2^8
        
        # Test that memory is initialized
        @test !any(isnan, floats(uf)[1:end-1])  # Only last should be NaN
        @test all(x -> 0 <= x <= 255, codes(uf))  # All codes valid
    end
    
    @testset "Numerical Accuracy" begin
        uf = UnsignedFiniteFloats(6, 3)
        values = floats(uf)
        
        # Test that foundation magnitudes are accurately represented
        foundation_mags = foundation_magnitudes(AbsUnsignedFiniteFloat{6, 3})
        
        # Most values should match foundation (except special values)
        n_foundation = length(foundation_mags)
        @test values[1:n_foundation] ≈ foundation_mags rtol=1e-12
    end
end