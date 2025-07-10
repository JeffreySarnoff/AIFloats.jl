@testset "Counts Tests" begin
    @testset "Basic Counts" begin
        @test nNaNs(TestSignedFinite{8, 4}) == 1
        @test nNaNs(TestUnsignedExtended{6, 3}) == 1
        @test nZeros(TestSignedFinite{8, 4}) == 1
        @test nZeros(TestUnsignedExtended{6, 3}) == 1
    end
    
    @testset "Infinity Counts" begin
        # Finite types have no infinities
        @test nInfs(TestSignedFinite{8, 4}) == 0
        @test nInfs(TestUnsignedFinite{6, 3}) == 0
        
        # Extended types have infinities
        @test nInfs(TestSignedExtended{8, 4}) == 2  # +Inf, -Inf
        @test nInfs(TestUnsignedExtended{6, 3}) == 1  # +Inf only
        
        # Positive infinities
        @test nPosInfs(TestSignedFinite{8, 4}) == 0
        @test nPosInfs(TestUnsignedFinite{6, 3}) == 0
        @test nPosInfs(TestSignedExtended{8, 4}) == 1
        @test nPosInfs(TestUnsignedExtended{6, 3}) == 1
        
        # Negative infinities
        @test nNegInfs(TestSignedFinite{8, 4}) == 0
        @test nNegInfs(TestUnsignedFinite{6, 3}) == 0
        @test nNegInfs(TestSignedExtended{8, 4}) == 1
        @test nNegInfs(TestUnsignedExtended{6, 3}) == 0
    end
    
    @testset "Bit Counts" begin
        # Test parameter extraction
        @test nbits(TestSignedFinite{8, 4}) == 8
        @test nbits(TestUnsignedExtended{6, 3}) == 6
        @test nbits_sig(TestSignedFinite{8, 4}) == 4
        @test nbits_sig(TestUnsignedExtended{6, 3}) == 3
        @test nbits_frac(TestSignedFinite{8, 4}) == 3
        @test nbits_frac(TestUnsignedExtended{6, 3}) == 2
        
        # Sign bits
        @test nbits_sign(TestSignedFinite{8, 4}) == 1
        @test nbits_sign(TestUnsignedFinite{6, 3}) == 0
        
        # Exponent bits
        @test nbits_exp(TestSignedFinite{8, 4}) == 4  # 8 - 4 = 4
        @test nbits_exp(TestUnsignedFinite{6, 3}) == 4  # 6 - 3 + 1 = 4
    end
    
    @testset "Value Counts" begin
        # Total values
        @test nvalues(TestSignedFinite{8, 4}) == 256  # 2^8
        @test nvalues(TestUnsignedFinite{6, 3}) == 64   # 2^6
        
        # Numeric values (excluding NaN)
        @test nvalues_numeric(TestSignedFinite{8, 4}) == 255  # 256 - 1
        @test nvalues_numeric_nonzero(TestSignedFinite{8, 4}) == 254  # 255 - 1
    end
    
    @testset "Magnitude Counts" begin
        # For signed types, magnitudes are half the values
        @test nmagnitudes(TestSignedFinite{8, 4}) == 128  # 256 / 2
        @test nmagnitudes(TestSignedExtended{8, 4}) == 128
        
        # For unsigned types, magnitudes exclude NaN
        @test nmagnitudes(TestUnsignedFinite{6, 3}) == 63  # 64 - 1
        @test nmagnitudes(TestUnsignedExtended{6, 3}) == 63
        
        @test nmagnitudes_nonzero(TestSignedFinite{8, 4}) == 127  # 128 - 1
        @test nmagnitudes_nonzero(TestUnsignedFinite{6, 3}) == 62  # 63 - 1
    end
    
    @testset "Finite Value Counts" begin
        # Finite values exclude infinities
        @test nvalues_finite(TestSignedFinite{8, 4}) == 255  # no infinities
        @test nvalues_finite(TestSignedExtended{8, 4}) == 253  # 255 - 2
        @test nvalues_finite(TestUnsignedFinite{6, 3}) == 63   # no infinities
        @test nvalues_finite(TestUnsignedExtended{6, 3}) == 62  # 63 - 1
        
        @test nvalues_finite_nonzero(TestSignedFinite{8, 4}) == 254
        @test nvalues_finite_nonzero(TestSignedExtended{8, 4}) == 252
    end
    
    @testset "Prenormal and Subnormal Counts" begin
        # Prenormal magnitudes depend on significand bits
        @test nmagnitudes_prenormal(TestSignedFinite{8, 4}) == 8   # 2^(4-1)
        @test nmagnitudes_prenormal(TestUnsignedFinite{6, 3}) == 4  # 2^(3-1)
        
        @test nmagnitudes_subnormal(TestSignedFinite{8, 4}) == 7   # 8 - 1
        @test nmagnitudes_subnormal(TestUnsignedFinite{6, 3}) == 3  # 4 - 1
        
        # Prenormal values
        @test nvalues_prenormal(TestSignedFinite{8, 4}) == 15      # 2*8 - 1
        @test nvalues_prenormal(TestUnsignedFinite{6, 3}) == 4     # 4
        
        @test nvalues_subnormal(TestSignedFinite{8, 4}) == 14      # 15 - 1
        @test nvalues_subnormal(TestUnsignedFinite{6, 3}) == 3     # 4 - 1
    end
    
    @testset "Count Relationships" begin
        # Test relationships between different counts
        T = TestSignedFinite{8, 4}
        
        @test nvalues_numeric(T) == nvalues(T) - nNaNs(T)
        @test nvalues_numeric_nonzero(T) == nvalues_numeric(T) - nZeros(T)
        @test nvalues_finite(T) == nvalues_numeric(T) - nInfs(T)
        @test nvalues_subnormal(T) == nvalues_prenormal(T) - 1
        @test nmagnitudes_subnormal(T) == nmagnitudes_prenormal(T) - 1
        
        # Bit relationships
        @test nbits_frac(T) == nbits_sig(T) - 1
    end
    
    @testset "Instance vs Type Counts" begin
        # Test that count functions work on both types and instances
        test_type = TestSignedFinite{8, 4}
        test_instance = test_type()
        
        @test nbits(test_type) == nbits(test_instance)
        @test nbits_sig(test_type) == nbits_sig(test_instance)
        @test nvalues(test_type) == nvalues(test_instance)
        @test nmagnitudes(test_type) == nmagnitudes(test_instance)
        @test nInfs(test_type) == nInfs(test_instance)
    end
    
    @testset "Edge Cases" begin
        # Test minimal configurations
        T_min = TestUnsignedFinite{2, 1}
        @test nbits(T_min) == 2
        @test nbits_sig(T_min) == 1
        @test nvalues(T_min) == 4
        @test nmagnitudes_prenormal(T_min) == 1  # 2^(1-1) = 1
        
        # Test that counts are always positive
        for Bits in 3:8, SigBits in 1:(Bits-1)
            T = TestSignedFinite{Bits, SigBits}
            @test nvalues(T) > 0
            @test nmagnitudes(T) > 0
            @test nmagnitudes_prenormal(T) > 0
        end
    end
end

