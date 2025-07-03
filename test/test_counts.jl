using Test
using AIFloats
using AIFloats: AbsSignedFiniteFloat, AbsUnsignedFiniteFloat,
                  nNaNs, nZeros, nInfs, nPosInfs, nNegInfs,
                  nBits, nSigBits, nFracBits, nSignBits, nExpBits,
                  nValues, nNumericValues, nNonzeroNumericValues,
                  nMagnitudes, nNonzeroMagnitudes,
                  nFiniteValues, nNonzeroFiniteValues,
                  nPrenormalMagnitudes, nSubnormalMagnitudes,
                  nPrenormalValues, nSubnormalValues,
                  nNormalMagnitudes, nNormalValues,
                  nFiniteMagnitudes, nFiniteValues,
                  nNonzeroFiniteMagnitudes, nNonzeroFiniteValues,
                  nPrenormalValues, nSubnormalValues,
                  nNormalValues, nExtendedNormalValues,
                  nExtendedNormalMagnitudes, nFiniteNonnegValues,
                  nFinitePositiveValues, nFiniteNegativeValues,
                  nNonnegValues, nPositiveValues, nNegativeValues,
                  nFiniteNonnegValues, nFinitePositiveValues, nFiniteNegativeValues,
                  nSubnormalValues, nSubnormalMagnitudes,
                  nNormalValues, nNormalMagnitudes,
                  nExpValues, nNonzeroExpValues

# Create test types for count testing
struct TestSignedFinite{Bits, SigBits} <: AbsSignedFiniteFloat{Bits, SigBits} end
struct TestSignedExtended{Bits, SigBits} <: AbsSignedExtendedFloat{Bits, SigBits} end
struct TestUnsignedFinite{Bits, SigBits} <: AbsUnsignedFiniteFloat{Bits, SigBits} end
struct TestUnsignedExtended{Bits, SigBits} <: AbsUnsignedExtendedFloat{Bits, SigBits} end

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
        @test nBits(TestSignedFinite{8, 4}) == 8
        @test nBits(TestUnsignedExtended{6, 3}) == 6
        @test nSigBits(TestSignedFinite{8, 4}) == 4
        @test nSigBits(TestUnsignedExtended{6, 3}) == 3
        @test nFracBits(TestSignedFinite{8, 4}) == 3
        @test nFracBits(TestUnsignedExtended{6, 3}) == 2
        
        # Sign bits
        @test nSignBits(TestSignedFinite{8, 4}) == 1
        @test nSignBits(TestUnsignedFinite{6, 3}) == 0
        
        # Exponent bits
        @test nExpBits(TestSignedFinite{8, 4}) == 4  # 8 - 4 = 4
        @test nExpBits(TestUnsignedFinite{6, 3}) == 4  # 6 - 3 + 1 = 4
    end
    
    @testset "Value Counts" begin
        # Total values
        @test nValues(TestSignedFinite{8, 4}) == 256  # 2^8
        @test nValues(TestUnsignedFinite{6, 3}) == 64   # 2^6
        
        # Numeric values (excluding NaN)
        @test nNumericValues(TestSignedFinite{8, 4}) == 255  # 256 - 1
        @test nNonzeroNumericValues(TestSignedFinite{8, 4}) == 254  # 255 - 1
    end
    
    @testset "Magnitude Counts" begin
        # For signed types, magnitudes are half the values
        @test nMagnitudes(TestSignedFinite{8, 4}) == 128  # 256 / 2
        @test nMagnitudes(TestSignedExtended{8, 4}) == 128
        
        # For unsigned types, magnitudes exclude NaN
        @test nMagnitudes(TestUnsignedFinite{6, 3}) == 63  # 64 - 1
        @test nMagnitudes(TestUnsignedExtended{6, 3}) == 63
        
        @test nNonzeroMagnitudes(TestSignedFinite{8, 4}) == 127  # 128 - 1
        @test nNonzeroMagnitudes(TestUnsignedFinite{6, 3}) == 62  # 63 - 1
    end
    
    @testset "Finite Value Counts" begin
        # Finite values exclude infinities
        @test nFiniteValues(TestSignedFinite{8, 4}) == 255  # no infinities
        @test nFiniteValues(TestSignedExtended{8, 4}) == 253  # 255 - 2
        @test nFiniteValues(TestUnsignedFinite{6, 3}) == 63   # no infinities
        @test nFiniteValues(TestUnsignedExtended{6, 3}) == 62  # 63 - 1
        
        @test nNonzeroFiniteValues(TestSignedFinite{8, 4}) == 254
        @test nNonzeroFiniteValues(TestSignedExtended{8, 4}) == 252
    end
    
    @testset "Prenormal and Subnormal Counts" begin
        # Prenormal magnitudes depend on significand bits
        @test nPrenormalMagnitudes(TestSignedFinite{8, 4}) == 8   # 2^(4-1)
        @test nPrenormalMagnitudes(TestUnsignedFinite{6, 3}) == 4  # 2^(3-1)
        
        @test nSubnormalMagnitudes(TestSignedFinite{8, 4}) == 7   # 8 - 1
        @test nSubnormalMagnitudes(TestUnsignedFinite{6, 3}) == 3  # 4 - 1
        
        # Prenormal values
        @test nPrenormalValues(TestSignedFinite{8, 4}) == 15      # 2*8 - 1
        @test nPrenormalValues(TestUnsignedFinite{6, 3}) == 4     # 4
        
        @test nSubnormalValues(TestSignedFinite{8, 4}) == 14      # 15 - 1
        @test nSubnormalValues(TestUnsignedFinite{6, 3}) == 3     # 4 - 1
    end
    
    @testset "Count Relationships" begin
        # Test relationships between different counts
        T = TestSignedFinite{8, 4}
        
        @test nNumericValues(T) == nValues(T) - nNaNs(T)
        @test nNonzeroNumericValues(T) == nNumericValues(T) - nZeros(T)
        @test nFiniteValues(T) == nNumericValues(T) - nInfs(T)
        @test nSubnormalValues(T) == nPrenormalValues(T) - 1
        @test nSubnormalMagnitudes(T) == nPrenormalMagnitudes(T) - 1
        
        # Bit relationships
        @test nFracBits(T) == nSigBits(T) - 1
    end
    
    @testset "Instance vs Type Counts" begin
        # Test that count functions work on both types and instances
        test_type = TestSignedFinite{8, 4}
        test_instance = test_type()
        
        @test nBits(test_type) == nBits(test_instance)
        @test nSigBits(test_type) == nSigBits(test_instance)
        @test nValues(test_type) == nValues(test_instance)
        @test nMagnitudes(test_type) == nMagnitudes(test_instance)
        @test nInfs(test_type) == nInfs(test_instance)
    end
    
    @testset "Edge Cases" begin
        # Test minimal configurations
        T_min = TestUnsignedFinite{2, 1}
        @test nBits(T_min) == 2
        @test nSigBits(T_min) == 1
        @test nValues(T_min) == 4
        @test nPrenormalMagnitudes(T_min) == 1  # 2^(1-1) = 1
        
        # Test that counts are always positive
        for Bits in 3:8, SigBits in 1:(Bits-1)
            T = TestSignedFinite{Bits, SigBits}
            @test nValues(T) > 0
            @test nMagnitudes(T) > 0
            @test nPrenormalMagnitudes(T) > 0
        end
    end
end

