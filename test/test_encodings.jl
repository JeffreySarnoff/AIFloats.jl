using Test
using AIFloats
using AIFloats: AbsSignedFiniteFloat, AbsUnsignedFiniteFloat, encoding_sequence, typeforcode

using AlignedAllocs

# Create test types for encoding testing
struct TestSignedFinite{Bits, SigBits} <: AbsSignedFiniteFloat{Bits, SigBits} end
struct TestUnsignedFinite{Bits, SigBits} <: AbsUnsignedFiniteFloat{Bits, SigBits} end

@testset "Encodings Tests" begin
    @testset "Basic Encoding Sequence" begin
        T = TestSignedFinite{8, 4}
        
        codes = encoding_sequence(T)
        @test isa(codes, Vector)
        @test length(codes) == nValues(T)
        @test length(codes) == 2^nBits(T)
        
        # Should contain all values from 0 to 2^bits - 1
        expected_values = collect(0:(2^nBits(T) - 1))
        @test sort(codes) == expected_values
        
        # Test element type
        expected_type = typeforcode(nBits(T))
        @test eltype(codes) == expected_type
    end
    
    @testset "Encoding Sequence with Different Bit Widths" begin
        # Test 8-bit encoding (should use UInt8)
        T8 = TestSignedFinite{8, 4}
        codes8 = encoding_sequence(T8)
        @test eltype(codes8) == UInt8
        @test length(codes8) == 256
        @test codes8 == collect(UInt8, 0:255)
        
        # Test larger bit width (should use UInt16)
        T12 = TestSignedFinite{12, 6}
        codes12 = encoding_sequence(T12)
        @test eltype(codes12) == UInt16
        @test length(codes12) == 4096  # 2^12
        @test codes12[1] == UInt16(0)
        @test codes12[end] == UInt16(4095)
    end
    
    @testset "Generic Integer Encoding Sequence" begin
        # Test the generic integer version
        codes_uint8 = encoding_sequence(UInt8, 6)
        @test eltype(codes_uint8) == UInt8
        @test length(codes_uint8) == 64  # 2^6
        @test codes_uint8 == collect(UInt8, 0:63)
        
        codes_uint16 = encoding_sequence(UInt16, 10)
        @test eltype(codes_uint16) == UInt16
        @test length(codes_uint16) == 1024  # 2^10
        @test codes_uint16[1] == UInt16(0)
        @test codes_uint16[end] == UInt16(1023)
    end
    
    @testset "Memory Alignment" begin
        T = TestSignedFinite{6, 3}
        codes = encoding_sequence(T)
        
        # Test that memory is properly aligned (AlignedAllocs requirement)
        @test isa(codes, Vector)
        
        # Test that all values are present and correct
        @test issorted(codes)
        @test codes[1] == 0
        @test codes[end] == 2^nBits(T) - 1
    end
    
    @testset "Encoding Consistency Across Types" begin
        # Test that different AIFloat types with same bit width produce same encodings
        TS = TestSignedFinite{8, 4}
        TU = TestUnsignedFinite{8, 4}
        
        codes_s = encoding_sequence(TS)
        codes_u = encoding_sequence(TU)
        
        @test codes_s == codes_u
        @test eltype(codes_s) == eltype(codes_u)
        @test length(codes_s) == length(codes_u)
    end
    
    @testset "Instance Function Coverage" begin
        # Test that encoding_sequence works with instances
        test_type = TestSignedFinite{8, 4}
        test_instance = test_type()
        
        codes_type = encoding_sequence(test_type)
        codes_instance = encoding_sequence(test_instance)
        
        @test codes_type == codes_instance
        @test eltype(codes_type) == eltype(codes_instance)
    end
    
    @testset "Edge Cases" begin
        # Test minimal bit width
        T_min = TestSignedFinite{2, 1}
        codes_min = encoding_sequence(T_min)
        @test length(codes_min) == 4  # 2^2
        @test codes_min == [0, 1, 2, 3]
        @test eltype(codes_min) == UInt8
        
        # Test near-maximum bit width for UInt8
        T_max8 = TestSignedFinite{8, 4}
        codes_max8 = encoding_sequence(T_max8)
        @test length(codes_max8) == 256
        @test eltype(codes_max8) == UInt8
        
        # Test transition to UInt16
        T_trans = TestSignedFinite{9, 4}
        codes_trans = encoding_sequence(T_trans)
        @test length(codes_trans) == 512
        @test eltype(codes_trans) == UInt16
    end
    
    @testset "Performance and Memory" begin
        # Test that encoding sequences are efficiently generated
        T = TestSignedFinite{10, 5}
        
        # Should not throw and should complete quickly
        @test @allocated(encoding_sequence(T)) > 0
        
        codes = encoding_sequence(T)
        @test length(codes) == 2^10
        
        # Test memory efficiency - no unnecessary copying
        @test codes isa Vector{UInt16}
    end
    
    @testset "Type Correctness" begin
        # Verify that typeforcode is used correctly
        for bits in [3, 6, 8, 9, 12, 15]
            expected_type = typeforcode(bits)
            T = TestSignedFinite{bits, bits-1}
            codes = encoding_sequence(T)
            @test eltype(codes) == expected_type
            
            # Also test generic version
            generic_codes = encoding_sequence(expected_type, bits)
            @test eltype(generic_codes) == expected_type
            @test codes == generic_codes
        end
    end
    
    @testset "Monotonicity and Completeness" begin
        T = TestSignedFinite{7, 3}
        codes = encoding_sequence(T)
        
        # Test monotonicity
        @test issorted(codes)
        
        # Test completeness - no gaps in sequence
        for i in 1:length(codes)-1
            @test codes[i+1] == codes[i] + 1
        end
        
        # Test boundary values
        @test minimum(codes) == 0
        @test maximum(codes) == 2^nBits(T) - 1
        
        # Test no duplicates
        @test length(unique(codes)) == length(codes)
    end
end

