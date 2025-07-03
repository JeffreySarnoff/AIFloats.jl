using Test
using AIFloats

@testset "AIFloats Main Module Tests" begin
    @testset "AIFloat Constructor - Basic Functionality" begin
        # Test basic signed finite construction
        af1 = AIFloat(8, 4; SignedFloat=true, FiniteFloat=true)
        @test isa(af1, SignedFiniteFloats{8, 4})
        
        # Test basic unsigned finite construction
        af2 = AIFloat(8, 4; UnsignedFloat=true, FiniteFloat=true)
        @test isa(af2, UnsignedFiniteFloats{8, 4})
        
        # Test basic signed extended construction
        af3 = AIFloat(8, 4; SignedFloat=true, ExtendedFloat=true)
        @test isa(af3, SignedExtendedFloats{8, 4})
        
        # Test basic unsigned extended construction
        af4 = AIFloat(8, 4; UnsignedFloat=true, ExtendedFloat=true)
        @test isa(af4, UnsignedExtendedFloats{8, 4})
    end
    
    @testset "AIFloat Constructor - Parameter Validation" begin
        # Test that exactly one signedness must be specified
        @test_throws ErrorException AIFloat(8, 4; FiniteFloat=true)
        @test_throws ErrorException AIFloat(8, 4; SignedFloat=true, UnsignedFloat=true, FiniteFloat=true)
        
        # Test that exactly one finiteness must be specified
        @test_throws ErrorException AIFloat(8, 4; SignedFloat=true)
        @test_throws ErrorException AIFloat(8, 4; SignedFloat=true, FiniteFloat=true, ExtendedFloat=true)
        
        # Test invalid parameter ranges for unsigned
        @test_throws ErrorException AIFloat(4, 5; UnsignedFloat=true, FiniteFloat=true)  # sigbits > bitwidth
        @test_throws ErrorException AIFloat(8, 0; UnsignedFloat=true, FiniteFloat=true)  # sigbits < 1
        
        # Test invalid parameter ranges for signed
        @test_throws ErrorException AIFloat(4, 4; SignedFloat=true, FiniteFloat=true)   # sigbits >= bitwidth
        @test_throws ErrorException AIFloat(8, 0; SignedFloat=true, FiniteFloat=true)   # sigbits < 1
    end
    
    @testset "AIFloat Constructor - Valid Parameter Ranges" begin
        # Test valid unsigned ranges
        af_u1 = AIFloat(8, 8; UnsignedFloat=true, FiniteFloat=true)  # sigbits == bitwidth is OK for unsigned
        @test isa(af_u1, UnsignedFiniteFloats{8, 8})
        
        af_u2 = AIFloat(6, 3; UnsignedFloat=true, FiniteFloat=true)
        @test isa(af_u2, UnsignedFiniteFloats{6, 3})
        
        # Test valid signed ranges
        af_s1 = AIFloat(8, 7; SignedFloat=true, FiniteFloat=true)   # sigbits < bitwidth required for signed
        @test isa(af_s1, SignedFiniteFloats{8, 7})
        
        af_s2 = AIFloat(6, 3; SignedFloat=true, FiniteFloat=true)
        @test isa(af_s2, SignedFiniteFloats{6, 3})
    end
    
    @testset "AIFloat from Type Constructor" begin
        # Test constructing AIFloat from existing type
        original = AIFloat(8, 4; SignedFloat=true, FiniteFloat=true)
        reconstructed = AIFloat(typeof(original))
        
        @test typeof(original) == typeof(reconstructed)
        @test floats(original) == floats(reconstructed)
        @test codes(original) == codes(reconstructed)
        
        # Test with different configurations
        uf_orig = AIFloat(6, 3; UnsignedFloat=true, ExtendedFloat=true)
        uf_recon = AIFloat(typeof(uf_orig))
        @test typeof(uf_orig) == typeof(uf_recon)
    end
    
    @testset "ConstructAIFloat Internal Function" begin
        # Test the internal constructor directly
        sf = ConstructAIFloat(8, 4; SignedFloat=true, ExtendedFloat=false)
        @test isa(sf, SignedFiniteFloats{8, 4})
        
        se = ConstructAIFloat(8, 4; SignedFloat=true, ExtendedFloat=true)
        @test isa(se, SignedExtendedFloats{8, 4})
        
        uf = ConstructAIFloat(8, 4; SignedFloat=false, ExtendedFloat=false)
        @test isa(uf, UnsignedFiniteFloats{8, 4})
        
        ue = ConstructAIFloat(8, 4; SignedFloat=false, ExtendedFloat=true)
        @test isa(ue, UnsignedExtendedFloats{8, 4})
    end
    
    @testset "Type Helper Functions" begin
        # Test typeforfloat and typeforcode functions
        af = AIFloat(8, 4; SignedFloat=true, FiniteFloat=true)
        
        @test typeforfloat(typeof(af)) == typeforfloat(8)
        @test typeforcode(typeof(af)) == typeforcode(8)
        
        # Test with different bit widths
        af_small = AIFloat(6, 3; UnsignedFloat=true, FiniteFloat=true)
        @test typeforfloat(typeof(af_small)) == typeforfloat(6)
        @test typeforcode(typeof(af_small)) == typeforcode(6)
    end
    
    @testset "Constants and Exports" begin
        # Test that boolean constants are properly defined
        @test UnsignedFloat === true
        @test SignedFloat === true
        @test FiniteFloat === true
        @test ExtendedFloat === true
        
        # These should be accessible as they're exported or used in constructors
        @test AIFloats.UnsignedFloat === true
        @test AIFloats.SignedFloat === true
        @test AIFloats.FiniteFloat === true  
        @test AIFloats.ExtendedFloat === true
    end
    
    @testset "Comprehensive Construction Matrix" begin
        # Test all valid combinations systematically
        bit_sig_pairs = [(4, 2), (6, 3), (8, 4), (8, 6)]
        
        for (bits, sigbits) in bit_sig_pairs
            # Signed finite
            sf = AIFloat(bits, sigbits; SignedFloat=true, FiniteFloat=true)
            @test isa(sf, SignedFiniteFloats{bits, sigbits})
            @test length(floats(sf)) == 2^bits
            
            # Signed extended  
            se = AIFloat(bits, sigbits; SignedFloat=true, ExtendedFloat=true)
            @test isa(se, SignedExtendedFloats{bits, sigbits})
            @test length(floats(se)) == 2^bits
            
            # Unsigned finite (allow sigbits == bits for unsigned)
            if sigbits <= bits
                uf = AIFloat(bits, sigbits; UnsignedFloat=true, FiniteFloat=true)
                @test isa(uf, UnsignedFiniteFloats{bits, sigbits})
                @test length(floats(uf)) == 2^bits
                
                # Unsigned extended
                ue = AIFloat(bits, sigbits; UnsignedFloat=true, ExtendedFloat=true)
                @test isa(ue, UnsignedExtendedFloats{bits, sigbits})
                @test length(floats(ue)) == 2^bits
            end
        end
    end
    
    @testset "Type Reconstruction Consistency" begin
        # Test that reconstructing from a type gives identical results
        original_configs = [
            (8, 4, true, true),   # signed finite
            (8, 4, true, false),  # signed extended
            (8, 4, false, true),  # unsigned finite
            (8, 4, false, false), # unsigned extended
        ]
        
        for (bits, sigbits, is_signed, is_finite) in original_configs
            # Create original
            original = ConstructAIFloat(bits, sigbits; SignedFloat=is_signed, ExtendedFloat=!is_finite)
            
            # Reconstruct from type
            reconstructed = AIFloat(typeof(original))
            
            # Should be identical
            @test typeof(original) == typeof(reconstructed)
            @test nBits(typeof(original)) == nBits(typeof(reconstructed))
            @test nSigBits(typeof(original)) == nSigBits(typeof(reconstructed))
            @test is_signed(typeof(original)) == is_signed(typeof(reconstructed))
            @test is_extended(typeof(original)) == is_extended(typeof(reconstructed))
        end
    end
    
    @testset "Error Message Quality" begin
        # Test that error messages are informative
        try
            AIFloat(8, 4; FiniteFloat=true)  # Missing signedness
            @test false  # Should not reach here
        catch e
            @test occursin("SignedFloat", string(e))
            @test occursin("UnsignedFloat", string(e))
        end
        
        try
            AIFloat(8, 4; SignedFloat=true)  # Missing finiteness
            @test false  # Should not reach here
        catch e
            @test occursin("FiniteFloat", string(e))
            @test occursin("ExtendedFloat", string(e))
        end
        
        try
            AIFloat(4, 5; UnsignedFloat=true, FiniteFloat=true)  # Invalid range
            @test false  # Should not reach here
        catch e
            @test occursin("bitwidth", string(e)) || occursin("precision", string(e))
        end
    end
    
    @testset "Module Integration" begin
        # Test that the main module properly integrates all components
        af = AIFloat(8, 4; SignedFloat=true, FiniteFloat=true)
        
        # Should be able to access all the expected functionality
        @test isa(floats(af), Vector)
        @test isa(codes(af), Vector)
        @test nBits(typeof(af)) == 8
        @test nSigBits(typeof(af)) == 4
        @test is_signed(typeof(af)) == true
        @test is_finite(typeof(af)) == true
        
        # Should work with all the defined functions
        @test nValues(typeof(af)) > 0
        @test nMagnitudes(typeof(af)) > 0
        @test expBias(typeof(af)) > 0
    end
    
    @testset "Edge Case Bit Widths" begin
        # Test minimal configurations
        af_min = AIFloat(3, 2; SignedFloat=true, FiniteFloat=true)
        @test isa(af_min, SignedFiniteFloats{3, 2})
        @test length(floats(af_min)) == 8  # 2^3
        
        # Test with precision = 1 (should work for unsigned)
        af_p1 = AIFloat(3, 1; UnsignedFloat=true, FiniteFloat=true)  
        @test isa(af_p1, UnsignedFiniteFloats{3, 1})
        @test !has_subnormals(typeof(af_p1))  # precision 1 has no subnormals
        
        # Test larger configurations
        af_large = AIFloat(12, 8; SignedFloat=true, ExtendedFloat=true)
        @test isa(af_large, SignedExtendedFloats{12, 8})
        @test length(floats(af_large)) == 4096  # 2^12
    end
end