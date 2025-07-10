@testset "AIFloats Main Module Tests" begin
    @testset "AIFloat Constructor - Basic Functionality" begin
        # Test basic signed finite construction
        af1 = AIFloat(8, 4, :signed, :finite)
        @test isa(af1, SignedFinite{8, 4})
        
        # Test basic unsigned finite construction
        af2 = AIFloat(8, 4, :unsigned, :finite)
        @test isa(af2, UnsignedFinite{8, 4})
        
        # Test basic signed extended construction
        af3 = AIFloat(8, 4, :signed, :extended)
        @test isa(af3, SignedExtended{8, 4})
        
        # Test basic unsigned extended construction
        af4 = AIFloat(8, 4, :unsigned, :extended)
        @test isa(af4, UnsignedExtended{8, 4})
    end
    
    @testset "AIFloat Constructor - Parameter Validation" begin
        # Test that exactly one signedness must be specified
        @test_throws ErrorException AIFloat(8, 4, :finite)
        @test_throws ErrorException AIFloat(8, 4, :signed, :unsigned, :finite)
        
        # Test that exactly one finiteness must be specified
        @test_throws ErrorException AIFloat(8, 4, :signed)
        @test_throws ErrorException AIFloat(8, 4, :signed, :extended, :finite)
        
        # Test invalid parameter ranges for unsigned
        @test_throws ErrorException AIFloat(4, 5, :unsigned, :finite)  # sigbits > bitwidth
        @test_throws ErrorException AIFloat(8, 0, :unsigned, :finite)  # sigbits < 1
        
        # Test invalid parameter ranges for signed
        @test_throws ErrorException AIFloat(4, 4, :signed, :finite)   # sigbits >= bitwidth
        @test_throws ErrorException AIFloat(8, 0, :signed, :finite)   # sigbits < 1
    end
    
    @testset "AIFloat Constructor - Valid Parameter Ranges" begin
        # Test valid unsigned ranges
        af_u1 = AIFloat(8, 8, :unsigned, :finite)  # sigbits == bitwidth is OK for unsigned
        @test isa(af_u1, UnsignedFinite{8, 8})
        
        af_u2 = AIFloat(6, 3, :unsigned, :finite)
        @test isa(af_u2, UnsignedFinite{6, 3})
        
        # Test valid signed ranges
        af_s1 = AIFloat(8, 7, :signed, :finite)   # sigbits < bitwidth required for signed
        @test isa(af_s1, SignedFinite{8, 7})
        
        af_s2 = AIFloat(6, 3, :signed, :finite)
        @test isa(af_s2, SignedFinite{6, 3})
    end
    
    @testset "AIFloat from Type Constructor" begin
        # Test constructing AIFloat from existing type
        original = AIFloat(8, 4, :signed, :finite)
        reconstructed = AIFloat(typeof(original))
        
        @test typeof(original) == typeof(reconstructed)
        @test all(floats(original) .=== floats(reconstructed))
        @test codes(original) == codes(reconstructed)
        
        # Test with different configurations
        uf_orig = AIFloat(6, 3, :unsigned, :extended)
        uf_recon = AIFloat(typeof(uf_orig))
        @test typeof(uf_orig) == typeof(uf_recon)
    end
    
    @testset "ConstructAIFloat Internal Function" begin
        # Test the internal constructor directly
        sf = ConstructAIFloat(8, 4; plusminus=true, extended=false)
        @test isa(sf, SignedFinite{8, 4})
        
        se = ConstructAIFloat(8, 4; plusminus=true, extended=true)
        @test isa(se, SignedExtended{8, 4})
        
        uf = ConstructAIFloat(8, 4; plusminus=false, extended=false)
        @test isa(uf, UnsignedFinite{8, 4})
        
        ue = ConstructAIFloat(8, 4; plusminus=false, extended=true)
        @test isa(ue, UnsignedExtended{8, 4})
    end
    
    @testset "Type Helper Functions" begin
        # Test typeforfloat and typeforcode functions
        af = AIFloat(8, 4, :signed, :finite)
        
        @test typeforfloat(typeof(af)) == typeforfloat(8)
        @test typeforcode(typeof(af)) == typeforcode(8)
        
        # Test with different bit widths
        af_small = AIFloat(6, 3, :unsigned, :finite)
        @test typeforfloat(typeof(af_small)) == typeforfloat(6)
        @test typeforcode(typeof(af_small)) == typeforcode(6)
    end
    
    @testset "Comprehensive Construction Matrix" begin
        # Test all valid combinations systematically
        bit_sig_pairs = [(4, 2), (6, 3), (8, 4), (8, 6)]
        
        for (bits, sigbits) in bit_sig_pairs
            # Signed finite
            sf = AIFloat(bits, sigbits, :signed, :finite)
            @test isa(sf, SignedFinite{bits, sigbits})
            @test length(floats(sf)) == 2^bits
            
            # Signed extended  
            se = AIFloat(bits, sigbits, :signed, :extended)
            @test isa(se, SignedExtended{bits, sigbits})
            @test length(floats(se)) == 2^bits
            
            # Unsigned finite (allow sigbits == bits for unsigned)
            if sigbits <= bits
                uf = AIFloat(bits, sigbits, :unsigned, :finite)
                @test isa(uf, UnsignedFinite{bits, sigbits})
                @test length(floats(uf)) == 2^bits
                
                # Unsigned extended
                ue = AIFloat(bits, sigbits, :unsigned, :extended)
                @test isa(ue, UnsignedExtended{bits, sigbits})
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
            original = ConstructAIFloat(bits, sigbits; plusminus=is_signed, extended=!is_finite)
            
            # Reconstruct from type
            reconstructed = AIFloat(typeof(original))
            
            # Should be identical
            @test typeof(original) == typeof(reconstructed)
            @test nbits(typeof(original)) == nbits(typeof(reconstructed))
            @test nbits_sig(typeof(original)) == nbits_sig(typeof(reconstructed))
            @test AIFloats.is_signed(typeof(original)) == AIFloats.is_signed(typeof(reconstructed))
            @test AIFloats.is_extended(typeof(original)) == AIFloats.is_extended(typeof(reconstructed))
        end
    end
    
    @testset "Module Integration" begin
        # Test that the main module properly integrates all components
        af = AIFloat(8, 4, :signed, :finite)
        
        # Should be able to access all the expected functionality
        @test isa(floats(af), Vector)
        @test isa(codes(af), Vector)
        @test nbits(typeof(af)) == 8
        @test nbits_sig(typeof(af)) == 4
        @test is_signed(typeof(af)) == true
        @test is_finite(typeof(af)) == true
        
        # Should work with all the defined functions
        @test nvalues(typeof(af)) > 0
        @test nmagnitudes(typeof(af)) > 0
        @test exp_bias(typeof(af)) > 0
    end
    
    @testset "Edge Case Bit Widths" begin
        # Test minimal configurations
        af_min = AIFloat(3, 2, :signed, :finite)
        @test isa(af_min, SignedFinite{3, 2})
        @test length(floats(af_min)) == 8  # 2^3
        
        # Test with precision = 1 (should work for unsigned)
        af_p1 = AIFloat(3, 1, :unsigned, :finite)
        @test isa(af_p1, UnsignedFinite{3, 1})
        @test !has_subnormals(typeof(af_p1))  # precision 1 has no subnormals
        
        # Test larger configurations
        af_large = AIFloat(12, 8, :signed, :extended)
        @test isa(af_large, SignedExtended{12, 8})
        @test length(floats(af_large)) == 4096  # 2^12
    end
end

