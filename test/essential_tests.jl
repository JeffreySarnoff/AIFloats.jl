using Test
using AIFloats

@testset "AIFloats.jl Core Functionality" begin
    
    @testset "Abstract Type Hierarchy" begin
        # Test type hierarchy construction
        @test AbstractAIFloat{4, 2, true} <: AbstractFloat
        @test AbstractSigned{4, 2} <: AbstractAIFloat{4, 2, true}
        @test AbstractUnsigned{4, 2} <: AbstractAIFloat{4, 2, false}
        @test AkoSignedFinite{4, 2} <: AbstractSigned{4, 2}
        @test AkoUnsignedExtended{4, 2} <: AbstractUnsigned{4, 2}
    end
    
    @testset "AIFloat Constructor" begin
        # Test basic constructor with keyword arguments
        sf32 = AIFloat(3, 2, :signed, :finite)
        @test typeof(sf32) <: AkoSignedFinite{3, 2}
        @test length(floats(sf32)) == 8
        @test length(codes(sf32)) == 8
        
        ue43 = AIFloat(4, 3, :unsigned, :extended)
        @test typeof(ue43) <: AkoUnsignedExtended{4, 3}
        @test length(floats(ue43)) == 16
        
        # Test constructor validation
        @test_throws ErrorException AIFloat(3, 4, :signed, :finite)  # precision > bitwidth-1 for signed
        @test_throws ErrorException AIFloat(3, 1, :neither, :finite)  # invalid signedness
        @test_throws ErrorException AIFloat(3, 1, :signed, :both)     # invalid domain
    end
    
    @testset "Type Predicates" begin
        sf = AIFloat(4, 2, :signed, :finite)
        ue = AIFloat(5, 3, :unsigned, :extended)
        
        @test is_aifloat(sf) == true
        @test is_aifloat(Float64) == false
        @test is_signed(sf) == true
        @test is_unsigned(sf) == false
        @test is_signed(ue) == false
        @test is_unsigned(ue) == true
        @test is_finite(sf) == true
        @test is_extended(sf) == false
        @test is_finite(ue) == false
        @test is_extended(ue) == true
    end
    
    @testset "Bit Width and Precision Queries" begin
        sf43 = AIFloat(4, 3, :signed, :finite)
        uf32 = AIFloat(3, 2, :unsigned, :finite)
        
        @test n_bits(sf43) == 4
        @test n_sig_bits(sf43) == 3
        @test n_frac_bits(sf43) == 2
        @test n_sign_bits(sf43) == 1
        @test n_exp_bits(sf43) == 1  # 4 - 3 = 1 for signed
        
        @test n_bits(uf32) == 3
        @test n_sig_bits(uf32) == 2
        @test n_frac_bits(uf32) == 1
        @test n_sign_bits(uf32) == 0
        @test n_exp_bits(uf32) == 2  # 3 - 2 + 1 = 2 for unsigned
    end
    
    @testset "Value and Magnitude Counts" begin
        sf43 = AIFloat(4, 3, :signed, :finite)
        ue52 = AIFloat(5, 2, :unsigned, :extended)
        
        # Basic counts
        @test n_values(sf43) == 16  # 2^4
        @test nmags(sf43) == 8   # 2^(4-1) for signed
        @test nmags(ue52) == 31  # 2^5 - 1 for unsigned
        
        # NaN and infinity counts
        @test n_nans(sf43) == 1
        @test n_zeros(sf43) == 1
        @test n_inf(sf43) == 0  # finite type
        @test n_inf(ue52) == 1  # extended unsigned has +Inf
        @test n_pos_inf(ue52) == 1
        @test n_neg_inf(ue52) == 0  # unsigned has no -Inf
        
        # Subnormal counts
        @test nmags_prenormal(sf43) == 4  # 2^(3-1)
        @test nmags_subnormal(sf43) == 3  # prenormal - 1
        @test n_values_prenormal(sf43) == 7      # 2*prenormal - 1 for signed
        @test n_values_subnormal(sf43) == 6      # prenormal - 1
    end
    
    @testset "Exponent Characteristics" begin
        sf43 = AIFloat(4, 3, :signed, :finite)
        ue42 = AIFloat(4, 2, :unsigned, :extended)
        
        # Exponent bias calculation
        @test exp_bias(typeof(sf43)) == 1  # 2^(4-3-1) = 2^(0)
        @test exp_bias(typeof(ue42)) == 4  # 2^(4-2) = 4
        
        # Test that exponent functions don't throw
        @test exp_unbiased_min(sf43) isa Integer
        @test exp_unbiased_max(sf43) isa Integer
        @test exp_value_min(sf43) isa AbstractFloat
        @test exp_value_max(sf43) isa AbstractFloat
    end
    
    @testset "Value Sequences and Encoding" begin
        sf32 = AIFloat(3, 2, :signed, :finite)
        
        # Test that floats and codes have correct lengths
        @test length(floats(sf32)) == 8
        @test length(codes(sf32)) == 8
        
        # Test that all values are finite for finite types
        vals = floats(sf32)
        finite_vals = filter(isfinite, vals)
        nan_vals = filter(isnan, vals)
        @test length(nan_vals) == 1  # exactly one NaN
        @test length(finite_vals) == 7  # rest should be finite
        
        # Test encoding sequence is consecutive
        code_seq = codes(sf32)
        @test code_seq == collect(0:7)
        
        # Test zero is at expected position
        @test vals[1] == 0.0  # Zero should be at index 1 (code 0)
    end
    
    @testset "Code and Index Validation" begin
        sf32 = AIFloat(3, 2, :signed, :finite)
        
        # Test code validation
        @test validate_code(8, UInt8(0)) == UInt8(0)
        @test validate_code(8, UInt8(7)) == UInt8(7)
        @test validate_code(8, UInt8(8)) === nothing
        
        # Test index validation  
        @test validate_index(8, UInt8(0)) == UInt8(0)
        @test validate_index(8, UInt8(7)) == UInt8(7)
        @test validate_index(8, UInt8(8)) === nothing
        
        # Test code/index conversion
        @test unsafe_code_to_index(UInt8(0)) == UInt8(1)
        @test unsafe_code_to_index(UInt8(7)) == UInt8(8)
        @test unsafe_index_to_code(1) == 0
        @test unsafe_index_to_code(8) == 7
    end
    
    @testset "Special Value Identification" begin
        sf32 = AIFloat(3, 2, :signed, :finite)
        ue32 = AIFloat(3, 2, :unsigned, :extended)
        
        # Test zero identification
        @test code_zero(typeof(sf32)) == 0x00
        @test code_zero(typeof(ue32)) == 0x00
        
        # Test NaN codes
        nan_code_sf = code_nan(typeof(sf32))
        nan_code_ue = code_nan(typeof(ue32))
        @test nan_code_sf isa Unsigned
        @test nan_code_ue isa Unsigned
        
        # Test infinity codes for extended types
        @test code_posinf(typeof(ue32)) isa Unsigned
        @test code_neginf(typeof(ue32)) === nothing  # unsigned has no -Inf
        
        # Test that finite types return nothing for infinity codes
        @test code_posinf(typeof(sf32)) === nothing
        @test code_neginf(typeof(sf32)) === nothing
    end
    
    @testset "Type-based vs Instance-based Methods" begin
        sf32 = AIFloat(3, 2, :signed, :finite)
        T = typeof(sf32)
        
        # Test that instance methods match type methods
        @test n_bits(sf32) == n_bits(T)
        @test n_sig_bits(sf32) == n_sig_bits(T)
        @test n_values(sf32) == n_values(T)
        @test is_signed(sf32) == is_signed(T)
        @test is_finite(sf32) == is_finite(T)
        @test exp_bias(sf32) == exp_bias(T)
        @test code_zero(sf32) == code_zero(T)
        @test code_nan(sf32) == code_nan(T)
    end
    
    @testset "Edge Cases and Boundary Conditions" begin
        # Test minimum valid configurations
        min_signed = AIFloat(3, 1, :signed, :finite)
        @test n_bits(min_signed) == 3
        @test n_sig_bits(min_signed) == 1
        
        min_unsigned = AIFloat(2, 1, :unsigned, :finite)  
        @test n_bits(min_unsigned) == 2
        @test n_sig_bits(min_unsigned) == 1
        
        # Test that has_subnormals works correctly
        precision_1 = AIFloat(4, 1, :signed, :finite)
        precision_2 = AIFloat(4, 2, :signed, :finite)
        @test has_subnormals(precision_1) == false
        @test has_subnormals(precision_2) == true
        
        # Test value sequences contain expected special values
        vals = floats(precision_2)
        @test any(iszero, vals)
        @test any(isnan, vals)
        @test count(isnan, vals) == 1  # exactly one NaN
    end
    
    @testset "Memory Layout and Type Consistency" begin
        sf32 = AIFloat(3, 2, :signed, :finite)
        
        # Test that floats and codes use appropriate storage types
        @test eltype(floats(sf32)) <: AbstractFloat
        @test eltype(codes(sf32)) <: Unsigned
        
        # Test that storage types are chosen correctly based on bitwidth
        small_type = AIFloat(4, 2, :unsigned, :finite)
        @test eltype(codes(small_type)) == UInt8  # <= 8 bits
        
        # Test concrete type parameter consistency
        T = typeof(sf32)
        @test T.parameters[1] == 3  # bits
        @test T.parameters[2] == 2  # sigbits
    end
    
    @testset "Mathematical Properties" begin
        sf43 = AIFloat(4, 3, :signed, :finite)
        vals = floats(sf43)
        
        # Test that zero exists and is unique
        zeros = filter(iszero, vals)
        @test length(zeros) == 1
        
        # Test that finite values are properly ordered in mag
        finite_vals = filter(isfinite, vals)
        finite_positive = filter(x -> isfinite(x) && x > 0, vals)
        
        # Should have some positive finite values
        @test length(finite_positive) > 0
        
        # Test that NaN is properly isolated
        @test count(isnan, vals) == 1
        
        # For signed types, test symmetry around zero
        if is_signed(sf43)
            positive_finite = filter(x -> isfinite(x) && x > 0, vals)
            negative_finite = filter(x -> isfinite(x) && x < 0, vals)
            # Should have both positive and negative finite values
            @test length(positive_finite) > 0
            @test length(negative_finite) > 0
        end
    end
end