@testset "config seBinary8p4" begin
    config = config_floatml(8, 4, true, true)
    @test config.bits == 8
    @test config.precision == 4
    @test config.signed == true
    @test config.extended == false
    @test config.n_nans == 1
    @test config.n_zeros == 1
    @test config.n_infs == 1
    @test config.n_bits == 8
    @test config.n_significant_bits == 4
    @test config.n_fraction_bits == 3
    @test config.n_exponent_bits == 4
    @test config.n_sign_bits == 1
    @test config.n_values == 256    
end

#=
(bits = 8, precision = 4, signed = true, extended = true, 
 n_nans = 1, n_zeros = 1, n_infs = 2, 
 n_bits = 8, n_significant_bits = 4, n_fraction_bits = 3, n_exponent_bits = 4, n_sign_bits = 1, 
 n_values = 256, n_extended_values = 255, n_finite_values = 253, n_nonzero_finite_values = 252, 
 n_magnitudes = 126, n_fraction_magnitudes = 7, n_nonzero_fraction_magnitudes = 6, 
 n_fraction_values = 13, n_nonzero_fraction_values = 12, n_exponent_values = 16, 
 n_subnormal_values = 11, n_normal_values = 242, 
 n_subnormal_magnitudes = 5, n_normal_magnitudes = 121, 
 n_fraction_cycles = 9, n_exponent_cycles = 7, 
 exp_bias = 7, unbiased_exponent_min = -7, unbiased_exponent_max = 7, 
 exponent_min = 0.0078125, exponent_max = 128.0)
=#

@testset "config sfBinary8p4" begin
    config = config_floatml(8, 4, true, false)
    @test config.bits == 8
    @test config.precision == 4
    @test config.signed == true
    @test config.extended == false
    @test config.n_nans == 1
    @test config.n_zeros == 1
    @test config.n_infs == 1
    @test config.n_bits == 8
    @test config.n_significant_bits == 4
    @test config.n_fraction_bits == 3
    @test config.n_exponent_bits == 4
    @test config.n_sign_bits == 1
    @test config.n_values == 256    
end

@testset "config ueBinary5p3" begin
    config = config_floatml(8, 4, false, true)
    @test config.bits == 8
    @test config.precision == 4
    @test config.signed == true
    @test config.extended == false
    @test config.n_nans == 1
    @test config.n_zeros == 1
    @test config.n_infs == 1
    @test config.n_bits == 8
    @test config.n_significant_bits == 4
    @test config.n_fraction_bits == 3
    @test config.n_exponent_bits == 4
    @test config.n_sign_bits == 1
    @test config.n_values == 256    
end

@testset "config ufBinary5p3" begin
    config = config_floatml(5, 3, false, false)
    @test config.bits == 8
    @test config.precision == 4
    @test config.signed == true
    @test config.extended == false
    @test config.n_nans == 1
    @test config.n_zeros == 1
    @test config.n_infs == 1
    @test config.n_bits == 8
    @test config.n_significant_bits == 4
    @test config.n_fraction_bits == 3
    @test config.n_exponent_bits == 4
    @test config.n_sign_bits == 1
    @test config.n_values == 256    
end
