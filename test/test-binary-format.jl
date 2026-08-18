using AIFloats
using Test

@testset "Binary format" begin
    f = AIFloats.format(16, 10, SIGNED, FINITE)
    b = AIFloats.binary(16, 10, UNSIGNED, EXTENDED)
      
    @testset "Format" begin
        @test f isa AIFloats.Format
        @test f.K == Int8(16)
        @test f.P == Int8(10)
        @test f.S == true
        @test f.D == false

        @test AIFloats.format_fields(16, 10, SIGNED, FINITE) == (Int8(16), Int8(10), true, false)
        @test AIFloats.format_fields(16, 10, true, false) == (Int8(16), Int8(10), true, false)
    end

    @testset "Binary" begin
        @test b isa AIFloats.Binary{16, 10, false, true}
        @test AIFloats.BitwidthOf(b) == 16
        @test AIFloats.PrecisionOf(b) == 10
        @test AIFloats.SignednessOf(b) == false
        @test AIFloats.DomainOf(b) == true
    end

    @testset "Binary Format" begin
        @test AIFloats.FormatOf(b) == AIFloats.Format(Int8(16), Int8(10), false, true)
        @test AIFloats.BinaryOf(f) == AIFloats.Binary{Int(f.K), Int(f.P), f.S, f.D}()

        io = IOBuffer()
        show(io, MIME("text/plain"), b)
        @test String(take!(io)) == "Binary{16, 10, false, true}"

        io = IOBuffer()
        show(io, MIME("text/plain"), f)
        @test String(take!(io)) == "Format(16, 10, true, false)"
    end
end
