module TestAbstractAI

using FloatsForML, Test

include("test_inits.jl")
using .TestInits

@testset "AbstractAIFloat{4,_}" begin
    for T ∈ aai4s
        bits = T.parameters[1]
        sigbits = T.parameters[2]

        @test nBits(T) == bits
        @test nSigBits(T) == sigbits
        @test nFracBits(T) == sigbits - 1
        @test nValues(T) == 2^bits
        @test nNumericValues(T) == nValues(T) - 1
        @test nNonzeroNumericValues(T) == nNumericValues(T) - 1
        @test nFracMagnitudes(T) == 2^nFracBits(T)
        @test nNonzeroFracMagnitudes(T) == nFracMagnitudes(T) - 1
    end
end

@testset "AbstractAIFloat{5,_}" begin
    for T ∈ aai5s
        bits = T.parameters[1]
        sigbits = T.parameters[2]

        @test nBits(T) == bits
        @test nSigBits(T) == sigbits
        @test nFracBits(T) == sigbits - 1
        @test nValues(T) == 2^bits
        @test nNumericValues(T) == nValues(T) - 1
        @test nNonzeroNumericValues(T) == nNumericValues(T) - 1
        @test nFracMagnitudes(T) == 2^nFracBits(T)
        @test nNonzeroFracMagnitudes(T) == nFracMagnitudes(T) - 1
    end
end

end # module TestAbstractAI
