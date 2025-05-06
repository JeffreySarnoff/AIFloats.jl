module TestAbsUnsignedAIFloat

using FloatsForML, Test

include(s"C:\github\FloatsForML.jl\test\test_abstypes\test_inits.jl")

using .TestInits

@testset "AbsUnsignedAIFloat{4|5,_}" begin
    for T ∈ vcat(auai4s, auai5s)
        bits = T.parameters[1]
        sigbits = T.parameters[2]
        isSigned = is_signed(T)
        isUnsigned = is_unsigned(T)

        @test nSignBits(T) == ifelse(isSigned, 1, 0)
        @test nExpBits(T) == ifelse(isUnsigned, (bits - sigbits + 1), (bits - sigbits))
        @test nMagnitudes(T) ==
              ifelse(isUnsigned, nNumericValues(T), nNumericValues(T) >> 1)
        @test nNonzeroMagnitudes(T) == nMagnitudes(T) - 1
        @test nPositiveValues(T) == nNonzeroMagnitudes(T)
        @test nNegativeValues(T) == ifelse(isUnsigned, 0, nPositiveValues(T))
        @test nExpValues(T) == 2^nExpBits(T)
        @test nNonzeroExpValues(T) == nExpValues(T) - 1
    end
end

end # module TestAbsUnsignedAIFloat
