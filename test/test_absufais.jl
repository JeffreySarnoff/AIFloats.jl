module TestAbsUnsignedFiniteAIFloat

using FloatsForML, Test

include(s"C:\github\FloatsForML.jl\test\test_inits.jl")

using .TestInits

@testset "AbsUnsignedFiniteAIFloat{4|5,_}" begin
    for T ∈ vcat(aufai4s, aufai5s)
        bits = T.parameters[1]
        sigbits = T.parameters[2]
        isSigned = is_signed(T)
        isUnsigned = is_unsigned(T)
        isFinite = is_finite(T)
        isExtended = is_extended(T)

        @test nInfs(T) == ifelse(isExtended, (isSigned ? 2 : 1), 0)
        @test nPosInfs(T) == ifelse(isExtended, 1, 0)
        @test nNegInfs(T) == ifelse(isExtended, (isSigned ? 1 : 0), 0)
        @test nFiniteValues(T) == nNumericValues(T) - nInfs(T)
        @test nNonzeroFiniteValues(T) == nFiniteValues(T) - 1
        @test nPositiveFiniteValues(T) == nFiniteValues(T) >> (0 + is_signed(T))
        @test nNegativeFiniteValues(T) == ifelse(is_unsigned(T), 0, nPositiveFiniteValues(T))
    end
end

end # module TestAbsUnsignedFiniteAIFloat
