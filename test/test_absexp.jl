module TestAbsExp

using AIFloats, Test

include("test_inits.jl")
using .TestInits

@testset "AbsExpAIFloat{4,_}" begin

    for T ∈ aeai4s
        bits = T.parameters[1]
        sigbits = T.parameters[2
        isSigned = is_signed(T)
        isUnsigned = is_unsigned(T)
]


        @test nBits(T) == bits
        @test nSigBits(T) == sigbits
        @test nExpBits(T) == bits - sigbits - 1
        @test nValues(T) == 2^bits
        @test nNumericValues(T) == nValues(T) - 1
        @test nNonzeroNumericValues(T) == nNumericValues(T) - 1
    end
end

end # module TestAbsExp
