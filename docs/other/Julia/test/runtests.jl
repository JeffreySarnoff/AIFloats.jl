using Test: Test, @test, @testset, @test_throws, @inferred
using JSON: JSON
import P3109Reference as P
include("support/source_cases.jl")

@testset "Source parity" begin
    for suite in (
        "smoke",
        "domains",
        "codec",
        "projection",
        "scalar",
        "order-next",
        "blocks",
        "conformance",
        "symbolic",
        "order-full",
        "standalone",
    )
        @testset "$suite" begin
            result=SourceCases.run_suite(suite)
            if !isempty(result.failures)
                println(join(first(result.failures, min(10, length(result.failures))), "\n"))
            end
            @test isempty(result.failures)
            @test result.count > 0
            println("$suite: $(result.count) source cases checked")
        end
    end
end

include("test_interfaces.jl")
