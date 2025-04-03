using FloatsForML, Test

include("config.jl")

BF32 = BaseFloat(3, 2);

@test typeof(encoding(BF32)[1]) == UInt8
@test typeof(values(BF32)[1]) == Float32

@test encoding(BF32) == [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07]
@test values(BF32) == [0.0, 0.25, 0.5, 0.75, 1.0, 1.5, 2.0, 3.0]

BF98 = BaseFloat(9, 8);

@test typeof(encoding(BF98)[1]) == UInt16
@test typeof(values(BF98)[1]) == Float64

