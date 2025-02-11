using FloatsForML, Test

SF32 = MLFloats(3, 2, IsSigned, IsFinite)
UF32 = MLFloats(3, 2, IsUnsigned, IsFinite)

SE53 = MLFloats(5, 3, IsSigned, IsExtended)
UE53 = MLFloats(5, 3, IsUnsigned, IsExtended)

SF96 = MLFloats(9, 6, IsSigned, IsFinite)
UF96 = MLFloats(9, 6, IsUnsigned, IsFinite)

SE96 = MLFloats(9, 6, IsSigned, IsExtended)
UE96 = MLFloats(9, 6, IsUnsigned, IsExtended)

@test isaligned(floats(SF32), 64)
@test isaligned(floats(UF32), 64)
@test isaligned(floats(SE53), 64)
@test isaligned(floats(UE53), 64)

@test isaligned(floats(SF96), 64)
@test isaligned(floats(UF96), 64)
@test isaligned(floats(SE96), 64)
@test isaligned(floats(UE96), 64)

@test isaligned(codes(SF32), 64)
@test isaligned(codes(UF32), 64)
@test isaligned(codes(SE53), 64)
@test isaligned(codes(UE53), 64)

@test isaligned(codes(SF96), 64)
@test isaligned(codes(UF96), 64)
@test isaligned(codes(SE96), 64)
@test isaligned(codes(UE96), 64)
