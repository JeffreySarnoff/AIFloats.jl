using P3109Reference: BinaryFormat, Projection, SpecAPI, finite
import P3109Reference as P

f4=BinaryFormat(4, 2, P.SIGNED, P.FINITE)
f8=BinaryFormat(8, 4, P.SIGNED, P.EXTENDED)
policy=Projection(P.NEAREST_EVEN)
@assert SpecAPI.Convert(f8, f4, policy, 72)==6
@assert P.fused_multiply_add(finite(3//2), finite(3//2), finite(-1//4))==finite(2)
@assert P.project_elements(
    f4,
    P.BlockProjection(P.NEAREST_EVEN),
    [P.POS_INF, finite(-2)];
    scale = P.POS_INF,
)==[4, 12]
println("PASS three core examples")
