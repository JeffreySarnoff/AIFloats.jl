import P3109Reference as P

@assert P.Symbolic.elementary(:Sqrt, P.finite(9//16))==P.finite(3//4)
@assert P.Symbolic.elementary(:Sqrt, P.finite(2)) isa P.Symbolic.SymbolicExpr
@assert P.divide(P.atan2_value(P.finite(1), P.finite(-1)), P.PI)==P.finite(3//4)
@assert P.Symbolic.elementary(:TanPi, P.finite(-1//2))===P.NEG_INF
@assert P.mathematical_equal(
    P.Symbolic.expression(:Exp, P.finite(1)),
    P.Symbolic.expression(:Exp, P.finite(2)),
)===P.UNKNOWN
println("PASS five symbolic examples")
