# scalar suite: the datum-at-a-time paths — codec, projection, the operation
# engine at each carrier rung, the construction seam, and the Base veneers.

section("scalar — codec and projection")

const T8  = binary8p4se                      # rung 1, UInt8 code, table decode
const T12 = BinaryValue(Binary(12, 6, SIGNED, EXTENDED))   # rung 1, UInt16 code
const T16 = BinaryValue(Binary(16, 4, SIGNED, EXTENDED))   # rung 2, Float128 carrier
const F8, F12, F16 = BinaryFormatOf(T8), BinaryFormatOf(T12), BinaryFormatOf(T16)

let x8 = T8(1.5), x12 = T12(1.5), x16 = T16(1.5)
    row("decode K=8 (generated table)",  @b decode($x8))
    row("decode K=12 (computed)",        @b decode($x12))
    row("decode K=16 (rung 2)",          @b decode($x16))
    row("codepoint",                     @b codepoint($x8))
    row("project Float64 → K=8",         @b AIFloats.project($F8, RTE_SN, 1.3))
    row("project Float64 → K=12",        @b AIFloats.project($F12, RTE_SN, 1.3))
    row("project Float64 → K=8 RTZ_SF",  @b AIFloats.project($F8, RTZ_SF, 1e30))
    row("project Float64 → K=8 RSA_SN",  @b AIFloats.project($F8, RSA_SN, 1.3; R = 7))
    q = decode(x16)
    row("project Float128 → K=16",       @b AIFloats.project($F16, RTE_SN, $q))
    row("binary128 → exact Dyadic",      @b AIFloats._dyadic128($q))
    row("binary128 exact Float64 accept",@b AIFloats._try_f64_exact($q))
    qwide = decode(MaxFiniteOf(T16))
    row("binary128 exact Float64 refuse",@b AIFloats._try_f64_exact($qwide))
    row("order_key",                     @b AIFloats.order_key($x8))
    row("NextGreaterThan",               @b NextGreaterThan($x8))
    row("Class",                         @b Class($x8))
end

section("scalar — construction")

row("T8(1.3)      (Float64 value)",     @b T8(1.3))
row("T8(1.3f0)    (Float32 value)",     @b T8(1.3f0))
row("T8(3)        (Integer value)",     @b T8(3))
row("convert(T8, 1.3)",                 @b convert(T8, 1.3))
row("T8(0x05)     (code point)",        @b T8(0x05))
row("Convert(F8, RTE_SN, 1.3)",         @b Convert($F8, RTE_SN, 1.3))

section("scalar — operations by registry group, K=8")

let x = T8(1.5), y = T8(0.25), z = T8(0.75)
    row("Add       explicit ρ",         @b Add($F8, RTE_SN, $x, $y))
    row("Add       session default ρ",  @b Add($x, $y))
    row("Subtract  explicit ρ",         @b Subtract($F8, RTE_SN, $x, $y))
    row("Multiply  explicit ρ",         @b Multiply($F8, RTE_SN, $x, $y))
    row("Divide    explicit ρ",         @b Divide($F8, RTE_SN, $x, $y))
    row("FMA       explicit ρ",         @b FMA($F8, RTE_SN, $x, $y, $z))
    row("FAA       explicit ρ",         @b FAA($F8, RTE_SN, $x, $y, $z))
    row("Sqrt      explicit ρ",         @b Sqrt($F8, RTE_SN, $x))
    row("Exp       explicit ρ",         @b Exp($F8, RTE_SN, $x))
    row("Exp2      explicit ρ",         @b Exp2($F8, RTE_SN, $x))
    row("Log       explicit ρ",         @b Log($F8, RTE_SN, $x))
    row("Log2      explicit ρ",         @b Log2($F8, RTE_SN, $x))
    row("Sin       explicit ρ",         @b Sin($F8, RTE_SN, $x))
    row("Tanh      explicit ρ",         @b Tanh($F8, RTE_SN, $x))
    row("ArcTan2Pi explicit ρ",         @b ArcTan2Pi($F8, RTE_SN, $x, $y))
    row("Maximum   explicit ρ",         @b Maximum($F8, RTE_SN, $x, $y))
    row("Convert   K=8 → K=12",         @b Convert($F12, RTE_SN, $x))
    row("Add       RSA_SN (stochastic)",@b Add($F8, RSA_SN, $x, $y; R = 3))
    withflags(fast_arith = false) do
        Add(F8, RTE_SN, x, y)
        row("Add       FAST_ARITH=false",  @b Add($F8, RTE_SN, $x, $y))
    end
    withflags(fast_enclosure = false) do
        Exp(F8, RTE_SN, x)
        row("Exp       FAST_ENCLOSURE=false", @b Exp($F8, RTE_SN, $x))
    end
end

section("scalar — operations, K=12 and K=16")

let x12 = T12(1.5), y12 = T12(0.25), z12 = T12(0.75), x16 = T16(1.5), y16 = T16(0.25)
    row("Add       K=12",               @b Add($F12, RTE_SN, $x12, $y12))
    row("Multiply  K=12",               @b Multiply($F12, RTE_SN, $x12, $y12))
    row("FMA       K=12",               @b FMA($F12, RTE_SN, $x12, $y12, $z12))
    row("Exp       K=12",               @b Exp($F12, RTE_SN, $x12))
    row("Log       K=12",               @b Log($F12, RTE_SN, $x12))
    row("Add       K=16 (rung 2)",      @b Add($F16, RTE_SN, $x16, $y16))
    row("Multiply  K=16 (rung 2)",      @b Multiply($F16, RTE_SN, $x16, $y16))
    row("Exp       K=16 (rung 2)",      @b Exp($F16, RTE_SN, $x16))
end

section("scalar — Base veneers")

let x = T8(1.5), y = T8(0.25), z = T8(0.75)
    row("x + y",                        @b $x + $y)
    row("x * y",                        @b $x * $y)
    row("fma(x, y, z)",                 @b fma($x, $y, $z))
    row("exp(x)",                       @b exp($x))
    row("log(x)",                       @b log($x))
    row("x < y",                        @b $x < $y)
    row("Float64(x)",                   @b Float64($x))
    row("BigFloat(x)",                  @b BigFloat($x))
    row("round(x)",                     @b round($x))
    row("floor(x)",                     @b floor($x))
    row("ceil(x)",                      @b ceil($x))
    row("trunc(x)",                     @b trunc($x))
    row("round(x, RoundUp)",            @b round($x, RoundUp))
    row("eps(x)",                       @b eps($x))
    row("hash(x)",                      @b hash($x))
    row("rand(T8)",                     @b rand($T8))
end
