"""
    AIFloats

Small binary floating-point formats for machine learning, following IEEE P3109.

A format is completely determined by four parameters — bitwidth, precision, signedness, and
domain — and [`Binary`](@ref) is the specifier that carries them. A member of a format's
value set is a [`BinaryValue`](@ref) datum, stored as its code point. [`Projection`](@ref)
names the rounding and saturation choice that maps a real onto a format's values.

Implemented today: the format layer; datums and the code ⇆ value codec; the
projection engine (`project` — the single write path, every rounding and saturation
mode); and the draft's operation register (`Add` … `Convert`, correctly rounded via
exact evaluation or interval enclosure); array kernels and memoized tables; and
the Base surface (`+`, `sort`, `round`, promotion, the `AbstractFloat` contract);
blocks ([`Block`](@ref), [`BlockVector`](@ref), the `Block*`/`Scaled*` operations)
and packed storage ([`PackedVector`](@ref)). See the documentation's status page.
"""
module AIFloats

export BinaryFloat, Binary,
# Binary format signedness
ΣBool, UNSIGNED, SIGNED, is_unsigned, is_signed,
# Binary  format domain
ΔBool, FINITE, EXTENDED, is_finite, is_extended,
# rounding modes
RTE, RTA, RTP, RTN, RTZ, RTO, RSA, RSB, RSC,
# saturation modes
SF, SP, SN,
# projection functions
Projection, RoundOf, SatOf,
# projections
RTE_SF, RTE_SP, RTE_SN, RTA_SF, RTA_SP, RTA_SN, RTP_SF, RTP_SP, RTP_SN, RTN_SF, RTN_SP, RTN_SN, RTZ_SF, RTZ_SP, RTZ_SN, RTO_SF, RTO_SP, RTO_SN, RSA_SF, RSA_SP, RSA_SN, RSB_SF, RSB_SP, RSB_SN, RSC_SF, RSC_SP, RSC_SN,
# Binary format API
BitwidthOf, PrecisionOf, SignednessOf, DomainOf,
ExponentBiasOf, ExponentBitwidthOf, TrailingSignificantBitsOf,
# stochastic-mode queries
isstochastic, nrandbits,
# the datum type and its codec (codepoint extends Base.codepoint)
BinaryValue, BinaryFormatOf, decode, formatname,
# special-value accessors
MaxFiniteOf, MinFiniteOf, MinPositiveOf, MaxSubnormalOf, MinNormalOf,
# classification and neighbors
Class, FPClass,
ClassNaN, ClassNegInf, ClassNegNormal, ClassNegSubnormal, ClassZero,
ClassPosSubnormal, ClassPosNormal, ClassPosInf,
NextGreaterThan, NextLessThan,
# datum display
VALID_SHOW_STYLES, set_show_style!, get_show_style,
# format enumeration
codetable, printcodetable,
# the projection engine
project,
# blocks and packed storage
Block, BlockVector, blocksize, scaleformat, elemformat,
BlockReduceAdd, BlockReduceMultiply, BlockDotProduct,
ConvertFromBlock, ConvertToBlock, ConvertToBlockMaxAbsFinite,
PackedVector, packing_saves,
# governance: conformance and the κ registry
conformance, conformance_dict, conformance_report, draft_revision, draft_identity,
measure_kappa, register_approx!, unregister_approx!, approx, list_approx, kappa, kappa_measured,
ftz_variant,
# session defaults
DefaultProjection, DefaultProjection!,
DefaultRoundingMode, DefaultRoundingMode!,
DefaultSaturationMode, DefaultSaturationMode!,
# external types (IEEE 754, bfloat16)
binary16, binary32, binary64, binary128, bfloat16,
# dual use constants: both implementation-facing and user-facing
IntParam,
CodeType, ValueType

# published, must be imported explicitly
public resolve_fields, rawvalue, encode, order_key,
       nan_code, posinf_code, neginf_code, codemask, signmask, orderkeytype,
       rung, datumcarrier, promotecarrier, decodepolicy, Formats, CodeCountingSort,
       Dyadic, DyadicNumbers, lift, CarrierValue, fma128, faa128, Sticky, Enclosure,
       FAST_ARITH, FAST_ENCLOSURE,
       round_to_precision, saturate, project_interval, bigprec,
       blockdecode, blockproject, PACK_TILE, codedistance, ApproxImpl, ConformanceDeclaration,
       get_table, table_for, table_policy,
       table_bytes, table_count, table_keys, empty_tables!

# working with other Julia packages
using Quadmath
using BFloat16s
using Random: Random
using PrecompileTools: @setup_workload, @compile_workload

# internal organization — include order is load-bearing and is stated in
# docs/structuralplan.md §7; changing it means changing that section too
include("carriers/dyadic.jl")      # first: zero package dependencies
include("carriers/fma128.jl")
include("carriers/faa128.jl")
using .DyadicNumbers: Dyadic, DyadicNumbers,
                      # the exact accumulator used by the block reductions
                      add_dy, mul_dy, nbits_dy, DYADIC_ZERO, DYADIC_ONE, DYADIC_ALIGN_MAX
using .Float128FMA: fma128
using .Float128FAA: faa128
include("types/constants.jl")
include("types/external.jl")
include("types/singletons.jl")
include("types/binaryformats.jl")
include("types/traits.jl")
include("carriers/heads.jl")
include("types/binaryvalue.jl")
include("content/codepoints.jl")
include("compat/show.jl")          # early: error paths may print datums
include("content/floatvalues.jl")
include("content/datums.jl")
include("carriers/bigprec.jl")
include("projection/rounded.jl")
include("projection/round.jl")
include("projection/saturate.jl")
include("projection/project.jl")
include("rules/constraints.jl")    # the alias grid; validity stays in validformat
include("rules/defaults.jl")       # before ops: consumed by generated methods
include("ops/registry.jl")
include("ops/oracle.jl")
include("ops/scalar.jl")
include("tables/cache.jl")
include("tables/policy.jl")
include("tables/build.jl")
include("arrays/kernels.jl")
include("arrays/blocks.jl")
include("arrays/packed.jl")
include("compat/base.jl")          # Base veneers, order, AbstractFloat contract, promotion
include("arrays/broadcast.jl")     # after compat/base.jl: reads its veneer tables
include("compat/rand.jl")
include("content/gentables.jl")
include("rules/conformance.jl")
include("rules/approx.jl")

# the K ≤ 8 half of the alias grid is exported; the rest are reachable
# qualified or via `using AIFloats.Formats`
for n in sort!(collect(keys(_NAMED)))
    Int(BitwidthOf(_NAMED[n])) <= 8 && @eval export $n
end

# ---- precompile workload: the standard profile's hot entries compile during
# precompilation; everything else specializes lazily. One wide format per rung
# above 1 — a second format at the same rung compiles the same methods again
# for a different type parameter and buys nothing.
@setup_workload begin
    @compile_workload begin
        T = binary8p4se; S = binary8p3se
        a, b = T(1.5), T(0.25)
        Add(T, RTE_SN, a, b); Multiply(T, RTE_SF, a, b)
        Exp(T, RTE_SN, a); Convert(S, RTE_SN, a)
        a + b; exp(b); fma(a, b, a); min(a, b); a < b; round(a); eps(a)
        # the value constructors: T(::Float64) is the single most common entry
        # point and was 15 ms of first-call latency uncompiled
        T(1.3); T(1.3f0); T(3); convert(T, 1.3)
        # one Group B ladder row — the enclosure machinery is shared, and Log
        # alone was ~103 ms cold
        Log(T, RTE_SN, a); log(a)
        get_table(:Exp, BinaryFormatOf(T), BinaryFormatOf(T), RTE_SN)
        A = [a, b, a, b]; B = [b, a, b, a]; d = similar(A)
        vmap!(d, Val(:Add), RTE_SN, A, B)
        vmap!(d, Val(:Exp), RTE_SN, A)
        sort!(copy(A))
        # the broadcast route (arrays/broadcast.jl): binary, unary, and the
        # in-place form all land in distinct copyto! methods
        A .+ B; exp.(A); d .= A .+ B
        ScaledAdd(T, RTE_SN, one(S), a, one(S), b)
        bx = Block(one(S), (a, b, a, b)); by = Block(one(S), (b, a, b, a))
        BlockDotProduct(T, RTE_SN, bx, by)
        BlockAdd(T, RTE_SN, bx, by, one(S))
        BlockReduceAdd(T, RTE_SN, bx)          # the Dyadic accumulator path
        # Block{B} specializes on B — precompiling B = 4 does nothing for a
        # B = 16 caller. Cover the two MX-standard block sizes; anything else
        # a caller picks compiles on first use, as it must.
        for BSZ in (16, 32)
            m = Block(one(S), ntuple(_ -> a, BSZ))
            n = Block(one(S), ntuple(_ -> b, BSZ))
            BlockReduceAdd(T, RTE_SN, m); BlockDotProduct(T, RTE_SN, m, n)
        end
        collect(PackedVector(A))
        for WF in (binary16p5se, binary16p1uf)          # rung 2, rung 3
            w1 = WF(1.5); w2 = WF(0.25)
            Add(WF, RTE_SN, w1, w2); Multiply(WF, RTE_SF, w1, w2)
            Exp(WF, RTE_SN, w1); Convert(T, RTE_SN, w1)
            decode(w1); codepoint(w1); w1 < w2
        end
        empty_tables!()
    end
end

end

# AIFloats.jl
