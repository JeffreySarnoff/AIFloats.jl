# P3109Reference

An independent, exact Julia conversion of `../Maude/`. The implementation uses
`Rational{BigInt}` for finite values, explicit exceptional values, and shared
scalar, scaled and block algorithms. It does not use the existing repository
Julia implementation or its documentation.

The 193 specification operations are available through `P3109Reference.SpecAPI`.
Their parameter order, operands and source clauses are listed in
[inventory/operations.tsv](inventory/operations.tsv). Thin adapters are generated;
the arithmetic, domain guards and symbolic reductions are handwritten.

## Run

From this directory, using Julia 1.13:

```sh
julia --startup-file=no --project=. -e 'using Pkg; Pkg.instantiate(; workspace=true); Pkg.test()'
julia --startup-file=no --project=. examples/core.jl
julia --startup-file=no --project=. examples/symbolic.jl
julia --startup-file=no --project=tools tools/run-cases.jl
julia --startup-file=no --project=tools tools/generate.jl --check
julia --startup-file=no --project=tools tools/audit.jl
julia --startup-file=no --project=benchmark benchmark/benchmarks.jl
```

The checked-in workspace manifest was resolved and tested on **1.13.0-rc4**.
Stable 1.13 validation remains a release follow-up. Package tests use the frozen
fixtures in this directory; they do not require Python, Maude or the sibling
source tree. The provenance audit and optional source recapture require that tree.

## Use

```julia
import P3109Reference as P

f = P.BinaryFormat(4, 2, P.SIGNED, P.FINITE)
p = P.Projection(P.NEAREST_EVEN)
x = P.finite(3 // 2)
@assert P.encode(f, x) == 5
@assert P.decode(f, 5) == x
@assert P.SpecAPI.Add(f, f, f, p, 4, 4) == 6

random_rounding = P.RoundPolicy(P.STOCHASTIC_A, 3, 5)
random_projection = P.Projection(random_rounding, P.SAT_NONE)
code = P.project(f, random_projection, P.finite(5 // 4))
```

Codes and format parameters are exact integers. A format stores width,
precision, signedness and finite/extended domain at runtime. There is one zero
and one NaN; this carrier does not model IEEE signed zero or NaN payloads.
`finite` accepts integers and rationals, deliberately avoiding implicit binary
floating-point approximations. `encode` requires a representable datum;
`project` performs rounding, saturation and encoding.

All nine rounding modes take their randomness explicitly. `STOCHASTIC_A`,
`STOCHASTIC_B` and `STOCHASTIC_C` correspond to source `StochasticA/B/C`.
The six deterministic modes are `NEAREST_EVEN`, `NEAREST_AWAY`, `UP`, `DOWN`,
`TO_ZERO`, `TO_ODD`; saturation is `SAT_NONE`, `SAT_FINITE`, `SAT_PROPAGATE`.
No operation samples an RNG. A block policy receives one random integer per
element, in sequence order. Public block positions are zero-based where the
source has an explicit position argument; ordinary Julia storage is not.

Constructors reject invalid formats and policies. Invalid codes and datums
raise `DomainError`; invalid sizes raise `ArgumentError` or `DimensionMismatch`.
Valid but undecidable symbolic/backend applications return a `Residual` or
`UNKNOWN`, retaining the distinction from false and NaN. See
[API and architecture](api.md) for these boundaries.

## Evidence

The frozen corpus contains **347,580 assertions**: 67,541 core, 194 symbolic,
279,840 exhaustive ordering and five current standalone assertions. Four stale
standalone assertions were removed at the user's request and are not ported.
The package also has 902 interface, boundary and tooling checks.

[checkpoint.md](checkpoint.md) records progress and actual gate results;
[evidence/reviews.md](evidence/reviews.md) records review findings.
[evidence/obligations.md](evidence/obligations.md) preserves the distinction
between finite test evidence, historical Maude proofs and open universal claims.
External concrete codecs and certified irrational projection remain absent,
as in the source. This package is an executable reference, not a claim that a
separate floating-point implementation conforms to the standard.

Planning and execution are governed by [improvedconversion.md](improvedconversion.md),
[conversionplan.md](conversionplan.md) and [conversionactions.md](conversionactions.md).
