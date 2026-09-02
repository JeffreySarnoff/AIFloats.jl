# [Internal carriers](@id internals)

```@meta
CurrentModule = AIFloats
```

!!! warning "Unstable — not part of the public interface"
    Everything on this page is implementation detail. Names, types, and behavior may
    change in any release without a deprecation, and nothing here is covered by the
    package's contract. The supported surface is the [Reference](@ref reference); use
    [`decode`](@ref), the register operations, and [`project`](@ref) rather than
    depending on a particular carrier or rung.

The exact rung-3 carrier and the pure-Julia `Float128` fused operations, vendored
from SmallFloats.jl (provenance headers in `src/carriers/`). Reach them as
`AIFloats.Dyadic`, `AIFloats.fma128`, `AIFloats.faa128`.

Which carrier a format uses is its **rung**, chosen from the format's exponent span
rather than its storage width. `Dyadic` is the exact fixed-point carrier above the
`Float64` and `Float128` rungs; it is `<: Real` and deliberately not `<: AbstractFloat`.
The `DyadicNumbers` module is verified against golden digests captured from the original
(`test/support/dyadic_golden.sha256`).

`Quadmath.Float128` appears here as a value carrier only. libquadmath's elementary
functions are **not** assumed to be correctly rounded; a fast result is accepted only
under a proof or a two-sided enclosure check, and otherwise the operation escalates to
the rigorous MPFR ladder. `fma128` and `faa128` are pure Julia and carry their own
documented guarantees.

```@autodocs
Modules = [AIFloats.DyadicNumbers, AIFloats.Float128FMA, AIFloats.Float128FAA]
```
