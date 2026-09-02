# [Dyadic Numbers](@id dyadic-numbers)

```@meta
CurrentModule = AIFloats
```

!!! warning "Unstable — not part of the public interface"
    Everything on this page is implementation detail. Names, types, and behavior may
    change in any release without a deprecation, and nothing here is covered by the
    package's contract. The supported surface is the [Reference](@ref reference); use
    [`decode`](@ref), the register operations, and [`project`](@ref) rather than
    depending on a particular carrier.

`AIFloats.Dyadic` is the exact carrier: an exact dyadic rational `S · 2^Q` in an
`Int128` significand, together with the three non-finite rows. Every datum of every
P3109 format is exactly `S · 2^Q` with `|S| < 2^16`, so arithmetic over datums is
closed and exact here and allocation-free — MPFR buys nothing for it. Transcendental
fallbacks still escalate to MPFR through an exact `BigFloat` image.

It is the carrier of the widest **rung**, above `Float64` and `Float128`. Which rung a
format uses follows from its exponent span rather than its storage width; see
[Algorithms](@ref alg-enclosure) for where the carriers sit in the evaluation path.

`Dyadic <: Real`, deliberately **not** `<: AbstractFloat`. Methods elsewhere written
`::AbstractFloat` mean "a float carrier", and `Dyadic` implements about ten operations
rather than the full `AbstractFloat` obligation. `AIFloats.promotecarrier` targets
`BigFloat`, never this type.

The exact fixed-point accumulator behind the block reductions is this type, and its
alignment band — `DYADIC_ALIGN_MAX`, 94 bits — is what makes the
[sticky protocol](@ref alg-sticky) sound: a tail discarded past that band lies below
every rounding threshold in play, so recording its direction loses nothing.

Vendored from SmallFloats.jl, with the provenance headers in `src/carriers/dyadic.jl`,
and verified against golden digests captured from the original
(`test/support/dyadic_golden.sha256`).

```@autodocs
Modules = [AIFloats.DyadicNumbers]
```
