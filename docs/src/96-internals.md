# [Internal carriers](@id internals)

```@meta
CurrentModule = AIFloats
```

The exact rung-3 carrier and the pure-Julia `Float128` fused operations, vendored
from SmallFloats.jl (see the provenance headers in `src/carriers/`). Internal:
reach them as `AIFloats.Dyadic`, `AIFloats.fma128`, `AIFloats.faa128`. The
`DyadicNumbers` module is verified against golden digests captured from the
original (`test/support/dyadic_golden.sha256`).

```@autodocs
Modules = [AIFloats.DyadicNumbers, AIFloats.Float128FMA, AIFloats.Float128FAA]
```
