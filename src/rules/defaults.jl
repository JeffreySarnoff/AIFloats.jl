# the task-local default projection — ONE source of dynamic truth, task-local
#
# A `Ref` was wrong for this, and not merely unfashionable: a projection
# CHANGES NUMERIC RESULTS, so two tasks that want different rounding cannot
# share one. `ScopedValue` binds for a dynamic extent, restores on normal
# return and on exception, nests, and follows Julia's inheritance rules for
# child tasks. There are no setters: a persistent process-wide setter is
# incompatible with a reliable task-local default (improveapi3.md §4.3).
#
# Performance-policy controls (FAST_ARITH, FAST_ENCLOSURE, the table budgets)
# stay process-wide `Ref`s on purpose. They select an implementation strategy
# rather than a result, and they are read on hot paths where a scoped lookup
# would cost more than it is worth. Display keeps its own two-level scheme:
# an `IOContext` property is the local override, `DEFAULT_SHOW_STYLE` only the
# process-wide fallback, because display context travels with `IO` rather than
# with task scope. See §4.3.1.

using Base.ScopedValues: ScopedValue, with

# The abstract parameter is REQUIRED. `ScopedValue(RTE_SN)` would infer
# `ScopedValue{Projection{typeof(RTE),typeof(SN)}}` and then reject every other
# projection at bind time.
const _DEFAULT_PROJECTION = ScopedValue{Projection}(RTE_SN)

"""
    DefaultProjection() -> Projection

The task's default [`Projection`](@ref), consumed by the same-format
convenience methods and by the value constructors. `RTE_SN` unless a
[`with_projection`](@ref) block is in dynamic extent.

Coherent with [`DefaultRoundingMode`](@ref) and [`DefaultSaturationMode`](@ref)
by construction: both derive from this one value, so they cannot be read torn
or set inconsistently.

# Examples

```jldoctest
julia> DefaultProjection()
ρ(RTE, SN)

julia> with_projection(RTZ_SF) do
           DefaultProjection()
       end
ρ(RTZ, SF)

julia> DefaultProjection()          # restored on exit
ρ(RTE, SN)
```
"""
DefaultProjection() = _DEFAULT_PROJECTION[]

"""
    with_projection(f, ρ::Projection)
    with_projection(f, μ::RoundingMode, σ::SaturationMode)

Run `f()` with `ρ` as the task's default projection, restoring the previous
value on return **and on exception**. Blocks nest, and a task started inside
one inherits the binding.

This replaces the former `DefaultProjection!` setters. The change is not
cosmetic: a projection changes numeric results, so a process-wide setter makes
two concurrently running tasks silently fight over what arithmetic means.

The convenience seam it feeds costs one dynamic dispatch for a non-`RTE_SN`
projection. Where that matters, pass the projection explicitly — `Add(F, ρ, x, y)`
never reads this value at all.

# Examples

```jldoctest
julia> F = Binary8p4se;

julia> with_projection(RTZ_SN) do
           F(1.35)
       end
1.25

julia> F(1.35)                      # the unscoped default rounds to nearest
1.375
```
"""
with_projection(f, ρ::Projection) = with(f, _DEFAULT_PROJECTION => ρ)
with_projection(f, μ::RoundingMode, σ::SaturationMode) =
    with_projection(f, Projection(μ, σ))

"""
    DefaultRoundingMode() -> RoundingMode

The rounding half of [`DefaultProjection`](@ref), derived from it.
"""
DefaultRoundingMode() = RoundOf(DefaultProjection())

"""
    DefaultSaturationMode() -> SaturationMode

The saturation half of [`DefaultProjection`](@ref), derived from it.
"""
DefaultSaturationMode() = SatOf(DefaultProjection())
