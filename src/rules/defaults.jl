# session defaults — plain Refs, process-global
#
# Not ScopedValue, not task-local: set defaults from one task, not
# concurrently. The projection setters are COUPLED both ways: setting a
# component rebuilds the projection from it and the other component's current
# value; setting the projection decomposes it back — so
# DefaultProjection() === Projection(DefaultRoundingMode(), DefaultSaturationMode())
# after any setter, and a consumer reads ONE Ref, never two (a torn read
# across two component Refs is the hazard the coupling exists to prevent).

const _DEFAULT_PROJECTION = Ref{Projection}(RTE_SN)
const _DEFAULT_ROUNDING = Ref{RoundingMode}(RTE)
const _DEFAULT_SATURATION = Ref{SaturationMode}(SN)

"""
    DefaultProjection() -> Projection
    DefaultProjection!(ρ::Projection)
    DefaultProjection!(μ::RoundingMode, σ::SaturationMode)

The session default [`Projection`](@ref), consumed by the same-format
convenience methods and the value constructors. Starts as `RTE_SN`.
Coherent with [`DefaultRoundingMode`](@ref)/[`DefaultSaturationMode`](@ref) in
both directions.
"""
DefaultProjection() = _DEFAULT_PROJECTION[]
function DefaultProjection!(ρ::Projection)
    _DEFAULT_PROJECTION[] = ρ
    _DEFAULT_ROUNDING[] = RoundOf(ρ)
    _DEFAULT_SATURATION[] = SatOf(ρ)
    ρ
end
DefaultProjection!(μ::RoundingMode, σ::SaturationMode) = DefaultProjection!(Projection(μ, σ))

"""
    DefaultRoundingMode() ; DefaultRoundingMode!(μ)

The rounding half of the session default projection; setting it rebuilds the
projection with the current saturation mode.
"""
DefaultRoundingMode() = _DEFAULT_ROUNDING[]
DefaultRoundingMode!(μ::RoundingMode) = (DefaultProjection!(Projection(μ, _DEFAULT_SATURATION[])); μ)

"""
    DefaultSaturationMode() ; DefaultSaturationMode!(σ)

The saturation half of the session default projection; setting it rebuilds the
projection with the current rounding mode.
"""
DefaultSaturationMode() = _DEFAULT_SATURATION[]
DefaultSaturationMode!(σ::SaturationMode) = (DefaultProjection!(Projection(_DEFAULT_ROUNDING[], σ)); σ)