# suggestions from Aqua.test_all(FloatsForML) to resolve ambiguities

for T in (:SignedFiniteFloat, :SignedInfiniteFloat, :UnsignedFiniteFloat, :UnsignedInfiniteFloat,
          :SignedFiniteFP, :SignedInfiniteFP, :UnsignedFiniteFP, :UnsignedInfiniteFP)
    @eval begin
        $T(::Real, ::RoundingMode) = nothing
    end
end
