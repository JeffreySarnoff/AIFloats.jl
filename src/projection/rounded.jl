# the canonical rounded form, and the sticky protocol
#
# Rounded is what ωRoundToPrecision produces and ωSaturate consumes:
# value = sign · S · 2^Q with S ∈ 0:2^P (2^P is a next-binade carry that
# round_to_precision normalizes away before returning).
#
# sticky ∈ {−1, 0, +1} is SYMBOLIC information: the true value equals the
# carried value plus sticky·ε for an infinitesimal ε > 0. It lets a correctly
# rounded enclosure endpoint stand in for an irrational true value without
# losing the direction that directed, tie-breaking, and stochastic rounding
# need. This is the mechanism that makes the interval oracle sound.

const KIND_FIN  = 0x00
const KIND_NAN  = 0x01
const KIND_PINF = 0x02
const KIND_NINF = 0x03

struct Rounded
    kind::UInt8
    sign::Int8      # ±1 for finite nonzero; +1 for zero
    S::Int64        # significand, 0 <= S < 2^P after normalization
    Q::Int64        # value = sign · S · 2^Q
end

# "finite but beyond every format": the sentinel exponent used when an
# infinity arrives with sticky pointing back inward — the true value is finite
# and over-large, so it must SATURATE rather than propagate an infinity the
# true value never reached. Exceeds every format's Q_hi.
const HUGEQ = Int64(1) << 40

const ROUNDED_NAN  = Rounded(KIND_NAN,  Int8(1), Int64(0), Int64(0))
const ROUNDED_ZERO = Rounded(KIND_FIN,  Int8(1), Int64(0), Int64(0))
const ROUNDED_PINF = Rounded(KIND_PINF, Int8(1), Int64(0), Int64(0))
const ROUNDED_NINF = Rounded(KIND_NINF, Int8(-1), Int64(0), Int64(0))