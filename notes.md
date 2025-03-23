posvals(xs) = filter(x->(isfinite(x) && !iszero(x) && !signbit(x)), xs)

BV81 = Base.values(8,1)

BV81[[67:192]] matches the strictly postive values of SE81




