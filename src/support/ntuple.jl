#=
chatgpt: using Julia, what is the most performant and portable way to write a function that works like searchsortedfirst and takes a target value and an NTuple as its arguments

Performance: Avoid unnecessary allocations and
             enable the compiler to fully unroll small tuple searches


@generated: Ensures loop bounds are constants, so the compiler can fully unroll the binary search for small N.

@inbounds: Skips bounds checking for performance (safe because loop is bounded).

No allocations: Fully stack-allocated and pure.
=#
@generated function tuple_searchsortedfirst(t::NTuple{N,T}, x::T) where {N, T}
    quote
        @inbounds begin
            lo = 1
            hi = $N + 1  # upper bound is one past the last index
            while lo < hi
                mid = (lo + hi) >>> 1
                if x <= t[mid]
                    hi = mid
                else
                    lo = mid + 1
                end
            end
            return lo
        end
    end
end
