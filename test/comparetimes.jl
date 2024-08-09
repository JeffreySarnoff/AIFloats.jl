using BenchmarkTools, Chairmarks
using OrderedCollections: LittleDict
using Static
#=
 ifelse( test, istrue, isfalse )
 - all the arguments are evaluated first
 - some uses can eliminate the branch in generated code
=#
using Base: ifelse # ifelse(1 > 2, 1, 2)
using Base: @constprop
using Base: @assume_effects
#=
The following `setting`s are supported.
- `:consistent`
- `:effect_free`
- `:nothrow`
- `:terminates_globally`
- `:terminates_locally`
- `:notaskstate`
- `:inaccessiblememonly`
- `:foldable`
- `:removable`
- `:total`

## `:foldable`

This setting is a convenient shortcut for the set of effects that the compiler
requires to be guaranteed to constant fold a call at compile time. It is
currently equivalent to the following `setting`s:
- `:consistent`
- `:effect_free`
- `:terminates_globally`

## `:removable`

This setting is a convenient shortcut for the set of effects that the compiler
requires to be guaranteed to delete a call whose result is unused at compile time.
It is currently equivalent to the following `setting`s:
- `:effect_free`
- `:nothrow`
- `:terminates_globally`
=#


idx8sn3 = [collect(max(1, n-3) for n=1:255)][1];
idx8s17 = [collect(min(n, 17) for n=1:255)][1];

uint8vecs = [map(UInt8, collect(1:n)) for n=1:255];
f16vecs = map(vec->map(Float16, vec), uint8vecs);
uint8tups = map(Tuple, uint8vecs);
f16tups = map(Tuple, f16vecs);

# uintvecs = [map(UInt16, collect(1:n)) for n=1:1024];
# f32vecs = map(vec->map(Float32, vec), uintvecs);

function lookuptime(idxs, sequence)
    n = length(idxs)
    results = Vector{Float32}(undef, n)
    for i in 1:n
        idx = idxs[i]
        seq = sequence[i]
        res = @belapsed(getindex($seq, $idx))
        results[i] = Float32(res)
    end
    results
end


function lookuptime(idxs, sequence)
    n = length(idxs)
    results = Vector{Float32}(undef, n)
    for i in 1:n
        idx = idxs[i]
        seq = sequence[i]
        res = @be (getindex($seq, $idx))
        results[i] = Float32(mean(res).time)
    end
    results
end


function lookuptime(idxs, sequence)
    n = length(idxs)
    results = Vector{Float32}(undef, n)
    both = zip(idxs, sequence)
    idx = 1
    for (i,s) in both
        res = (@be (getindex($s, $i))); m = mean(res).time;
        results[i] = Float32(m); idx+=1
    end
    results
end

