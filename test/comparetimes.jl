using BenchmarkTools, Chairmarks
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

