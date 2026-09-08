# OpSpecialization — the draft's *operation specialization* as a first-class value
#
# The report writes an operation as `Op_{fx,fy,fr,ρ}(x, y)` (§4.3.1): the
# PARAMETERS are subscripts, bound first, and the OPERANDS follow in the
# parentheses. Julia gets `fx` and `fy` for free — every datum carries its
# format in its type — which leaves `fr` and `ρ` as the only subscripts
# without a carrier, and they keep the report's position ahead of the
# operands. `Op(fr, ρ)` binds exactly those two and hands back the
# specialization, so the subscript/operand split the report draws on paper is
# a split a caller can hold in a variable.
#
# A BINDING, NEVER A COMPOSITION. The call forwards to the very method
# `Op(fr, ρ, xs...)` would have run; nothing is projected until the operands
# arrive, so the one-projection invariant is untouched. There is deliberately
# no way to compose two specializations: `Op₂ ∘ Op₁` projects twice, and a
# doubly rounded result is not the correctly rounded one — the Operations page
# carries the counterexample.
#
# THROUGHPUT. The array call forwards to the array method of the same name,
# which is `vmap` — the memoized Shape-A gather when `table_policy` grants a
# table, threaded past `THREAD_MIN_ELEMS` otherwise. This is the reason the
# array methods exist here at all: `map(op, A, B)` would run the scalar path
# per element and gather from nothing, while `op(A, B)` runs the kernel. The
# two spellings differ by more than two orders of magnitude at K = 8.

"""
    AIFloats.OpSpecialization{OP,FR,P}

A registry operation with its **result format** and **projection** already
bound — the draft's `Op_{…,fr,ρ}` with the subscripts filled in (§4.3.2.4).

Built by calling any operation with just those two parameters, `Op(fr, ρ)`,
and called with the operands alone. `OP` is the operation name (a `Symbol`),
`FR` the result [`Binary`](@ref) format, and the projection is the field `ρ`.

Operands may be datums *or* arrays of datums. The array call is the array
operation, so it takes the [`vmap`](@ref) kernel — the memoized gather and the
threaded loop — rather than a per-element `map`.

The three parameters read back as `nameof(b)`, [`formatof`](@ref)`(b)` (also
[`BinaryFormatOf`](@ref)), and `Projection(b)` (also the field `b.ρ`).

A specialization **binds** parameters; it never composes operations. There is
deliberately no `∘` for it, because `Op₂ ∘ Op₁` would project twice and a
doubly rounded result is not the correctly rounded one — see the Operations
page.

Not exported; call it `AIFloats.OpSpecialization`. The values are what a
caller names, not the type.

# Examples

```jldoctest
julia> F = Binary8p4se; x = F(1.5); y = F(0.25);

julia> mul = Multiply(F, RTE_SN)
Multiply(Binary8p4se, ρ(RoundToEven, SatNone))

julia> mul(x, y) === Multiply(F, RTE_SN, x, y)
true

julia> mul([x, y], [y, x]) == Multiply(F, RTE_SN, [x, y], [y, x])
true

julia> formatof(mul) === F, nameof(mul)
(true, :Multiply)
```

See also [`Projection`](@ref), [`vmap`](@ref).
"""
struct OpSpecialization{OP, FR<:Binary, P<:Projection} <: Function
    ρ::P

    # The two type parameters a caller supplies are OP and FR; P is read off
    # the projection so the field type stays CONCRETE. That concreteness is
    # the whole performance story: a specialization over a constant projection
    # is a zero-size, `isbits` value, so `b.ρ` folds and the forwarded call is
    # the same static call the explicit form makes.
    OpSpecialization{OP,FR}(ρ::P) where {OP,FR<:Binary,P<:Projection} =
        new{OP,FR,P}(ρ)
end

Base.nameof(::OpSpecialization{OP}) where {OP} = OP
BinaryFormatOf(::OpSpecialization{OP,FR}) where {OP,FR} = FR
BinaryFormatOf(::Type{<:OpSpecialization{OP,FR}}) where {OP,FR} = FR
# the projection bound into `b`. `b.ρ` says the same thing; this spelling
# exists so the three parameters read the same way — nameof, formatof,
# Projection. Documented on OpSpecialization, not here: a second docstring on
# the `Projection` binding would land in the Reference beside the constructor.
Projection(b::OpSpecialization) = b.ρ

Base.show(io::IO, b::OpSpecialization{OP,FR}) where {OP,FR} =
    print(io, OP, "(", formatname(FR), ", ", b.ρ, ")")
# A specialization IS a function object and subtypes `Function`, which puts
# Base's "generic function with N methods" three-argument `show` ahead of the
# two above at the REPL. The operation, its format, and its projection are what
# a caller needs to see, so the MIME method is the same line.
Base.show(io::IO, ::MIME"text/plain", b::OpSpecialization) = show(io, b)

# The call error. One @noinline path for both mistakes a caller makes here:
# the wrong operand COUNT (the specialization binds parameters, not operands,
# so the count is still the registry's arity) and the right count of the wrong
# THING. Julia's own MethodError would name `OpSpecialization{:Multiply, …}`,
# which tells a caller nothing they can act on.
@noinline function _spec_call_error(b::OpSpecialization{OP}, args::Tuple) where {OP}
    n = opinfo(OP).arity
    got = length(args)
    what = n == 1 ? "operand" : "operands"
    shown = sprint(show, b)
    got == n && throw(ArgumentError(
        "$shown takes $n datum $what, or $n array$(n == 1 ? "" : "s") of datums; got " *
        join((string(typeof(a)) for a in args), ", ")))
    throw(ArgumentError(
        "$shown takes $n $what, got $got. A specialization binds the result " *
        "format and the projection; the operands are supplied at the call."))
end
@noinline (b::OpSpecialization{OP})(args...; kw...) where {OP} = _spec_call_error(b, args)

# ---- registry-generated: the constructor and the two call shapes ------------
# Convert is excluded and written by hand below: its operand set is
# `ConvertSource`, not `BinaryValue`, and its array surface accepts external
# float and integer arrays that no other operation does.
for op in OP_REGISTRY
    op.name === :Convert && continue
    name = op.name
    Q = QuoteNode(name)
    xs = [Symbol(:x, i) for i in 1:op.arity]
    dat = [:($x::BinaryValue) for x in xs]
    arr = [:($x::AbstractArray{<:BinaryValue}) for x in xs]
    @eval begin
        # `Op(fr, ρ)` cannot collide with any existing method: the same-format
        # convenience is `Op(x::T, y::T)` over datums, and the unary
        # projection-first form is `Op(ρ, x)`. A leading `Type{<:Binary}`
        # followed by a `Projection` is neither.
        @inline $name(::Type{FR}, ρ::Projection) where {FR<:Binary} =
            OpSpecialization{$Q,FR}(ρ)
        @inline $name(fr::Type{<:BinaryValue}, ρ::Projection) =
            $name(BinaryFormatOf(fr), ρ)

        @inline (b::OpSpecialization{$Q,FR})($(dat...); kw...) where {FR<:Binary} =
            $name(FR, b.ρ, $(xs...); kw...)
        @inline (b::OpSpecialization{$Q,FR})($(arr...); kw...) where {FR<:Binary} =
            $name(FR, b.ρ, $(xs...); kw...)
    end
end

@inline Convert(::Type{FR}, ρ::Projection) where {FR<:Binary} =
    OpSpecialization{:Convert,FR}(ρ)
@inline Convert(fr::Type{<:BinaryValue}, ρ::Projection) = Convert(BinaryFormatOf(fr), ρ)
@inline (b::OpSpecialization{:Convert,FR})(x::ConvertSource; kw...) where {FR<:Binary} =
    Convert(FR, b.ρ, x; kw...)
# every array, including the ones Convert rejects — the refusal message is
# Convert's own, and better than anything this seam could say
@inline (b::OpSpecialization{:Convert,FR})(A::AbstractArray; kw...) where {FR<:Binary} =
    Convert(FR, b.ρ, A; kw...)
