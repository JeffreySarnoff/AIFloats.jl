baremodule TypeDomainNaturalNumbers
    baremodule Basic
        using Base: @nospecialize
        export
            natural_successor, natural_predecessor,
            NonnegativeInteger, PositiveInteger, PositiveIntegerUpperBound,
            with_refined_type, zero
        baremodule RecursiveStep
            using Base: @nospecialize
            export recursive_step
            function recursive_step(@nospecialize t::Type)
                Union{Nothing,t}
            end
        end
        baremodule UpperBounds
            using ..RecursiveStep
            abstract type A{P <: recursive_step(Any)} end
            abstract type B{P <: recursive_step(A)} <: A{P} end
        end
        const NonnegativeIntegerUpperBound = UpperBounds.B
        using .RecursiveStep
        struct NonnegativeIntegerImpl{
            Predecessor<:recursive_step(NonnegativeIntegerUpperBound),
        } <: NonnegativeIntegerUpperBound{Predecessor}
            predecessor::Predecessor
            function stricter(t::UnionAll)
                t{P} where {P <: recursive_step(t)}
            end
            global const NonnegativeIntegerImplTighter = stricter(NonnegativeIntegerImpl)
            global const NonnegativeInteger = stricter(NonnegativeIntegerImplTighter)
            global const PositiveInteger = let t = NonnegativeIntegerImplTighter
                t{P} where {P <: t}
            end
            global const PositiveIntegerUpperBound = let t = UpperBounds.A
                t{P} where {P <: t}
            end
            global function new_nonnegative_integer(p::P) where {P<:recursive_step(NonnegativeInteger)}
                t_p = P::DataType
                r = new{t_p}(p)
                with_refined_type(r)
            end
        end
        function with_refined_type(@nospecialize r::NonnegativeInteger)
            r
        end
        function natural_successor(o::NonnegativeInteger)
            new_nonnegative_integer(o)::PositiveInteger
        end
        function natural_predecessor(o::PositiveInteger)
            r = o.predecessor
            with_refined_type(r)
        end
        function zero()
            new_nonnegative_integer(nothing)
        end
    end

    baremodule RecursiveAlgorithms
        using ..Basic
        using Base: +, -, <, @assume_effects, @inline, @nospecialize
        export subtracted, added, to_int, from_int, is_even, multiplied
        @assume_effects :foldable function subtracted((@nospecialize l::NonnegativeInteger), @nospecialize r::NonnegativeInteger)
            ret = if r isa PositiveIntegerUpperBound
                let a = natural_predecessor(l), b = natural_predecessor(r)
                    @inline subtracted(a, b)
                end
            else
                l
            end
            with_refined_type(ret)
        end
        @assume_effects :foldable function added((@nospecialize l::NonnegativeInteger), @nospecialize r::NonnegativeInteger)
            ret = if r isa PositiveIntegerUpperBound
                let a = natural_successor(l), b = natural_predecessor(r)
                    @inline added(a, b)
                end
            else
                l
            end
            with_refined_type(ret)
        end
        @assume_effects :foldable function to_int(@nospecialize o::NonnegativeInteger)
            if o isa PositiveIntegerUpperBound
                let p = natural_predecessor(o), t = @inline to_int(p)
                    t::Int + 1
                end
            else
                0
            end::Int
        end
        struct ConvertNaturalToNegativeException <: Exception end
        @assume_effects :foldable function from_int(n::Int)
            if n < 0
                throw(ConvertNaturalToNegativeException())
            end
            ret = if n === 0
                zero()
            else
                let v = n - 1, p = @inline from_int(v)
                    p = with_refined_type(p)
                    natural_successor(p)
                end
            end
            with_refined_type(ret)
        end
        @assume_effects :foldable function is_even(@nospecialize o::NonnegativeInteger)
            if o isa PositiveIntegerUpperBound
                let p = natural_predecessor(o)
                    if p isa PositiveIntegerUpperBound
                        let s = natural_predecessor(p), r = @inline is_even(s)
                            r::Bool
                        end
                    else
                        false
                    end
                end
            else
                true
            end
        end
        @assume_effects :foldable function multiplied((@nospecialize l::NonnegativeInteger), @nospecialize r::NonnegativeInteger)
            if r isa PositiveIntegerUpperBound
                let p = natural_predecessor(r), x = @inline multiplied(l, p)
                    added(x, l)
                end
            else
                zero()
            end
        end
    end

    baremodule BaseOverloads
        using ..Basic, ..RecursiveAlgorithms
        using Base: Base, <, !, @nospecialize
        function Base.zero(::Type{NonnegativeInteger})
            zero()
        end
        function Base.zero(@nospecialize unused::NonnegativeInteger)
            zero()
        end
        function Base.iszero(@nospecialize n::NonnegativeInteger)
            if n isa PositiveIntegerUpperBound
                false
            else
                true
            end
        end
        struct ConvertTwoOrGreaterToBooleanException <: Exception end
        function to_bool(@nospecialize n::NonnegativeInteger)
            if n isa PositiveIntegerUpperBound
                let p = natural_predecessor(n)
                    if p isa PositiveIntegerUpperBound
                        throw(ConvertTwoOrGreaterToBooleanException())
                    else
                        true
                    end
                end
            else
                false
            end
        end
        function from_bool(b::Bool)
            z = zero()
            if b
                natural_successor(z)
            else
                z
            end
        end
        function Base.convert(::Type{Bool}, @nospecialize o::NonnegativeInteger)
            to_bool(o)
        end
        function Base.convert(::Type{NonnegativeInteger}, n::Bool)
            from_bool(n)
        end
        function Base.convert(::Type{Int}, @nospecialize o::NonnegativeInteger)
            to_int(o)
        end
        function Base.convert(::Type{NonnegativeInteger}, n::Int)
            from_int(n)
        end
        function Base.:(-)((@nospecialize l::NonnegativeInteger), @nospecialize r::NonnegativeInteger)
            subtracted(l, r)
        end
        function Base.:(+)((@nospecialize l::NonnegativeInteger), @nospecialize r::NonnegativeInteger)
            added(l, r)
        end
        function Base.propertynames((@nospecialize unused::Basic.NonnegativeIntegerImpl), ::Bool = false)
            ()
        end
        function Base.iseven(@nospecialize o::NonnegativeInteger)
            is_even(o)
        end
        function Base.isodd(@nospecialize o::NonnegativeInteger)
            !is_even(o)
        end
        function Base.one(::Type{NonnegativeInteger})
            natural_successor(zero())
        end
        function Base.one(@nospecialize unused::NonnegativeInteger)
            natural_successor(zero())
        end
        function Base.isone(@nospecialize n::NonnegativeInteger)
            if n isa PositiveIntegerUpperBound
                let p = natural_predecessor(n)
                    if p isa PositiveIntegerUpperBound
                        false
                    else
                        true
                    end
                end
            else
                false
            end
        end
        function Base.:(*)((@nospecialize l::NonnegativeInteger), @nospecialize r::NonnegativeInteger)
            multiplied(l, r)
        end
    end

    export
        natural_successor, natural_predecessor, NonnegativeInteger, PositiveInteger,
        natural_with_refined_type, PositiveIntegerUpperBound

    """
        natural_successor(::NonnegativeInteger)

    Return the successor of a natural number.
    """
    const natural_successor = Basic.natural_successor

    """
        natural_predecessor(::PositiveInteger)

    Return the predecessor of a nonzero natural number.
    """
    const natural_predecessor = Basic.natural_predecessor

    """
        natural_with_refined_type(::NonnegativeInteger)

    Return the argument unchanged. Throws for invalid/malformed arguments. Even though
    the returned value is identical to the argument, Julia's type inference may have
    more precise knowledge about the type of the returned value than of the argument.
    """
    const natural_with_refined_type = Basic.with_refined_type

    """
        NonnegativeInteger

    Nonnegative integers in the type domain.

    The implementation is basically the unary numeral system. Especially inspired by
    the Peano axioms/Zermelo construction of the natural numbers.
    """
    const NonnegativeInteger = Basic.NonnegativeInteger

    """
        PositiveInteger

    Positive integers in the type domain. Subtypes [`NonnegativeInteger`](@ref).
    """
    const PositiveInteger = Basic.PositiveInteger

    """
        PositiveIntegerUpperBound

    Positive integers in the type domain. Supertypes [`PositiveInteger`](@ref).
    """
    const PositiveIntegerUpperBound = Basic.PositiveIntegerUpperBound

    """
        ConvertNaturalToNegativeException

    Thrown when a conversion of a negative integer to a natural number is attempted.
    """
    const ConvertNaturalToNegativeException = RecursiveAlgorithms.ConvertNaturalToNegativeException

    """
        ConvertTwoOrGreaterToBooleanException

    Thrown when a conversion of a natural number greater than one to a Boolean is attempted.
    """
    const ConvertTwoOrGreaterToBooleanException = BaseOverloads.ConvertTwoOrGreaterToBooleanException
end
