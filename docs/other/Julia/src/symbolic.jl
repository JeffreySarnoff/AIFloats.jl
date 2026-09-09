# Source: symbolic/real-expressions.maude and symbolic/omega-elementary.maude.
"""Source expression syntax; construction alone does not establish real membership."""
struct SymbolicExpr
    head::Symbol
    args::Tuple
end
Base.:(==)(x::SymbolicExpr, y::SymbolicExpr) = x.head == y.head && x.args == y.args
Base.isequal(x::SymbolicExpr, y::SymbolicExpr) = x == y
Base.hash(x::SymbolicExpr, h::UInt) = hash((x.head, x.args), h)
const MathValue = Union{ExactValue,SymbolicExpr}
pi_multiple(r) = iszero(r) ? finite(0) : SymbolicExpr(:piMultiple, (ExactRational(r),))
const PI = pi_multiple(1)
is_pi(x) = x isa SymbolicExpr && x.head == :piMultiple
is_zero(x) = mathematical_equal(x, finite(0))
is_finite(x::SymbolicExpr) = real_domain(x) === true
is_negative(x::SymbolicExpr) = mathematical_less(x, finite(0))
function value_sign(x::SymbolicExpr)
    is_negative(x) === true && return -1
    is_zero(x) === true && return 0
    mathematical_less(finite(0), x) === true && return 1
    return UNKNOWN
end
function real_domain(x::SymbolicExpr)
    h, a = x.head, x.args
    h == :piMultiple && return true
    all(t -> is_finite(t), a) || return UNKNOWN
    h == :realDivide && return mathematical_equal(a[2], finite(0)) === false ? true : UNKNOWN
    h == :exprSqrt && return mathematical_le(finite(0), a[1])
    h in (:exprLog, :exprLog2) && return mathematical_less(finite(0), a[1])
    h == :exprTan &&
        return mathematical_equal(elementary(:Cos, a[1]), finite(0)) === false ? true : UNKNOWN
    h in (:exprArcSin, :exprArcCos) &&
        return known_and(mathematical_le(finite(-1), a[1]), mathematical_le(a[1], finite(1)))
    h == :exprArcCosh && return mathematical_le(finite(1), a[1])
    h == :exprArcTanh &&
        return known_and(mathematical_less(finite(-1), a[1]), mathematical_less(a[1], finite(1)))
    return h in (
        :realAdd,
        :realMultiply,
        :realNegate,
        :realAbs,
        :exprExp,
        :exprExp2,
        :exprSin,
        :exprCos,
        :exprArcTan,
        :exprSinh,
        :exprCosh,
        :exprTanh,
        :exprArcSinh,
    ) ? true : UNKNOWN
end
real_domain(x::FiniteValue) = true
real_domain(x) = false
function symbolic_equal(x, y)
    real_domain(x) === true || x isa ExactValue || return UNKNOWN
    real_domain(y) === true || y isa ExactValue || return UNKNOWN
    (is_nan(x) || is_nan(y)) && return false
    (is_infinite(x) || is_infinite(y)) && return false
    x == y && real_domain(x) === true && return true
    is_pi(x) && is_pi(y) && return x.args[1] == y.args[1]
    if y isa FiniteValue && iszero(y.value) && x isa SymbolicExpr
        is_pi(x) && return false
        x.head in (:exprExp, :exprExp2) && return false
        x.head == :exprCos && x.args[1] isa FiniteValue && return false
        x.head == :exprSqrt && mathematical_less(finite(0), x.args[1]) === true && return false
    end
    x isa FiniteValue && y isa SymbolicExpr && return symbolic_equal(y, x)
    return UNKNOWN
end
mathematical_equal(x::SymbolicExpr, y::MathValue) = symbolic_equal(x, y)
mathematical_equal(x::ExactValue, y::SymbolicExpr) = symbolic_equal(x, y)
function symbolic_less(x, y)
    real_domain(x) === true || x isa ExactValue || return UNKNOWN
    real_domain(y) === true || y isa ExactValue || return UNKNOWN
    (is_nan(x) || is_nan(y)) && return false
    x === NEG_INF && real_domain(y) === true && return true
    y === POS_INF && real_domain(x) === true && return true
    (x === POS_INF || y === NEG_INF) && return false
    is_pi(x) && is_pi(y) && return x.args[1] < y.args[1]
    if x isa SymbolicExpr && y isa FiniteValue && iszero(y.value)
        is_pi(x) && return x.args[1] < 0
        x.head in (:exprExp, :exprExp2) && return false
        x.head == :exprSqrt && mathematical_le(finite(0), x.args[1]) === true && return false
    elseif x isa FiniteValue && iszero(x.value) && y isa SymbolicExpr
        is_pi(y) && return y.args[1] > 0
        y.head in (:exprExp, :exprExp2) && return true
        y.head == :exprSqrt && mathematical_less(finite(0), y.args[1]) === true && return true
    end
    return UNKNOWN
end
mathematical_less(x::SymbolicExpr, y::MathValue) = symbolic_less(x, y)
mathematical_less(x::ExactValue, y::SymbolicExpr) = symbolic_less(x, y)
function negate(x::SymbolicExpr)
    real_domain(x) === true || return residual(:omegaNegate, x)
    is_pi(x) && return pi_multiple(-x.args[1])
    x.head == :realNegate && return x.args[1]
    return SymbolicExpr(:realNegate, (x,))
end
function magnitude(x::SymbolicExpr)
    real_domain(x) === true || return residual(:omegaAbs, x)
    return is_pi(x) ? pi_multiple(abs(x.args[1])) : SymbolicExpr(:realAbs, (x,))
end
function symbolic_add(x, y)
    all(v -> v isa ExactValue || real_domain(v) === true, (x, y)) ||
        return residual(:omegaAdd, x, y)
    (is_nan(x) || is_nan(y)) && return NAN
    is_infinite(x) && real_domain(y) === true && return x
    is_infinite(y) && real_domain(x) === true && return y
    is_zero(x) === true && return y
    is_zero(y) === true && return x
    is_pi(x) && is_pi(y) && return pi_multiple(x.args[1]+y.args[1])
    return SymbolicExpr(:realAdd, (x, y))
end
add(x::SymbolicExpr, y::MathValue) = symbolic_add(x, y)
add(x::ExactValue, y::SymbolicExpr) = symbolic_add(x, y)
function symbolic_multiply(x, y)
    all(v -> v isa ExactValue || real_domain(v) === true, (x, y)) ||
        return residual(:omegaMultiply, x, y)
    (is_nan(x) || is_nan(y)) && return NAN
    if is_infinite(x) || is_infinite(y)
        i, u = is_infinite(x) ? (x, y) : (y, x)
        is_zero(u) === true && return NAN
        if is_zero(u) === false && is_negative(u) !== UNKNOWN
            return is_negative(i) == is_negative(u) ? POS_INF : NEG_INF
        end
        return residual(:omegaMultiply, x, y)
    end
    (is_zero(x) === true || is_zero(y) === true) && return finite(0)
    mathematical_equal(x, finite(1)) === true && return y
    mathematical_equal(y, finite(1)) === true && return x
    is_pi(x) && y isa FiniteValue && return pi_multiple(x.args[1]*y.value)
    is_pi(y) && x isa FiniteValue && return pi_multiple(y.args[1]*x.value)
    return SymbolicExpr(:realMultiply, (x, y))
end
multiply(x::SymbolicExpr, y::MathValue) = symbolic_multiply(x, y)
multiply(x::ExactValue, y::SymbolicExpr) = symbolic_multiply(x, y)
function symbolic_divide(x, y)
    all(v -> v isa ExactValue || real_domain(v) === true, (x, y)) ||
        return residual(:omegaDivide, x, y)
    (is_nan(x) || is_nan(y) || is_zero(y) === true) && return NAN
    is_infinite(y) && real_domain(x) === true && return finite(0)
    is_zero(y) === false || return residual(:omegaDivide, x, y)
    if is_infinite(x)
        s = is_negative(y)
        return s === UNKNOWN ? residual(:omegaDivide, x, y) :
               is_negative(x) == s ? POS_INF : NEG_INF
    end
    is_zero(x) === true && return finite(0)
    mathematical_equal(y, finite(1)) === true && return x
    is_pi(x) && is_pi(y) && return finite(x.args[1]/y.args[1])
    is_pi(x) && y isa FiniteValue && return pi_multiple(x.args[1]/y.value)
    return SymbolicExpr(:realDivide, (x, y))
end
divide(x::SymbolicExpr, y::MathValue) = symbolic_divide(x, y)
divide(x::ExactValue, y::SymbolicExpr) = symbolic_divide(x, y)
project(f::Format, p::Projection, x::SymbolicExpr) =
    residual(:project, f, p, x; reason = :uncertified_projection)

function expression(name::Symbol, x)
    if x isa FiniteValue
        r = x.value
        if name == :Sqrt && r >= 0
            n, d = isqrt(numerator(r)), isqrt(denominator(r))
            n*n == numerator(r) && d*d == denominator(r) && return finite(n//d)
        elseif name == :Exp2 && denominator(r) == 1
            return finite(pow2(numerator(r)))
        elseif name == :Log2 && r > 0
            k = floor_log2(r)
            r == pow2(k) && return finite(k)
        elseif name in (:Exp, :Cos, :Cosh) && r == 0
            return finite(1)
        elseif name in (:Log, :ArcCosh) && r == 1
            return finite(0)
        elseif name in (:Sin, :Tan, :ArcSin, :ArcTan, :Sinh, :Tanh, :ArcSinh, :ArcTanh) && r == 0
            return finite(0)
        elseif name == :ArcSin && abs(r) == 1
            return pi_multiple(r/2)
        elseif name == :ArcCos && r in (-1, 0, 1)
            return pi_multiple((1-r)/2)
        elseif name == :ArcTan && abs(r) == 1
            return pi_multiple(r/4)
        end
    elseif is_pi(x) && name in (:Sin, :Cos, :Tan)
        r = x.args[1]
        q = floor(BigInt, r)
        fraction = r-q
        fraction == 0 && return finite(name == :Cos ? (iseven(q) ? 1 : -1) : 0)
        fraction == 1//2 && name == :Sin && return finite(iseven(q) ? 1 : -1)
        fraction == 1//2 && name == :Cos && return finite(0)
    end
    return SymbolicExpr(Symbol(:expr, name), (x,))
end
function elementary(name::Symbol, x::MathValue)
    x isa SymbolicExpr && real_domain(x) !== true && return residual(Symbol(:omega, name), x)
    is_nan(x) && return NAN
    name == :LogOnePlus && return elementary(:Log, add(finite(1), x))
    name == :ExpMinusOne && return subtract(elementary(:Exp, x), finite(1))
    name == :Softplus && return elementary(:Log, add(finite(1), elementary(:Exp, x)))
    if name in (:SinPi, :CosPi, :TanPi)
        return elementary(Symbol(chop(String(name); tail = 2)), multiply(x, PI))
    elseif name in (:ArcSinPi, :ArcCosPi, :ArcTanPi)
        return divide(elementary(Symbol(chop(String(name); tail = 2)), x), PI)
    end
    if is_infinite(x)
        name in (:Sin, :Cos, :Tan, :ArcSin, :ArcCos, :ArcTanh) && return NAN
        name == :ArcTan && return pi_multiple(x === POS_INF ? 1//2 : -1//2)
        name == :RSqrt && return x === POS_INF ? finite(0) : NAN
        name in (:Exp, :Exp2) && return x === POS_INF ? POS_INF : finite(0)
        name in (:Sinh, :ArcSinh) && return x
        name == :Cosh && return POS_INF
        name == :Tanh && return finite(x === POS_INF ? 1 : -1)
        return x === POS_INF ? POS_INF : NAN
    end
    if name in (:Sqrt, :RSqrt, :Log, :Log2)
        neg, zero = mathematical_less(x, finite(0)), is_zero(x)
        neg === true && return NAN
        name == :RSqrt && zero === true && return NAN
        name in (:Log, :Log2) && zero === true && return NEG_INF
        if name == :RSqrt
            return mathematical_less(finite(0), x) === true ? reciprocal(elementary(:Sqrt, x)) :
                   residual(:omegaRSqrt, x)
        end
    elseif name in (:ArcSin, :ArcCos, :ArcTanh)
        known_or(mathematical_less(x, finite(-1)), mathematical_less(finite(1), x)) === true &&
            return NAN
        if name == :ArcTanh
            mathematical_equal(x, finite(1)) === true && return POS_INF
            mathematical_equal(x, finite(-1)) === true && return NEG_INF
        end
    elseif name == :ArcCosh
        mathematical_less(x, finite(1)) === true && return NAN
    elseif name == :Tan
        c, s = elementary(:Cos, x), elementary(:Sin, x)
        if is_zero(c) === true
            mathematical_less(finite(0), s) === true && return POS_INF
            mathematical_less(s, finite(0)) === true && return NEG_INF
        end
    end
    result = expression(name, x)
    real_domain(result) === true && return result
    return residual(Symbol(:omega, name), x)
end
elementary(name::Symbol, x::Residual) = residual(Symbol(:omega, name), x)
function hypot_value(x, y)
    (is_nan(x) || is_nan(y)) && return NAN
    (is_infinite(x) || is_infinite(y)) && return POS_INF
    return elementary(:Sqrt, add(multiply(x, x), multiply(y, y)))
end
function atan2_value(y, x)
    (is_nan(x) || is_nan(y) || (is_infinite(x) && is_infinite(y))) && return NAN
    is_zero(x) === true && is_zero(y) === true && return NAN
    x === POS_INF && return finite(0)
    y === POS_INF && return pi_multiple(1//2)
    y === NEG_INF && return pi_multiple(-1//2)
    if x === NEG_INF
        mathematical_le(finite(0), y) === true && return PI
        mathematical_less(y, finite(0)) === true && return pi_multiple(-1)
    elseif is_zero(x) === true
        mathematical_less(finite(0), y) === true && return pi_multiple(1//2)
        mathematical_less(y, finite(0)) === true && return pi_multiple(-1//2)
    elseif mathematical_less(finite(0), x) === true
        is_zero(y) === true && return finite(0)
        is_zero(y) === false && return elementary(:ArcTan, divide(y, x))
    elseif mathematical_less(x, finite(0)) === true
        is_zero(y) === true && return PI
        mathematical_less(finite(0), y) === true &&
            return add(elementary(:ArcTan, divide(y, x)), PI)
        mathematical_less(y, finite(0)) === true &&
            return subtract(elementary(:ArcTan, divide(y, x)), PI)
    end
    return residual(:omegaArcTan2, y, x)
end

module Symbolic
using ..P3109Reference:
    SymbolicExpr,
    Residual,
    UNKNOWN,
    expression,
    elementary,
    real_domain,
    pi_multiple,
    mathematical_equal,
    mathematical_less
public SymbolicExpr,
    Residual,
    UNKNOWN,
    expression,
    elementary,
    real_domain,
    pi_multiple,
    mathematical_equal,
    mathematical_less
end
