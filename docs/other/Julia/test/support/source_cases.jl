module SourceCases
using JSON: JSON
using CodecZlib: GzipDecompressorStream
using SHA: sha256
import P3109Reference as P

struct Call
    name::String
    args::Vector{Any}
end
struct InvalidCall
    name::String
    args::Vector{Any}
end
struct BlockRandoms
    mode::P.RoundMode
    bits::BigInt
    randoms::Vector
end
mutable struct Parser
    tokens::Vector{String}
    position::Int
end
const TOKEN =
    r"\s*(=\/=|::|==|<=|>=|/\\|[(),+*/^<>-]|\"(?:[^\"\\]|\\.)*\"|[0-9]+|[A-Za-z][A-Za-z0-9_-]*)"
function tokenize(text)
    tokens=String[]
    offset=firstindex(text)
    while offset <= lastindex(text)
        all(isspace, SubString(text, offset)) && break
        m=match(TOKEN, text, offset)
        m !== nothing && m.offset == offset || error("unsupported source syntax at $offset: $text")
        push!(tokens, m.captures[1])
        offset += ncodeunits(m.match)
    end
    return tokens
end
peek(p) = p.position <= length(p.tokens) ? p.tokens[p.position] : ""
function take!(p)
    t=peek(p)
    isempty(t) && error("unexpected end of source term")
    p.position+=1
    return t
end
function expect!(p, t)
    take!(p)==t || error("expected $t")
end
const PRECEDENCE = Dict(
    "or"=>1,
    "and"=>2,
    "/\\"=>2,
    "=="=>3,
    "=/="=>3,
    "<"=>4,
    "<="=>4,
    ">"=>4,
    ">="=>4,
    "::"=>5,
    "+"=>6,
    "-"=>6,
    "*"=>7,
    "/"=>7,
    "^"=>8,
)
function parse_expression(p, level = 0)
    t=take!(p)
    left = if t == "("
        x=parse_expression(p)
        expect!(p, ")")
        x
    elseif t in ("-", "not")
        Call(t=="-" ? "negative" : "not", [parse_expression(p, t=="-" ? 8 : 3)])
    elseif startswith(t, "\"")
        JSON.parse(t)
    elseif isdigit(first(t))
        parse(BigInt, t)
    elseif peek(p)=="("
        take!(p)
        args=Any[]
        if peek(p)!=")"
            push!(args, parse_expression(p))
            while peek(p)==","
                take!(p)
                push!(args, parse_expression(p))
            end
        end
        expect!(p, ")")
        Call(t, args)
    else
        Symbol(t)
    end
    while get(PRECEDENCE, peek(p), -1) >= level
        op=take!(p)
        pr=PRECEDENCE[op]
        right=parse_expression(p, op=="^" ? pr : pr+1)
        left=Call(op, [left, right])
    end
    return left
end
function parse_source(text)
    p=Parser(tokenize(text), 1)
    x=parse_expression(p)
    isempty(peek(p)) || error("unconsumed source tokens: $(p.tokens[p.position:end])")
    return x
end
const MODES = Dict(
    "NearestTiesToEven"=>P.NEAREST_EVEN,
    "NearestTiesToAway"=>P.NEAREST_AWAY,
    "TowardPositive"=>P.UP,
    "TowardNegative"=>P.DOWN,
    "TowardZero"=>P.TO_ZERO,
    "ToOdd"=>P.TO_ODD,
)
const CONSTANTS = Dict{Symbol,Any}(
    :Signed=>P.SIGNED,
    :Unsigned=>P.UNSIGNED,
    :Finite=>P.FINITE,
    :Extended=>P.EXTENDED,
    :nan=>P.NAN,
    :posInf=>P.POS_INF,
    :negInf=>P.NEG_INF,
    :pi=>P.PI,
    Symbol("true")=>true,
    Symbol("false")=>false,
    :SatNone=>P.SAT_NONE,
    :SatFinite=>P.SAT_FINITE,
    :SatPropagate=>P.SAT_PROPAGATE,
    :binary64=>P.BINARY64,
    :binary32=>P.BINARY32,
    :binary16=>P.BINARY16,
    :BFloat16=>P.BFLOAT16,
    :kNaN=>P.Kappa(P.NAN_MISMATCH),
    :kInfinity=>P.Kappa(P.INFINITY_MISMATCH),
)
for (n, m) in MODES
    CONSTANTS[Symbol(n)]=P.RoundPolicy(m)
end
for name in (:cnil, :xnil, :rnil, :fnil, :dnil, :snil, :pnil, :knil, :onil, :anil)
    CONSTANTS[name]=Any[]
end
const ALIASES = Dict(
    "fin"=>P.finite,
    "piMultiple"=>P.pi_multiple,
    "Binary"=>P.BinaryFormat,
    "decode"=>P.decode,
    "encode"=>P.encode,
    "datum"=>P.is_datum,
    "project"=>P.project,
    "floorLog2"=>P.floor_log2,
    "roundToPrecision"=>P.round_to_precision,
    "realAdd"=>P.add,
    "realDivide"=>P.divide,
    "xEq"=>P.mathematical_equal,
    "xLt"=>P.mathematical_less,
    "xLe"=>P.mathematical_le,
    "validBlock"=>P.valid_block,
    "validBlockProjection"=>P.valid_block_projection,
    "blockDecode"=>P.decode_block,
    "normalizeElement"=>P.normalize_element,
    "block"=>P.BlockValue,
    "singletonLift"=>P.singleton_lift,
    "required"=>P.required,
    "validFX"=>P.valid_fx,
    "validSpecialization"=>P.valid_specialization,
    "numericArity"=>P.numeric_arity,
    "plainArity"=>P.plain_arity,
    "blockElementArity"=>P.block_element_arity,
    "wellFormedDeclaration"=>P.well_formed_declaration,
    "declarationKappa"=>P.declaration_kappa,
    "declarationsCover"=>P.declarations_cover,
    "finiteRank"=>P.finite_rank,
    "observation"=>P.Observation,
    "observationKappa"=>P.observation_kappa,
    "batchKappa"=>P.batch_kappa,
    "mergeKappa"=>P.merge_kappa,
    "partition"=>P.partition,
    "kappaPart"=>P.KappaPart,
)
function membership(x, t)
    (x isa InvalidCall || x isa P.Residual) && return false
    t in (:Nat, :Int, :Rat) && return x isa Union{Integer,Rational} &&
           (t==:Rat || (denominator(x)==1 && (t==:Int || x>=0)))
    t==:Real && return P.real_domain(x) === true
    t==:XReal && return x isa P.ExactValue || (x isa P.SymbolicExpr && P.real_domain(x)===true)
    t==:Number && return !P.is_nan(x) && (x isa P.ExactValue || P.real_domain(x)===true)
    t==:XSeq && return x isa AbstractVector && all(y->membership(y, :XReal), x)
    t==:CodeSeq && return x isa AbstractVector && all(y->y isa Integer, x)
    t==:RoundMode && return x isa P.RoundPolicy
    t==:SatMode && return x isa P.Saturation
    t==:Bool && return x isa Bool
    error("unsupported membership sort $t")
end
evaluate(x) = x
evaluate(x::Symbol) = get(CONSTANTS, x, x)
function invoke_call(name, args)
    name=="validFormat" && return !(args[1] isa InvalidCall) && P.valid_format(args[1])
    name=="validCode" && return !(args[1] isa InvalidCall) && P.valid_code(args...)
    name=="validRound" && return args[1] isa P.RoundPolicy
    any(x->x isa InvalidCall, args) && return InvalidCall(name, args)
    startswith(name, "omega") &&
        return getproperty(P.OPERATION_KERNELS, Symbol(name[6:end]))(args...)
    isdefined(P.SpecAPI, Symbol(name)) && return getfield(P.SpecAPI, Symbol(name))(args...)
    haskey(ALIASES, name) && return ALIASES[name](args...)
    name in
    ("ccons", "xcons", "rcons", "fcons", "dcons", "scons", "pcons", "kcons", "ocons", "acons") &&
        return vcat([args[1]], args[2])
    startswith(name, "expr") && return P.expression(Symbol(name[5:end]), args[1])
    name=="proj" && return P.Projection(args...)
    if name=="bproj"
        m, s=args
        return m isa BlockRandoms ? P.BlockProjection(m.mode, s, m.bits, m.randoms) :
               P.deterministic(m) ? P.BlockProjection(m.mode, s) : InvalidCall(name, args)
    elseif startswith(name, "BlockStochastic")
        return BlockRandoms(getproperty(P, Symbol("STOCHASTIC_", last(name))), args[1], args[2])
    elseif startswith(name, "Stochastic")
        return P.RoundPolicy(getproperty(P, Symbol("STOCHASTIC_", last(name))), args...)
    elseif name=="numeric"
        return P.specialization(:numeric, args[1], args[2]; projection = args[3])
    elseif name=="plain"
        return P.specialization(:plain, args...)
    elseif name in ("blockElements", "blockReduction", "blockScale")
        kw =
            name=="blockElements" ? (; block_projection = args[4]) :
            name=="blockReduction" ? (; projection = args[4]) :
            (; projection = args[4], block_projection = args[5])
        return P.specialization(Symbol(name), args[1], args[3]; size = args[2], kw...)
    elseif name=="steps"
        return P.Kappa(P.FINITE_STEPS, args[1])
    elseif name=="exact"
        return P.declaration(:exact, args[1], args[2], args[3])
    elseif name=="approximate"
        return P.declaration(:approximate, args[1], args[2], args[4]; bound = args[3])
    elseif name=="partitioned"
        return P.declaration(
            :partitioned,
            args[1],
            args[2],
            args[5];
            universe = args[3],
            parts = args[4],
        )
    elseif name=="partition2"
        return P.partition(args[1], args[2:3])
    elseif name=="evidenceComplete"
        return P.evidence_complete(args[1])
    elseif name=="foldMultiply"
        return foldl(P.multiply, args[2]; init = args[1])
    elseif name=="blockProject"
        n, fs, fr, p, s, xs=args
        n>=1 && length(xs)==n || throw(DimensionMismatch("block length"))
        return P.project_elements(fr, p, xs; scale = P.decode(fs, s))
    end
    error("unsupported source operation: $name")
end
function evaluate(c::Call)
    n=c.name
    if n=="::"
        return membership(evaluate(c.args[1]), c.args[2])
    end
    args=map(evaluate, c.args)
    n=="==" && return args[1]==args[2]
    n=="=/=" && return args[1]!=args[2]
    n=="and" || n=="/\\" ? (return P.known_and(args...)) : nothing
    n=="or" && return P.known_or(args...)
    n=="not" && return args[1] isa Bool ? !args[1] : P.UNKNOWN
    n=="negative" && return -args[1]
    n=="+" && return +(args...)
    n=="-" && return -(args...)
    n=="*" && return *(args...)
    n=="/" && return //(args...)
    n=="^" && return args[1]^args[2]
    n=="<" && return <(args...)
    n=="<=" && return <=(args...)
    n==">" && return >(args...)
    n==">=" && return >=(args...)
    try
        return invoke_call(n, args)
    catch e
        if e isa Union{ArgumentError,DomainError,DimensionMismatch,BoundsError}
            return InvalidCall(n, args)
        end
        rethrow()
    end
end
function run_suite(suite; limit = typemax(Int), root = joinpath(@__DIR__, "..", "vectors"))
    manifest=JSON.parsefile(joinpath(root, "manifest.json"))[suite]
    bytes=open(joinpath(root, suite*".jsonl.gz")) do io
        read(GzipDecompressorStream(io))
    end
    bytes2hex(sha256(bytes))==manifest["sha256"] || error("fixture hash mismatch: $suite")
    ids=Set{String}()
    failures=String[]
    count=0
    for line in eachline(IOBuffer(bytes))
        row=JSON.parse(line)
        id=String(row["id"])
        id in ids && error("duplicate case $id")
        push!(ids, id)
        count+=1
        try
            tree=parse_source(row["expression"])
            result=evaluate(tree)
            result === true || push!(failures, "$id: result=$(repr(result))\n$(row["expression"])")
        catch e
            push!(failures, "$id: $(sprint(showerror,e))\n$(row["expression"])")
        end
        count>=limit && break
    end
    limit==typemax(Int) && count!=manifest["cases"] && error("missing cases: $suite")
    return (; suite, count, failures)
end
end
