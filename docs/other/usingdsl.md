# Using a DSL as the P3109 source of truth

**Status:** Design recommendation and proposed language specification. This is
not an IEEE document and does not change the authority of `IEEE_D1.md` or the
designated P3109 report.

## 1. Recommendation

If CUE is not used, adopt a small, purpose-built language named **AFSpec**
(Arithmetic Format Specification Language). AFSpec source files should compile
into a typed, immutable intermediate representation (IR). Every other artifact
should be generated from that checked IR:

```text
AFSpec source (*.afspec)
        |
        v
parse, resolve, type-check, and analyze
        |
        v
canonical CheckedSpec IR
        |--------------------|-------------------|------------------|
        v                    v                   v                  v
Julia adapters          Lean definitions    Markdown          RDF/Turtle
and tests               and proofs          reference         provenance
```

AFSpec should be standard-oriented rather than Julia-oriented. For example, the
standard's `Binary` format family remains `Binary` in AFSpec. A separate Julia
adapter can map that entity to `BinaryFormat` and `Value<Binary(...)>` to the
Julia `Binary` value type. Target-language spelling must not leak into the
normative model.

This purpose-built DSL is preferable here to substituting another general
configuration language for CUE. Guard order, indexed format/value types,
partiality, exact arithmetic, and clause provenance are semantic concepts, not
data-shape conventions. Encoding them indirectly in YAML, TOML, JSON, or Dhall
would move essential rules into an out-of-band validator. Making Lean the
authoring language would strengthen proofs but raise the contribution barrier
and couple editorial work to a proof assistant. Embedding the source directly
in Julia would couple standard names and semantics to implementation concerns.
AFSpec keeps the review surface small while still allowing JSON, Lean, and
Julia to serve as generated representations.

This arrangement creates a clean seam. The compiler is a deep module: callers
provide source files and receive either a checked specification or diagnostics.
Parsing, name resolution, type checking, overlap analysis, canonicalization,
and provenance validation stay inside the module. Generators are adapters at a
second seam and consume only `CheckedSpec`; they never parse AFSpec themselves.

## 2. Goals and non-goals

AFSpec shall:

- Distinguish format families, format instances, encoded values, mathematical
  datums, operation families, and operation specializations by type.
- Represent guarded, first-match equations without relying on host-language
  dispatch or incidental method order.
- Use exact numeric syntax and make approximation explicit.
- Preserve stable identities and source provenance for every normative entity.
- Permit deterministic generation of Julia, Lean, Markdown, JSON, and RDF.
- Support useful static checks before any target artifact is generated.
- Remain small enough that its grammar and semantics can be reviewed as a
  whole.

AFSpec shall not:

- Execute arbitrary Julia or shell code.
- Contain target-specific implementation optimizations.
- Treat Markdown prose as executable semantics.
- Infer normative requirements from informative notes or examples.
- Use binary hardware floating point to interpret mathematical literals.
- Make a graph database, code generator, or proof assistant another source of
  truth.

## 3. Source-of-truth policy

After the Phase 6 migration, there shall be exactly one editable semantic
source: the AFSpec corpus. Until then, the designated P3109 report remains
authoritative and AFSpec output is compared against it.

The checked IR, canonical JSON, generated Julia, generated Lean, generated
Markdown, and knowledge graph are derived artifacts. A generated artifact shall
carry:

- The AFSpec language version.
- The specification module and revision.
- A digest of the complete source corpus.
- A semantic digest of the canonical checked IR.
- The generator name and version.

Generated files shall begin with a notice saying that manual edits will be
overwritten. CI shall regenerate them and fail when the working tree changes.

There are two useful digests:

1. The **source digest** covers source bytes, including informative prose.
2. The **semantic digest** covers canonical IR after comments and presentation
   details are removed, but includes every normative declaration and rule.

Changing whitespace may change the source digest but shall not change the
semantic digest. Changing a rule, type, constraint, stable ID, or normative
provenance shall change the semantic digest.

Both digests shall use SHA-256 with distinct domain-separation prefixes. The
source digest shall hash a canonical manifest containing each normalized
logical path, its byte length, and its unmodified bytes in path order. This
prevents filesystem traversal order, path aliases, or concatenation ambiguity
from changing or weakening the digest.

## 4. Repository layout

The proposed layout is:

```text
spec/
  p3109/
    module.afspec
    vocabulary.afspec
    formats.afspec
    projection.afspec
    scalar-operations.afspec
    block-operations.afspec
    conformance.afspec
    informative.afspec
    target-mappings/
      julia.toml
generated/
  spec/
    afspec-ir.schema.json
    p3109.json
    p3109.jl
    p3109.lean
    p3109.md
    p3109.ttl
src/
  spec/
    compiler.jl
    ir.jl
    diagnostics.jl
    emit.jl
test/
  spec/
    valid/
    invalid/
    golden/
build/
  spec/                       # ignored temporary build products
```

`generated/spec/` contains reviewable, reproducible artifacts checked into the
repository; `build/spec/` contains disposable intermediate files. Target
mappings are editable adapter configuration, but shall be unable to add,
remove, reorder, or reinterpret semantic declarations.

Imports shall be resolved only within an explicitly supplied source root. The
compiler shall not fetch imports from the network.

## 5. Compiler interface

The public compiler module should expose only two essential operations:

```julia
compile(sources::Vector{SourceFile}, options::CompileOptions)::CompileResult
emit(spec::CheckedSpec, target::EmitTarget)::ArtifactBundle
```

`compile` shall be deterministic and free of external I/O. The CLI adapter is
responsible for reading files and supplying their logical paths and contents.
`emit` shall return artifacts rather than writing them. A filesystem adapter
may write an `ArtifactBundle` after successful generation.

The initial CLI should be:

```text
aifspec check <source-root>
aifspec fmt [--check] <source-root>
aifspec build <source-root> --target <json|julia|lean|markdown|rdf>
aifspec diff <old-source-root> <new-source-root>
```

`aifspec diff` should report semantic changes by stable ID, independently of
file movement or formatting.

## 6. AFSpec 0.1 language specification

The words **shall**, **should**, and **may** in this section describe AFSpec
itself. They do not reproduce requirements from P3109.

### 6.1 Encoding and lexical rules

- Source files shall be UTF-8.
- Keywords and identifiers shall use ASCII. Unicode may occur in strings and
  documentation text.
- Identifiers shall match `[A-Za-z][A-Za-z0-9_]*`.
- `INTEGER` shall match `0|[1-9][0-9]*`; signs are unary operators, and leading
  zeroes are forbidden. `DECIMAL` shall match `[0-9]+\.[0-9]+`; exponent
  notation is deliberately absent in version 0.1.
- Keywords are lowercase and reserved.
- Declaration names preserve the standard's spelling. New non-standard
  declarations should use `UpperCamelCase`; local names use `lower_snake_case`.
- `//` begins a line comment. `/* ... */` comments shall not nest.
- `///` introduces documentation attached to the following declaration.
- `STRING` is a double-quoted string with the escapes `\"`, `\\`, `\n`, `\r`,
  `\t`, and `\u{...}`. Triple-double-quoted strings contain normalized UTF-8
  documentation text and may span lines; only the delimiter itself is escaped.
- Tabs are forbidden outside string literals.
- Semicolons terminate declarations and statements. Newlines are not
  significant.
- A trailing comma is permitted in every comma-separated list.
- The canonical formatter uses four-space indentation and one declaration per
  logical block.

### 6.2 Grammar

The following EBNF defines the required syntactic core. `IDENT`, `STRING`,
`INTEGER`, and `DECIMAL` are lexical tokens.

```ebnf
source          = module-decl, { import-decl }, { declaration } ;

module-decl     = "module", qualified-id, "revision", STRING,
                  "language", STRING, ";" ;
import-decl     = "import", qualified-id, [ "as", IDENT ], ";" ;
qualified-id    = IDENT, { ".", IDENT } ;

declaration     = { annotation },
                  ( document-decl | enum-decl | type-decl | format-decl |
                    set-decl | primitive-decl | function-decl |
                    operation-decl | requirement-decl | note-decl |
                    example-decl ) ;

annotation      = "@", IDENT, "(", [ named-args ], ")" ;
named-args      = named-arg, { ",", named-arg }, [ "," ] ;
named-arg       = IDENT, "=", literal ;

document-decl   = "document", IDENT, "{", { field-assignment }, "}" ;
field-assignment= IDENT, "=", literal, ";" ;

enum-decl       = "enum", IDENT, "{", enum-item, { enum-item }, "}" ;
enum-item       = IDENT, ";" ;

type-decl       = "type", IDENT, "=", type-expr,
                  [ "where", expression ], ";" ;

format-decl     = "format", IDENT, "(", [ parameters ], ")",
                  [ "where", constraint-block ], ";" ;
parameters      = parameter, { ",", parameter }, [ "," ] ;
parameter       = IDENT, ":", type-expr ;
constraint-block= "{", { constraint-stmt }, "}" ;
constraint-stmt = "require", expression, [ "when", expression ], ";" ;

set-decl        = "set", IDENT, [ "<", parameters, ">" ],
                  "=", expression, ";" ;

primitive-decl  = "primitive", "function", IDENT,
                  [ type-parameters ], "(", [ parameters ], ")",
                  "->", type-expr, ";" ;

function-decl   = [ "partial" ], "function", IDENT,
                  [ type-parameters ], "(", [ parameters ], ")",
                  "->", type-expr, behavior-block ;

operation-decl  = [ "partial" ], "operation", IDENT,
                  [ type-parameters ], "(", [ parameters ], ")",
                  "->", type-expr, behavior-block ;

type-parameters = "<", parameters, ">" ;
behavior-block  = "behavior", "first_match", "{",
                  case-clause, { case-clause }, [ default-clause ], "}" ;
case-clause     = { annotation }, "case", IDENT, [ pattern-list ],
                  [ "when", expression ], "=>", result-body, ";" ;
default-clause  = "default", IDENT, "=>", result-body, ";" ;
pattern-list    = "(", [ patterns ], ")" ;
patterns        = pattern, { ",", pattern }, [ "," ] ;
pattern         = "_" | literal | binding-pattern | entity-pattern |
                  set-pattern ;
binding-pattern = "bind", IDENT ;
entity-pattern  = entity-ref, [ "(", [ patterns ], ")" ] ;
set-pattern     = "{", [ patterns ], "}" ;
result-body     = expression |
                  "{", { "let", IDENT, "=", expression, ";" },
                  "return", expression, ";", "}" ;

requirement-decl= "requirement", IDENT,
                  [ "(", [ parameters ], ")" ], "{",
                  { modality, expression, ";" }, "}" ;
modality        = "shall" | "should" | "may" ;

note-decl       = "note", IDENT, "about", entity-ref,
                  "{", "text", STRING, ";", "}" ;
example-decl    = "example", IDENT, "about", entity-ref,
                  "{", "text", STRING, ";", "}" ;
entity-ref      = qualified-id ;

type-expr       = qualified-id, [ "<", type-args, ">" ] |
                  "(", type-expr, { ",", type-expr }, ")" ;
type-args       = expression, { ",", expression }, [ "," ] ;

expression      = conditional | quantifier | implication ;
conditional     = "if", expression, "then", expression,
                  "else", expression ;
quantifier      = ( "forall" | "exists" ), IDENT, "in", expression,
                  ":", expression ;
implication     = disjunction, [ "=>", implication ] ;
disjunction     = conjunction, { "or", conjunction } ;
conjunction     = comparison, { "and", comparison } ;
comparison      = set-expr,
                  [ comparison-op, set-expr ] ;
set-expr        = additive,
                  { ( "union" | "intersect" ), additive } ;
additive        = multiplicative, { ( "+" | "-" ), multiplicative } ;
multiplicative  = unary-expr,
                  { ( "*" | "/" | "div" | "mod" ), unary-expr } ;
unary-expr      = unary-op, unary-expr | power-expr ;
power-expr      = postfix-expr, [ "^", unary-expr ] ;
postfix-expr    = primary, { specialization-suffix | call-suffix |
                             index-suffix | field-suffix } ;
specialization-suffix = "{", type-args, "}" ;
call-suffix     = "(", [ arguments ], ")" ;
index-suffix    = "[", expression, "]" ;
field-suffix    = ".", IDENT ;
arguments       = expression, { ",", expression }, [ "," ] ;
primary         = literal | IDENT | tuple | sequence | set |
                  "(", expression, ")" ;
tuple           = "(", expression, ",", expression,
                  { ",", expression }, [ "," ], ")" ;
sequence        = "[", [ arguments ], "]" ;
set             = "{", [ arguments ], "}" ;

comparison-op   = "==" | "!=" | "<" | "<=" | ">" | ">=" | "in" ;
unary-op        = "not" | "+" | "-" ;
literal         = INTEGER | DECIMAL | STRING | "true" | "false" |
                  "nan" | "pos_inf" | "neg_inf" ;
```

The implementation shall publish a machine-readable grammar generated from the
same grammar source used by the parser. The EBNF and parser shall not be
maintained independently.

### 6.3 Modules, imports, and names

A corpus has one root module and zero or more imported modules:

```text
module p3109.d1 revision "2026-09-07" language "0.1";

import p3109.vocabulary;
import p3109.projection as projection;
```

The module revision identifies the modeled document revision; the language
version identifies AFSpec syntax and semantics. They are independent.

Imports form a directed acyclic graph. Every reference is resolved by qualified
semantic name, not by filename. Wildcard imports are forbidden. An import cycle,
missing import, duplicate declaration, or ambiguous unqualified name is an
error.

### 6.4 Required provenance

Every normative declaration shall have a stable ID, status, and source:

```text
@id(value="p3109.format.Binary")
@status(value="normative")
@source(document="ieee-p3109-d1-2026-09-07", clause="3.1", page=16)
format Binary(
    bitwidth: Bitwidth,
    precision: Precision,
    signedness: Signedness,
    domain: Domain,
) where {
    require precision < bitwidth when signedness == Signed;
    require precision <= bitwidth when signedness == Unsigned;
};
```

Because `when` is useful in constraints, AFSpec 0.1 shall treat
`require A when B;` as defined syntax sugar for `require B => A;`. The grammar
includes both the guarded form and the unguarded `require A;` form.

Stable IDs are never derived from page numbers, heading text, filenames, or
target-language names. Moving a declaration does not change its ID. Splitting or
merging normative concepts requires explicit `@supersedes` metadata rather than
reusing an ID with a different meaning.

Page numbers aid navigation but do not identify clauses. A source record may
also carry a source-span digest when the source document permits reliable text
extraction.

### 6.5 Semantic types

AFSpec shall provide these intrinsic types:

| Type | Meaning |
|:--|:--|
| `Bool` | `true` or `false` |
| `Int` | Unbounded mathematical integer |
| `Nat` | Integer greater than or equal to zero |
| `Rational` | Exact ratio of integers |
| `Real` | Mathematical real, possibly represented symbolically |
| `ExtendedReal` | `Real`, `neg_inf`, `pos_inf`, or `nan` |
| `String` | UTF-8 text |
| `Type` | The kind of value types, usable only in type-parameter bounds |
| `Format` | A valid format instance |
| `Value<f>` | An encoded value whose format is exactly `f` |
| `Code<f>` | An integer code point in the range of `f` |
| `OperationRef` | A resolved operation specialization, without invocation |
| `Implementation` | An abstract subject evaluated for conformance |
| `Sequence<T,n>` | A length-`n` sequence of `T` |
| `Set<T>` | A mathematical set of `T` |
| `Option<T>` | `some(T)` or `none(reason)` |

`Value<f>` and `Code<f>` are indexed types. A value in one format cannot be
passed where another format is required without an explicit conversion.
`Datum` should be declared as a domain name for `ExtendedReal`; it shall not be
conflated with `Value<f>`.

`some(value)` and `none(reason)` are intrinsic `Option` constructors. A reason
is a stable, nonempty string intended for diagnostics and semantic diffs, not
free-form target-language exception text.

There are no implicit numeric narrowing conversions. The safe inclusions
`Nat -> Int -> Rational -> Real` may be inserted by the checker. Conversion in
the opposite direction requires an explicit checked function.

### 6.6 Exact arithmetic

Integer literals are unbounded. Decimal literals denote exact rationals:

```text
0.1       // exactly 1/10
1.25      // exactly 5/4
2 ^ -11   // an exact rational
```

No AFSpec literal denotes an IEEE binary hardware float. Hexadecimal integer
literals may be added in a later language version, but shall still denote exact
integers.

`/` denotes exact rational division and is undefined when its divisor is zero.
`div` and `mod` denote Euclidean integer division and remainder, with a
strictly positive divisor. Exponentiation requires an integer exponent; a
negative exponent additionally requires a nonzero base and produces a
rational or real result. The type checker shall reject expressions whose
undefinedness is statically apparent and otherwise create a proof obligation
for the relevant precondition.

Functions such as logarithm, square root, and exponential return mathematical
reals. When the result cannot be represented by the exact algebraic fragment,
the IR retains a symbolic application such as `math.log(2)`. An execution
adapter may approximate such a term only under an explicit accuracy contract;
the approximation is not substituted into the canonical semantic IR.

`nan`, `pos_inf`, and `neg_inf` are constructors of `ExtendedReal`. AFSpec has no
mathematical negative zero. External encodings that distinguish negative zero
must represent it as an encoded `Value<f>`, not as a second zero datum.

### 6.7 Formats and values

A format declaration introduces a format family. Applying it to arguments
produces a format instance:

```text
enum Signedness { Signed; Unsigned; }
enum Domain { Finite; Extended; }

type Bitwidth = Nat where value > 2;
type Precision = Nat where value > 0;

@id(value="p3109.format.Binary")
@status(value="normative")
@source(document="ieee-p3109-d1-2026-09-07", clause="3.1", page=16)
format Binary(
    bitwidth: Bitwidth,
    precision: Precision,
    signedness: Signedness,
    domain: Domain,
) where {
    require signedness == Signed => precision < bitwidth;
    require signedness == Unsigned => precision <= bitwidth;
};

set RequiredF8 = {
    Binary(8, 4, Signed, Extended),
    Binary(8, 3, Signed, Extended),
};
```

The supporting enum and refinement declarations in this compact example omit
their annotations for readability. Production AFSpec shall give each one the
required stable ID, status, and source.

Within a type refinement, `value` is an implicit immutable binding of the base
type. It is not in scope outside that refinement.

The IR shall distinguish:

```text
FormatFamily       Binary
FormatInstance     Binary(8, 4, Signed, Extended)
Code<f>            an integer constrained by BitwidthOf(f)
Value<f>           an encoded floating-point value in f
Datum              a closed extended real value
```

Code-point arithmetic is never implicit. It uses explicit functions:

```text
code_of(x)               // Value<f> -> Code<f>
checked_code{f}(i)       // Int -> Option<Code<f>>
value_from_code{f}(code) // Code<f> -> Value<f>
decode{f}(x)             // Value<f> -> Datum
encode{f}(datum)         // Datum -> Value<f>, under its declared precondition
```

Arithmetic on a `Code<f>` produces an `Int`, not another `Code<f>`.
`checked_code` is therefore required before converting an arithmetic result
back to a value. This makes it impossible to accidentally leave the format's
code range or add `1` to a mathematical datum when the standard intends to
advance an encoded code point.

### 6.8 Functions, primitives, and operations

A `function` is a pure semantic helper. An `operation` is an externally visible
standard operation that may have required specializations. Both are referentially
transparent.

A `primitive function` is part of the trusted semantic vocabulary and has no
AFSpec body:

```text
primitive function floor(x: Real) -> Int;
primitive function log2(x: Real) -> Real;
primitive function abs(x: Real) -> Real;
```

Every primitive shall have:

- A stable ID and mathematical contract.
- At least one reference adapter.
- Tests shared by every adapter.
- A declaration of whether it is computable, symbolic, or both.

Adding a primitive expands the trusted base and therefore requires explicit
review. Target convenience is not sufficient reason to add one.

An operation's type parameters precede its operands:

```text
operation Convert<from: Format, to: Format, rho: Projection>(
    x: Value<from>,
) -> Value<to> behavior first_match {
    // cases
}
```

At an expression site, braces specialize a generic declaration and parentheses
invoke it: `Convert{from, to, rho}(x)`. A specialization without invocation,
such as `IsNaN{f}`, is a first-class `OperationRef` used by conformance
requirements. Braces deliberately avoid the parsing ambiguity between
angle-bracket specialization and numerical comparison.

### 6.9 Guarded, ordered equations

`behavior first_match` is normative. Cases are tested in source order. The first
case whose pattern matches and whose guard evaluates to `true` supplies the
result. No later case is evaluated.

The following is a complete, non-P3109 example of the rule mechanism:

```text
enum Sign { Negative; Zero; Positive; }

@id(value="example.function.SignOf")
@status(value="interpretation")
@source(document="usingdsl-design", clause="6.9")
function SignOf(x: Int) -> Sign behavior first_match {
    case negative (bind candidate) when candidate < 0 => Negative;
    case zero (0) => Zero;
    default positive => Positive;
}
```

`bind candidate` introduces a new immutable case-local variable. An unbound
name without `bind` is an entity reference and must resolve to an enum item,
constructor, or other pattern-capable declaration. Repeating a binding within
one pattern is forbidden; equality relationships belong in a guard. A case's
bindings are in scope in its guard and result only.

Every case name is stable within its enclosing declaration and becomes part of
the rule's stable ID. Reordering cases is a semantic change and shall change the
semantic digest.

The checker shall report:

- A case proved unable to match because earlier cases cover it.
- Overlap proved between cases. Overlap is permitted under first-match
  semantics but must be acknowledged with `@overlap(reason="...")` on the
  later case.
- A missing result path in any function or operation.
- A `default` case that is not last.
- More than one `default` case.
- A guard that is not `Bool`.
- A result that does not inhabit the declared result type.

A declaration is total unless marked `partial`. A partial declaration shall
explicitly declare `Option<T>` as its result and shall return `some(value)` or
`none("stable.reason.code")` on every path. `partial` does not permit a hidden
fall-through case: exhaustiveness is still required. The checker rejects a
partial declaration with a non-`Option` result. In a partial declaration,
`none` denotes semantic undefinedness; in a non-partial declaration returning
`Option<T>`, it is an ordinary defined result. An adapter shall not turn
undefinedness into an exception unless its target interface explicitly
requires that mapping.

### 6.10 Bindings, recursion, and evaluation

Bindings in a result block are immutable and evaluated in order. Shadowing is
forbidden. Function and operation arguments are immutable.

Recursive calls must be structurally decreasing or accompanied by a termination
measure:

```text
@id(value="example.function.Factorial")
@status(value="interpretation")
@source(document="usingdsl-design", clause="6.10")
@decreases(parameter="n", measure="identity")
function Factorial(n: Nat) -> Nat
behavior first_match {
    case base (0) => 1;
    case step (bind k) when k > 0 => k * Factorial(k - 1);
}
```

The termination checker can discharge this example because the recursive
argument is a natural number strictly smaller than `n`. A declaration outside
the checker's termination fragment produces a proof obligation rather than an
unchecked recursion escape.

Evaluation shall be deterministic. There is no ambient clock, random generator,
filesystem, environment, mutable global state, or target rounding mode.
Stochastic-rounding bits are explicit operands or parameters.

### 6.11 Collections and quantifiers

Sets are mathematical and unordered. Sequences are ordered and indexed from
one, matching the standard's notation. Index zero is an error unless a future
module defines a different indexed collection type explicitly.

Quantifiers range only over a statically typed set:

```text
forall f in RequiredF8: provides(implementation, IsNaN{f})
```

An executable adapter may evaluate a quantifier only when its domain is finite
and enumerable. Otherwise it remains a logical expression for proof and query
adapters.

### 6.12 Conformance requirements

Conformance is represented separately from operation behavior:

```text
@id(value="p3109.requirement.required_classifiers")
@status(value="normative")
@source(document="ieee-p3109-d1-2026-09-07", clause="4.5", page=22)
requirement RequiredClassifiers(implementation: Implementation) {
    shall forall f in RequiredF4 union RequiredF8:
        provides(implementation, IsNaN{f});
    shall forall f in RequiredF4 union RequiredF8:
        provides(implementation, IsFinite{f});
}
```

`provides(Implementation, OperationRef) -> Bool` is an intrinsic conformance
predicate. A conformance adapter supplies its facts; AFSpec operation semantics
do not inspect an implementation object.

`shall`, `should`, and `may` are stored as requirement modalities. Only a failed
`shall` makes an implementation nonconforming. A `should` may produce an
advisory; a `may` records a permitted capability and never produces a failure.

The checker shall reject a normative requirement expressed only as free text.
Its executable or logical predicate is mandatory. A verbatim source excerpt may
be attached as provenance but is not the predicate.

### 6.13 Informative notes and examples

Informative material is represented explicitly:

```text
@id(value="p3109.note.scaled_power_of_two")
@status(value="informative")
@source(document="ieee-p3109-d1-2026-09-07", clause="5.8", page=70)
note ScaledPowerOfTwo about ScaledOperation {
    text "A scale format with precision one can restrict scales to powers of two.";
}
```

Notes and examples may refer to semantic entities, but normative declarations
shall not depend on notes or examples. The compiler shall reject a dependency
edge from normative semantics to informative prose.

Examples that contain evaluable expressions should carry expected results in a
future structured `check` field. Until that field is specified, prose examples
are documentation only.

### 6.14 Annotation vocabulary

AFSpec 0.1 reserves these annotations:

| Annotation | Purpose |
|:--|:--|
| `@id(value=...)` | Stable semantic identity |
| `@status(value=...)` | `normative`, `informative`, or `interpretation` |
| `@source(...)` | Document, clause, page, and optional span |
| `@supersedes(id=...)` | Explicit revision lineage |
| `@overlap(reason=...)` | Review of intentional first-match overlap |
| `@decreases(...)` | Termination measure for recursion |
| `@primitive_mode(value=...)` | `computable`, `symbolic`, or `both` |

Unknown annotations are errors unless declared in a namespaced extension module.
Generators shall preserve unknown extension annotations in canonical JSON but
may ignore them only when the extension declares that behavior safe.

### 6.15 Expression precedence

From lowest to highest precedence:

1. `=>`
2. `or`
3. `and`
4. `==`, `!=`, `<`, `<=`, `>`, `>=`, `in`
5. `union`, `intersect`
6. `+`, `-`
7. `*`, `/`, `div`, `mod`
8. Unary `not`, `+`, `-`
9. `^` (right associative)
10. Specialization, calls, indexing, and field selection

Chained comparisons are forbidden. Write `0 <= x and x < limit`, not
`0 <= x < limit`.

### 6.16 Equality and special values

`==` is typed structural equality. Consequently, the `nan` datum is structurally
equal to itself inside specification patterns. IEEE-style numerical comparisons
are named operations such as `CompareEqual`; they are not implemented by the
DSL's structural equality operator.

This distinction prevents host-language NaN behavior from affecting pattern
matching, set membership, or rule analysis.

### 6.17 Errors and diagnostics

Diagnostics shall include:

- A stable diagnostic code.
- Severity: error, warning, or advisory.
- Logical source path and source span.
- Stable ID of the affected entity when resolution reached that stage.
- A primary explanation and, where possible, a corrective suggestion.
- Related spans for duplicate names, conflicting rules, or dependency cycles.

The compiler shall not generate any target artifacts after an error. Warnings
do not alter semantics and shall be promotable to errors in CI.

## 7. Canonical IR

The in-memory IR should use closed, immutable Julia types. It should not retain
parser nodes after lowering. A representative shape is:

```julia
abstract type Decl end
abstract type SpecExpr end
abstract type SpecType end

struct StableId
    value::String
end

struct SourceRef
    document::StableId
    clause::String
    page::Union{Nothing,Int}
    span::Union{Nothing,UnitRange{Int}}
end

struct BehaviorCase
    id::StableId
    patterns::Vector{Pattern}
    guard::SpecExpr
    result::SpecExpr
    acknowledged_overlap::Union{Nothing,String}
    source::SourceRef
end

struct OperationDecl <: Decl
    id::StableId
    name::Symbol
    type_parameters::Vector{Parameter}
    operands::Vector{Parameter}
    result::SpecType
    cases::Vector{BehaviorCase}
    total::Bool
    source::SourceRef
end

struct CheckedSpec
    language_version::VersionNumber
    module_revision::String
    declarations::Vector{Decl}
    semantic_digest::NTuple{32,UInt8}
end
```

These are illustrative implementation types, not an additional schema. The
canonical JSON schema is generated from the actual IR definitions and checked
against golden fixtures.

Canonical JSON shall:

- Sort declarations by stable ID, not source order, except that behavior cases
  retain normative case order.
- Encode an unbounded integer as a canonical base-10 string. Encode a rational
  as an object containing canonical numerator and positive-denominator strings,
  reduced to lowest terms.
- Encode every expression with an explicit node tag.
- Contain no target-specific names.
- Normalize maps by key and use UTF-8 without insignificant whitespace.
- Reject duplicate keys and noncanonical numeric spellings.

## 8. Generated adapters

Each adapter consumes `CheckedSpec` and returns an `ArtifactBundle`.

### 8.1 Julia adapter

Julia names belong in `spec/p3109/target-mappings/julia.toml`:

```toml
[entities]
"p3109.format.Binary" = "BinaryFormat"

[indexed_types]
"Value:p3109.format.Binary" = "Binary"
```

The `Value:` key is a closed adapter-defined pattern for the intrinsic indexed
type; it does not create an AFSpec entity. The mapping is target configuration,
not standard semantics. The adapter shall reject two stable IDs or type
patterns mapping to the same Julia binding unless an explicit alias
relationship exists.

Generated optimized methods shall be tested against the IR interpreter. The
interpreter is the behavioral oracle; hand-optimized methods are adapters and
must demonstrate equivalence over all enumerable narrow formats and with
property tests elsewhere.

### 8.2 Lean adapter

The Lean adapter should generate inductive types, definitions, and theorem
statements from the IR. Initially it may leave proof bodies as explicit goals.
Eventually it should establish:

- Rule determinism and declared exhaustiveness.
- Encoding/decoding properties.
- Format-constraint consistency.
- Agreement between generated executable definitions and declarative cases.

Lean is a verification target, not the authoring source. Handwritten lemmas may
import generated definitions, but shall not redefine them.

### 8.3 Markdown adapter

The Markdown adapter shall preserve standard names, clause relationships,
normative status, and equations. Presentation templates may choose notation,
but a notation mapping must be explicit and tested. Generated Markdown should
link every operation and rule back to its stable ID and source clause.

### 8.4 Knowledge-graph adapter

Generate RDF/Turtle using:

- RDF 1.1 named graphs for document revisions.
- PROV-O for derivation and revision provenance.
- SHACL for graph validation.
- Explicit assertion nodes for statement-level provenance.

The initial vocabulary should include:

```text
Classes:
  DocumentRevision, Clause, Definition, FormatFamily, FormatInstance,
  DatumType, Operation, OperationSpecialization, BehaviorRule,
  ConformanceRequirement, Note, Example, Citation, Interpretation

Relations:
  definedBy, specializes, uses, calls, constrains, requires, hasRule,
  precedesRule, cites, supersedes, generatedFrom, conformsTo,
  conflictsWith, clarifiedBy

Properties:
  normativeStatus, modality, sourcePage, sourceSpan, revision,
  sourceDigest, semanticDigest, caseOrder, approximationStatus
```

Graph nodes use stable AFSpec IDs. The graph may repeat an expression in a query-
friendly form, but the canonical IR remains authoritative.

## 9. Static analysis requirements

Before producing a `CheckedSpec`, the compiler shall perform:

1. Lexical and grammar validation.
2. Module and import resolution.
3. Stable-ID uniqueness and provenance validation.
4. Name and type resolution.
5. Refinement-constraint checking where decidable.
6. Rule guard and result type checking.
7. Rule overlap and reachability analysis.
8. Exhaustiveness checking for every behavioral declaration.
9. Dependency-cycle and recursion-termination analysis.
10. Normative-to-informative dependency rejection.
11. Primitive trusted-base reporting.
12. Canonicalization and semantic-digest computation.

When a proof is undecidable or outside the compiler's solver fragment, the
compiler shall report an explicit proof obligation. It shall never silently
assume the proposition. A checked specification may contain discharged proof
obligations only; an option such as `--allow-obligations` may produce an
analysis artifact but not normative generated code.

## 10. Testing strategy

The compiler and corpus need complementary tests.

### 10.1 Compiler tests

- Golden parsing and canonical-format tests.
- A negative fixture for every diagnostic code.
- Type-checking tests for indexed values and explicit conversions.
- Case-overlap, reachability, and exhaustiveness tests.
- Canonical JSON round-trip and deterministic-digest tests.
- Resource-limit and malicious-input tests.

### 10.2 Specification tests

- At least one example for every normative operation.
- Exhaustive evaluation for all code points of required 4- and 8-bit formats
  where the mathematical primitive is executable.
- Cross-checks against the current Julia implementation.
- Metamorphic properties such as decode/encode round trips, extrema ordering,
  and next-greater/next-less relationships.
- Explicit tests for NaN, infinities, zero, subnormals, saturation boundaries,
  and stochastic-bit endpoints.
- Provenance coverage: every normative entity resolves to a source clause.

### 10.3 Adapter tests

Every generator shall have golden output tests. Generated Julia shall be tested
against the interpreter. Generated Lean shall compile. RDF output shall conform
to its SHACL shapes. Markdown shall parse and contain every required stable ID.

CI should run:

```text
aifspec fmt --check spec/p3109
aifspec check spec/p3109
aifspec build spec/p3109 --target all
git diff --exit-code -- generated/spec
julia --project=. -e 'using Pkg; Pkg.test()'
lake build                         # once the Lean adapter exists
shacl validate ...                 # exact command chosen with the RDF adapter
```

## 11. Versioning and compatibility

AFSpec language versions use semantic versioning independently of P3109
revisions.

- A patch release clarifies diagnostics or fixes behavior that contradicted the
  published language specification.
- A minor release adds backward-compatible syntax or IR nodes.
- A major release changes parsing or semantics of valid existing source.

Each corpus pins one AFSpec language version. The compiler may read older minor
versions but emits only its canonical current IR after an explicit migration.
Migrations are named, deterministic transformations with before-and-after
fixtures. They never rewrite stable IDs automatically.

A P3109 revision is represented by a new module revision and provenance graph.
Semantic diffing reports additions, removals, rule reorderings, changed
constraints, changed modalities, and changed source references.

## 12. Security and reproducibility

- No network access during compilation.
- No arbitrary host-language evaluation.
- Imports remain under the supplied source root and may be digest-pinned.
- Parser nesting, integer size, collection size, and analysis time have
  configurable limits with deterministic failures.
- Diagnostics never include environment variables or unrelated file contents.
- Canonical output is independent of locale, timezone, filesystem ordering, and
  Julia hash randomization.
- Generators receive explicit versions and options; they do not inspect ambient
  package state.

## 13. Implementation sequence

### Phase 1: Prove the model

Implement the immutable IR, diagnostics, canonical JSON, and a minimal parser.
Model only:

- §3.1 format parameters and constraints.
- §4.7.2 decoding.
- §4.7.4 rounding to precision.
- §4.16 next greater and next less.

These clauses exercise indexed values, exact arithmetic, special values,
ordered rules, recursion, and provenance. Do not model the entire draft until
this slice produces useful diagnostics and stable generated output.

### Phase 2: Establish the behavioral oracle

Add the pure reference interpreter and exhaustive tests for narrow formats.
Generate Julia tests before generating optimized Julia implementation code.

### Phase 3: Add projections and conformance

Model saturation, conversion, required format sets, operation specializations,
and conformance modalities. Generate the existing declaration report from the
checked IR.

### Phase 4: Add block operations

Extend the grammar deliberately for sequence-rest patterns and indexed
stochastic rounding. Do not encode these through untyped escape expressions.

### Phase 5: Add provenance and proof adapters

Generate RDF/Turtle plus SHACL validation, then Lean definitions and proof
obligations. These are real adapters only after the JSON/Julia path has
established the seam.

### Phase 6: Make AFSpec authoritative

Only after semantic equivalence has been demonstrated:

1. Generate the retained Markdown reference from AFSpec.
2. Generate implementation registries and conformance tables.
3. Remove duplicated handwritten declarations.
4. Make generated-artifact freshness a required CI check.

## 14. Acceptance criteria

AFSpec is ready to become authoritative when all of the following hold:

- The published grammar and parser come from one grammar source.
- The pilot clauses compile without unresolved proof obligations.
- Formatting twice produces identical bytes.
- Canonical JSON round-trips without semantic change.
- Builds are byte-for-byte deterministic on supported platforms.
- All normative declarations have stable IDs and source references.
- Every total operation passes exhaustiveness analysis.
- Every intentional rule overlap is documented.
- Required narrow-format behavior agrees exhaustively with the Julia reference.
- Julia naming changes can be made solely in the target mapping and adapter.
- Generated RDF passes SHACL validation.
- Generated Lean definitions compile.
- CI detects every stale generated artifact.

## 15. Principal design risks

**Building syntax before stabilizing the IR.** Mitigate this by implementing the
pilot slice and canonical JSON first. The surface language should follow the
semantic model rather than determine it accidentally.

**Creating several sources of truth.** Julia, Lean, Markdown, and RDF are output
adapters. They may add presentation or proofs, but may not redefine operations.

**Making the trusted primitive base too large.** Every primitive is a semantic
assumption. Keep the set small, publish it, and require adapter agreement tests.

**Confusing mathematical and encoded values.** Preserve `Datum`, `Code<f>`, and
`Value<f>` as distinct types and require explicit encode/decode operations.

**Treating first-match order as formatting.** Case order is semantic, retained in
canonical IR, represented in the graph, and included in semantic diffs.

**Letting target names alter the model.** Standard names and stable IDs belong to
AFSpec. `BinaryFormat` versus `Binary` in Julia is an adapter decision.

**Overcommitting to formal proof too early.** Generate Lean only after the IR and
reference interpreter stabilize, but design the IR so that exact terms and proof
obligations are never lost.

## 16. External specifications used by the proposed adapters

- Lean 4 documentation: <https://lean-lang.org/theorem_proving_in_lean4/>
- W3C PROV-O: <https://www.w3.org/TR/prov-o/>
- W3C SHACL: <https://www.w3.org/TR/shacl/>
- W3C RDF 1.1 Concepts: <https://www.w3.org/TR/rdf11-concepts/>

These technologies support verification and provenance adapters. AFSpec does
not depend on them to parse or type-check its canonical source.
