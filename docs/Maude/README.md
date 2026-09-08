# P3109/D1 in Core Maude

This is an executable rational specification of the permitted September 2026
IEEE P3109/D1 draft, with a symbolic extension and separate mathematical
contracts. It follows [planmaude.md](planmaude.md). The plan's referenced
`asspec.md` was **not read** because the implementation request excluded it;
the permitted PDF supplies the arithmetic definitions directly.

The draft is unapproved. These artifacts model its definitions; neither a
successful load nor a test run establishes full implementation conformance.
See [the evidence and remaining obligations](proofs/obligations.tsv).

## First use

Use `docs/Maude/` as the working directory:

```sh
cd docs/Maude
maude -no-banner -no-ansi-color load-core.maude
```

At the Maude prompt:

```maude
red in P3109-CORE : Convert(
  Binary(8, 4, Signed, Extended), Binary(4, 2, Signed, Finite),
  proj(NearestTiesToEven, SatNone), 72) .
```

The result is code **6**, representing **2** in `Binary4p2sf`. The source
operand is code 72, representing 2 in `Binary8p4se`. Follow the generated
`p3109-scalar-Convert` equation in [scalar-ops.maude](lib/scalar-ops.maude),
then [project.maude](lib/project.maude), [rounding.maude](lib/rounding.maude),
[saturation.maude](lib/saturation.maude), and [codec.maude](lib/codec.maude).
Their labels link to clauses and printed pages in
[traceability.tsv](inventory/traceability.tsv).

For batch examples:

```sh
maude -no-banner -no-ansi-color examples/core.maude
maude -no-banner -no-ansi-color examples/symbolic.maude
```

The three loaders are alternatives, each used in a fresh process:

| Loader | Public entry point | Capability |
| --- | --- | --- |
| `load-core.maude` | `P3109-CORE` | Internal codecs, rational projection, arithmetic/extrema, predicates, order/Next, blocks, required-set and finite κ helpers |
| `load-symbolic.maude` | `P3109-SYMBOLIC` | Core plus elementary expressions, exact selected cases, scalar/block/scaled wrappers |
| `load-contracts.maude` | Theories and an uninstantiated external bridge | Obligations for mathematical reals and external codecs; no backend implementation |

## Values and calls

`Binary(K, P, Signedness, Domain)` is a syntactic format term. Valid formats
have `K > 2`, `P > 0`, and `P < K` when signed or `P <= K` when unsigned.
`validFormat` enforces those restrictions. Metadata for `binary64`, `binary32`,
`binary16`, and `BFloat16` is supplied by the draft's §4.14 table; their codecs
and code-valued bounds remain external interfaces.

`Rat < Real < Number < XReal`, with `Infinity < Number`. The extra `Number`
sort separates non-NaN values in guards. `nan`, `posInf`, and `negInf` denote
the draft's NaN, +∞, and −∞. There is one zero and one NaN datum.

Public numeric calls take **all parameters first, then operands**, in the
order recorded in [operations.json](inventory/operations.json). Operands and
results are integer **code points**; `omega...` kernels take decoded values.
For example, `Add(fx, fy, fr, rho, x, y)` and
`FMA(fx, fy, fz, fr, rho, x, y, z)` each perform one final projection.
`ArcTan2(fy, fx, fr, rho, y, x)` preserves the source's y-before-x order.

The six deterministic modes are `NearestTiesToEven`, `NearestTiesToAway`,
`TowardPositive`, `TowardNegative`, `TowardZero`, and `ToOdd`. The remaining
modes are `StochasticA(N, R)`, `StochasticB(N, R)`, and `StochasticC(N, R)`,
with `N >= 0` and `0 <= R < 2^N`. No randomness is generated internally.
A scalar specification is `proj(mode, SatNone | SatFinite | SatPropagate)`.

Ordered sequences use `ccons(code, tail)`/`cnil`, `xcons(value, tail)`/`xnil`,
and `rcons(random, tail)`/`rnil`. A block projection is `bproj(mode, sat)`;
stochastic block modes are `BlockStochasticA(N, randomSequence)` and the
analogous B/C forms. Sequence lengths must match the explicit positive block
size. Helper indexing is zero-based: source index i is helper index i−1.
`singletonLift` supplies the one-element stochastic sequence for scaled calls.

A block is `block(scaleCode, codeSequence)`. Public block operation arguments
flatten each source tuple into scale and sequence arguments. For example:

```maude
red in P3109-CORE : BlockAdd(
  1,
  Binary(4, 2, Signed, Finite), Binary(4, 2, Signed, Finite),
  Binary(4, 2, Signed, Finite), Binary(4, 2, Signed, Finite),
  Binary(4, 2, Signed, Finite), Binary(4, 2, Signed, Finite),
  bproj(NearestTiesToEven, SatNone),
  4, ccons(4, cnil), 4, ccons(4, cnil), 4) .
```

This returns `block(4, ccons(6, cnil))`: the supplied result scale is 1, and
the element is 2. `BlockReduceAdd`, `BlockReduceMultiply`, and
`BlockDotProduct` produce a scalar code. `ConvertToBlockMaxAbsFinite` computes
and returns the result scale; ordinary elementwise operations preserve their
supplied result scale.

`validCode`, `datum`, `validProjection`, `validBlockProjection`, and
`validBlock` expose domain checks. Invalid public applications remain
unreduced; they are different from specified NaN results. For example,
`datum(Binary(8, 4, Signed, Extended), 240)` is false, and encoding 240
remains a residual application. Printed kind names such as `[XReal,FindResult]`
reflect Maude's imported kind graph; they are not numeric error datums.
Internal helpers are visible through imports but require their documented
caller invariants; they are not additional public operations.

## Symbolic values and contracts

The symbolic loader evaluates `omegaSqrt(9/16)` to `3/4`,
`omegaArcTan2Pi(1, -1)` to `3/4`, and `omegaTanPi(1/2)` to `posInf`.
`omegaSqrt(2)` produces `exprSqrt(2)`. Uncertified projection of that expression
remains residual. Tests distinguish these intentional residuals from results.

Use `xEq`, `xLt`, and `xLe` for mathematical comparisons. Syntactic Maude
`==` is used for test representations and ordinary metadata, never as an
inequality oracle for arbitrary symbolic reals. Domain-restricted expression
constructors use kind declarations and guarded membership: `exprLog(-1)`
and `exprSqrt(-1)` do not acquire sort `Real`.

The real theory states necessary field/order obligations; additional
mathematical completeness, rational embedding, and elementary-function
obligations are documented alongside it. It is not itself a complete,
executable construction of all real numbers. An implementation view must
preserve its equations; the present expression syntax does not establish
that simply by representing an addition or a square root.

Instantiating a real interface requires a backend module, a view mapping its
operations to the theory, proofs of the view obligations, and a parameterized
consumer instantiated with that view. A practical future backend could use
expressions plus certified enclosures under a **partial evaluation contract**:
return a result when a certificate proves the decision, otherwise retain an
unresolved term. That is weaker than implementing the full mathematical-real
contract. Rationals or algebraic numbers alone do not meet that full contract.
The optional enclosure evaluator is not implemented here; the equal-endpoint
`[-100,100]`/NaN counterexample is retained as a negative test.

The external bridge is parameterized by `P3109-EXTERNAL-FORMAT`. No concrete
view is supplied. Authorized external encoding definitions, a backend, and
proofs for NaN canonicalization, positive-zero encoding, datum membership,
bounds, and finite-value counts are prerequisites for such a view.

## Conformance accounting

`numeric(name, formatSequence, projection)` identifies a projected scalar
specialization. `plain(name, formatSequence)` identifies one without a
projection parameter; it can still have a code-valued result.
`required(identity, externalFormatSequence)` implements §4.5's parameter
restrictions, including scaled Add/Subtract/Multiply. All seven valid choices
of the nonempty external-format subset are tested: 341, 443, or 549 required
identities for subset sizes 1, 2, or 3.

`exact(...)`, `approximate(...)`, and `partitioned(...)` are declaration records.
`wellFormedDeclaration` checks the supported identity's name, arity,
formats, projection, and distinct approximate identifier; it rejects
approximation declarations for nonnumeric results. It does not prove that
an implementation computes those results. `blockElements`, `blockReduction`, and `blockScale` identify the three
block parameter schemas, including explicit sizes and separate scale/element
projection specifications where required. `hasDeclaration` and
`declarationsCover` check presence for supplied identities; the caller must
supply the complete required set when making a coverage claim.

`observation(id, operandCodes, resultFormat, definedCode, candidateCode)` is
explicit adapter data. `observationKappa` and `batchKappa` compute exact finite
rank distances, with NaN mismatch taking precedence over infinity mismatch.
`mergeKappa` also combines multiple results. `partition` checks a supplied finite universe and any number of explicitly
enumerated disjoint subsets; `partition2` is a two-subset convenience helper.
`partitioned` associates a declared κ with each subset, and
`declarationKappa` combines those declared bounds. Symbolically described
partitions and complete operand coverage require adapter evidence. Evidence tags are **claims supplied by an adapter**, not
certificates checked by Maude. A sampled maximum is not whole-domain κ.

## Validation and regeneration

Python 3 and Core Maude 3.5.1 are sufficient for ordinary tests. Runners locate
this directory themselves and also work from the repository root:

```sh
python3 docs/Maude/tools/run-tests.py --suite core
python3 docs/Maude/tools/run-tests.py --suite symbolic
python3 docs/Maude/tools/run-tests.py --suite order-full
python3 docs/Maude/tools/run-tests.py --suite core --profile symbolic
python3 docs/Maude/tools/run-tests.py --suite core --engine maude++
python3 docs/Maude/tools/check-inventory.py
python3 docs/Maude/tools/check-loads.py
python3 docs/Maude/tools/generate-wrappers.py --check
python3 docs/Maude/tools/run-proofs.py --suite eligible
```

Individual suites are `smoke`, `domains`, `codec`, `projection`, `scalar`,
`order-next`, `blocks`, `conformance`, and `symbolic`. Small standalone
`tests/*.maude` files demonstrate representative checks; the Python runner
executes the complete suites. It rejects warnings, advisories, missing or
unreduced assertions, missing completion sentinels, timeouts, and unexpected
process termination. Full ordering runs are chunked; no cubic eight-bit job
or D.2 candidate experiment is hidden in the runner.

`generate-wrappers.py` deterministically emits only repetitive scalar,
elementwise, and scaled schemas. The arithmetic kernels and conformance
requirements are handwritten. Independent table fixtures and the original
FMA/FAA oracle are not generated from those wrappers.

Proof runs use `MAUDE_PROOF_ENGINE` and `MFE_PATH`, or `--engine` and `--mfe`,
and retain raw logs under the system temporary directory by default. They
screen flattened constructor inputs, run CRC first, then schedule SCC in a
fresh process only after accepted CRC conclusions. Both the smoke target and
a saturation decision slice pass. Production RAT modules are outside this
checker profile; the slice's refinement remains a separate obligation.

See [coverage.md](proofs/coverage.md), [deviations.md](proofs/deviations.md),
[obligations.tsv](proofs/obligations.tsv), and
[source.json](inventory/source.json) for test scopes, proof qualifications,
source hashes, resolved tool paths, and component banners. Language/tool
references are the [official Maude documentation](https://maude.cs.illinois.edu/documentation)
and [MFE tool documentation](https://github.com/maude-team/MFE/wiki/Tools-available).


Two things I changed beyond the new file:

load-symbolic.maude and load-contracts.maude each pulled core with plain load load-core.maude. sload only skips files that were themselves sloaded, so chaining the three loaders redefined all 22 core modules and 9 views. Both now use sload; each loader is also clean standalone (0 advisories each).
The first draft of the header comment broke the lexer: Maude's --- comments are not opaque to parentheses, braces, or backticks. Rewritten as plain words. Worth knowing for the other .maude headers.
One design note in the file: P3109-SPEC imports P3109-SYMBOLIC (which already includes P3109-CORE). The contract theories P3109-REAL-CONTRACT / P3109-EXTERNAL-FORMAT and the parameterized P3109-EXTERNAL-BRIDGE{B} are loaded into the module database but can't be imported by an fmod — they need a view to instantiate, which is exactly the "external-format contract remains open" obligation in asspec.md.


====

Two translator warnings:
- (Resolved.) Three equations used owise, the `false` fallbacks of `numericArity`, `plainArity` and `blockElementArity` in lib/conformance.maude. maude2lean emits an owise equation as a plain unconditional axiom, so alongside the positive rows it would derive true = false. They are now membership in explicit finite tables (`numericArityTable` etc.) by structural recursion (`inArityTable`), with no owise and no conditions; the old and new definitions agree on all 5,820 name/arity pairs checked, and the translator no longer warns. No owise remains anywhere in the specification.
- 75 special operators (Maude builtins from NAT/INT/RAT/STRING etc.) have no equational definition; they appear as uninterpreted constructors without axioms.

..

Only three equations, all in conformance.maude: the false fallbacks for numericArity, plainArity, blockElementArity. Each pairs with ceq … = true if A == k /\ (N == "Add" or N == …) positive rows over String × Nat name/arity metadata.

Why it's unsound in Lean. owise is a Maude execution strategy — "try this only after every other equation fails to match" — not an equational axiom. maude2lean's def_extractor.py refuses to treat an owise group as a definition, warns, and then emits the equation as an ordinary eqe constructor. So Lean gets both numericArity("Add", 3) =E true and numericArity(N, A) =E false for all N, A, hence true =E false. (In the current output the three ops don't appear at all — the String kind collapsed first — so today they're lost, not unsound. Fix the literal bug and they become unsound.)

Best practice: don't encode "otherwise" as a fallback; encode it as membership in an explicit finite set, defined by structural recursion. Three ways, in order of preference:

Table-driven, one unconditional equation. Make the name/arity list data, not conditions:


sort ArityEntry ArityTable .
op _:_ : String Nat -> ArityEntry [ctor] .
op nil : -> ArityTable [ctor] .  op _;_ : ArityEntry ArityTable -> ArityTable [ctor] .
op numericTable : -> ArityTable .
eq numericTable = ("Convert" : 2) ; ("Abs" : 2) ; … ; ("Clamp" : 4) ; ("ScaledFMA" : 7) ; nil .
op inTable : String Nat ArityTable -> Bool .
eq inTable(N, A, nil) = false .
eq inTable(N, A, (M : K) ; T) = (N == M and A == K) or inTable(N, A, T) .
eq numericArity(N, A) = inTable(N, A, numericTable) .
No owise, no ceq, complete and confluent by construction (constructor recursion), and == on String/Nat is one of the two things maude2lean does special-case. It also removes the four hand-typed or-chains and gives tools/generate-wrappers.py one source of truth: inventory/operations.json already holds every name and arity, so the table should be generated from it, not typed.

Explicit complement. Keep the ceq … = true rows and write ceq numericArity(N, A) = false if not(cond₂) /\ not(cond₃) /\ …. Sound, but duplicates every condition, and conditional equations still block the translator's definition extraction.

Sort-based disjointness. The right tool for the ω-operations (that's how NaN/±Inf vs Rat rows are already kept exclusive), but names here are String, not a constructor sort, so it doesn't apply unless you first make operation names an enumeration sort — which is defensible on its own merits and would also sidestep the string-literal collapse.

The proofs/coverage.md note already restricts owise to "decidable String/Nat metadata"; option 1 removes the last three uses, so the restriction becomes "none" and the README warning can go. Say the word and I'll do it, generating the tables from operations.json.

>>

Two separate problems, two different fixes.

1. owise equations (unsound today)

Maude semantics: eq f(x) = r [owise] applies only when no other f equation matches. Translator currently emits it as an unconditional eqe constructor, so Lean can derive f(a) =E r even when a non-owise equation covers f(a). Fix in __init__.py _do_equations: emit the owise equation with an extra premise that no other LHS matches. Concretely, for each sibling equation eq f(p₁..pₙ) = r' of the same top symbol, add a hypothesis

lean
(∀ vars_of_pᵢ, ¬ (kF.eqa x (f p₁ .. pₙ)))    -- or literally x ≠ f p₁..pₙ for ctor patterns

Simplest sound version: reject sibling conditional equations (keep the warning there), and for unconditional siblings generate ¬ ∃ vars, args =A pattern premises. This is the "definitional extension" approach in the maude2lean paper. Implementation points:
- maudext.get_variables on the sibling LHS for the binder list.
- self.eqa for the disequality (matching modulo axioms, so ≠ on terms is wrong when args have assoc/comm).
- Drop the warning once implemented; keep it for owise with conditional siblings.
  Cost: one new premise builder, ~40 lines. Gives real semantics for owise instead of a warning.

Alternative cheap option: --with-derived-as-defs path already handles ordered matching correctly, because Lean match is ordered. I made complete reject owise earlier to be safe; it could instead accept owise when it is the last equation and it is variable-only. That covers the common "default case" shape as a Lean def with | _ => r last. Fits your spec only where the operator qualifies as a definition (linear ctor patterns, no conditions, no axioms).

2. 75 special operators without equations

These are Maude builtins on Nat/Int/Rat/String/Float (_+_, _*_, _<_, _quo_, gcd, substr, float ops...) marked special in the prelude; Maude implements them in C++. The translator sees no equations, so Lean gets opaque constructors with no axioms. Nothing can be proven about arithmetic.

Fix: extend the native-kind mechanism that already exists for Bool (special.py find_bool, _index_native) to Nat, Int, Rat, String:
- Map Maude kind [Nat] to Lean Nat, [Int] to Int, [Rat] to Rat (needs Mathlib, or use Int × Nat/a custom Rat in a data file), [String] to String.
- Map special symbols to Lean expressions via their id-hook names, e.g. ACU_NumberOpSymbol + → ({} + {}), NumberOpSymbol quo → ({} / {}), _<_ → decide ({} < {}), s_ → ({} + 1), sd → Nat.dist... a table of maybe 60 hooks in special.py.
- Sorts Zero, NzNat, NzInt, PosRat, NzRat become has_sort predicates over the native type (n ≠ 0, 0 < q...).
- Equality =E on those kinds becomes Lean =, as already done for Bool.
- Option name --with-native-arith yes, default off. Lean 4 core suffices for Nat/Int/String; Rat needs a data file or Mathlib.
  Cost: largest change of the two, maybe 300 lines plus tests. Remaining unmapped specials (e.g. random, float transcendental) stay opaque with a per-operator warning naming them.

3. Practical for your spec now

P3109-SPEC translated as one 23k-line file with all Maude prelude arithmetic inlined as opaque symbols. Even after fixing both items, proving things about the rational core in Lean means proving over native Rat; that is the realistic route (item 2 with Rat). Item 1 matters wherever your spec uses owise defaults (worth checking how many: grep -c owise lib/*.maude).

Recommend order: item 2 for Nat/Int/Rat first (unblocks arithmetic), then item 1.

