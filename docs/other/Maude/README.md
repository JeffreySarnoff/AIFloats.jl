# P3109/D1 in Core Maude

Executable rational arithmetic, symbolic expressions, and mathematical contracts
for the September 2026 IEEE P3109/D1 draft. The draft is unapproved; passing
tests does not establish full implementation conformance. See
[proof obligations](proofs/obligations.tsv) for the remaining work.

## Quick start

With Python 3 and Core Maude installed, run from the repository root:

```sh
cd docs/other/Maude
maude -no-banner -no-ansi-color load-core.maude
```

At the Maude prompt:

```maude
red in P3109-CORE : Convert(
  Binary(8, 4, Signed, Extended), Binary(4, 2, Signed, Finite),
  proj(NearestTiesToEven, SatNone), 72) .
```

This returns code `6`, representing 2 in `Binary4p2sf`. The input code `72`
represents 2 in `Binary8p4se`. Batch examples are in
[examples/core.maude](examples/core.maude) and
[examples/symbolic.maude](examples/symbolic.maude):

```sh
maude -no-banner -no-ansi-color examples/core.maude
maude -no-banner -no-ansi-color examples/symbolic.maude
```

Choose a loader in a fresh process:

| Loader | Entry point | Contents |
| --- | --- | --- |
| `load-core.maude` | `P3109-CORE` | Codecs, rational projection, arithmetic, predicates, ordering, blocks, conformance helpers |
| `load-symbolic.maude` | `P3109-SYMBOLIC` | Core plus elementary expressions and scalar/block/scaled wrappers |
| `load-contracts.maude` | Contract theories and a parameterized bridge | Core plus real-number and external-codec obligations; no backend view |
| `load-spec.maude` | `P3109-SPEC` | All loaders and the separate `P3109-FORMAT-NAMES` presentation module |

`P3109-SPEC` imports the symbolic profile, which includes core. Contracts are
loaded into Maude's module database; using them requires an implementation
view. `formatName` is available in `P3109-FORMAT-NAMES`.

## Values and operations

Formats use `Binary(K, P, Signedness, Domain)`, with `Signed` or `Unsigned`
and `Finite` or `Extended`. Valid formats require `K > 2`, `P > 0`, and
`P < K` when signed or `P <= K` when unsigned. The external formats
`binary64`, `binary32`, `binary16`, and `BFloat16` have metadata, but their
codecs and code-valued bounds remain external interfaces.

Public numeric calls take **parameters first, then integer code operands**.
The complete argument order is in [operations.json](inventory/operations.json).
For example, `Add(fx, fy, fr, rho, x, y)` and
`FMA(fx, fy, fz, fr, rho, x, y, z)` each perform one final projection.
`ArcTan2(fy, fx, fr, rho, y, x)` uses y-before-x order.

The `omega...` kernels take decoded values: `fin(R)` for a rational `R`,
`nan`, `posInf`, or `negInf`. There is one zero and one NaN datum.
`Real < Number < XReal` and `Infinity < Number`; rationals are embedded with
`fin`, keeping builtin arithmetic separate from the `XReal` kind. Write
`fin(2)` wherever an `XReal` is expected; a bare `2` will not parse there.
`ratOf(fin(R))` extracts the rational.

A scalar projection is `proj(mode, saturation)`:

- Deterministic modes: `NearestTiesToEven`, `NearestTiesToAway`,
  `TowardPositive`, `TowardNegative`, `TowardZero`, and `ToOdd`.
- Stochastic modes: `StochasticA(N, R)`, `StochasticB(N, R)`, and
  `StochasticC(N, R)`, with `N >= 0` and `0 <= R < 2^N`.
- Saturation: `SatNone`, `SatFinite`, or `SatPropagate`.

Random integers are explicit inputs; no randomness is generated internally.
`validFormat`, `validCode`, `datum`, and `validProjection` check domains.
Invalid public applications remain unreduced, distinct from specified NaN
results. Imported helpers require their caller invariants.

## Blocks

Sequences use `ccons(code, tail)`/`cnil`, `xcons(value, tail)`/`xnil`, and
`rcons(random, tail)`/`rnil`. Indexing is zero-based. Lengths must match the
explicit positive block size; `validBlock` and `validBlockProjection` check
these requirements.

A block is `block(scaleCode, codeSequence)`. Public calls flatten each input
block into its scale and sequence arguments. Projection uses `bproj(mode, sat)`;
stochastic block modes are `BlockStochasticA(N, randomSequence)` and analogous
B/C forms. `singletonLift` adapts scalar projection for scaled calls.

Elementwise operations preserve the supplied result scale.
`BlockReduceAdd`, `BlockReduceMultiply`, and `BlockDotProduct` return scalar
codes. `ConvertToBlockMaxAbsFinite` computes and returns its result scale.
See [block-ops.maude](lib/block-ops.maude) and the
[block fixtures](tests/vectors/blocks.json) for calls.

## Symbolic expressions and contracts

The symbolic profile reduces `omegaSqrt(fin(9/16))` to `fin(3/4)` and
`omegaSqrt(fin(2))` to `exprSqrt(fin(2))`. Uncertified projection of the latter
remains residual. Domain-restricted expressions such as `exprLog(fin(-1))`
do not acquire sort `Real`.

Use `xEq`, `xLt`, and `xLe` for mathematical comparisons. Maude's syntactic
`==` checks representations and metadata; different symbolic forms do not
establish mathematical inequality.

The real contract states field/order obligations, not an executable
construction of all reals. The external-format bridge has no concrete view.
Both need backend implementations and evidence that their views preserve the
contracts. A future evaluator using certified enclosures could resolve selected
expressions while leaving undecidable cases residual; this would require a
separate partial-evaluation contract. See
[possible_enhancements.md](possible_enhancements.md).

## Conformance helpers

`numeric(name, formats, projection)` and `plain(name, formats)` identify scalar
specializations. `required(identity, externalFormats)` checks the draft's
parameter restrictions, including scaled operations. Tests enumerate all seven
nonempty subsets of the three required external formats: 341, 443, or 549
required identities for subset sizes 1, 2, or 3.

`exact`, `approximate`, and `partitioned` are declaration records.
`wellFormedDeclaration` checks their schemas; `hasDeclaration` and
`declarationsCover` check presence in a supplied set. `blockElements`,
`blockReduction`, and `blockScale` identify block schemas. Callers must supply
the complete required set to claim coverage.

`observationKappa` and `batchKappa` compute rank distances from explicit
observations, with NaN mismatch preceding infinity mismatch. `mergeKappa`
combines results. `partition` checks disjoint subsets of a supplied finite
universe; `partition2` handles two subsets. `declarationKappa` combines declared
partition bounds. Adapter evidence tags are claims, not checked certificates;
a sampled maximum does not establish whole-domain κ.

## Validation

From this directory:

```sh
python3 tools/run-tests.py --suite core
python3 tools/run-tests.py --suite symbolic
python3 tools/check-loads.py
python3 tools/check-inventory.py
python3 tools/generate-wrappers.py --check
python3 -B -m unittest discover -s tests -p 'test_*.py'
```

The core suite includes smoke, domains, codec, projection, scalar, order-next,
blocks, and conformance. Each can also run individually. Additional coverage:

```sh
python3 tools/run-tests.py --suite order-full
python3 tools/run-tests.py --suite core --profile symbolic
python3 tools/run-tests.py --suite core --engine maude++
python3 tools/run-proofs.py --suite eligible
```

Runners locate this directory automatically. Tests reject diagnostics,
unreduced or missing assertions, missing completion sentinels, timeouts, and
failed processes. Shared unary, binary, and ternary schemas live in
[scalar-templates.maude](lib/scalar-templates.maude) and
[block-templates.maude](lib/block-templates.maude). Wrapper generation emits
kernel views and named instances of those schemas, preserving public signatures,
map helpers, and operation-specific equation labels. Edit the templates for
shared behavior, the inventory for operation membership, and the generator for
instance naming. Template metadata cites the shared schema; operation-specific
clauses remain in the operation inventory and traceability table. Arithmetic
kernels remain handwritten.

Proof runs use Maude++ and MFE via `MAUDE_PROOF_ENGINE`/`MFE_PATH` or
`--engine`/`--mfe`. They screen constructor-only targets, require accepted CRC
conclusions before SCC, and save logs under the system temporary directory.
Production RAT modules and the saturation slice's refinement remain outside
those checker conclusions. Tool setup is recorded in [installation.md](installation.md).

## Reference files

- [planmaude.md](planmaude.md): original implementation plan, with historical paths.
- [inventory/traceability.tsv](inventory/traceability.tsv): equation labels, clauses, and pages.
- [inventory/source.json](inventory/source.json): recorded source and tool hashes.
  Its plan hash predates the current `planmaude.md`; the inventory check reports
  that mismatch until provenance is reconciled.
- [proofs/coverage.md](proofs/coverage.md), [deviations.md](proofs/deviations.md),
  and [obligations.tsv](proofs/obligations.tsv): evidence, interpretations, and open work.
- [maude2lean.md](maude2lean.md): translation workflow and limitations.
- [Lean/README.md](Lean/README.md): organized translation of `spec2.lean`;
  foundational compilation passed, full compilation remains unverified.
