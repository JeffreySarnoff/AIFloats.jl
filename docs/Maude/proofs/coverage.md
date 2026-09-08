# Coverage arguments and proof boundaries

This record distinguishes finite execution evidence, mathematical arguments,
and mechanical checker conclusions. It is not a blanket conformance proof.
The exact tool conclusions and remaining obligations are in obligations.tsv.

## Representation and imports

RAT is protected as the unchanged rational carrier. Adding `Real`, `Number`,
and `Infinity` extends the surrounding kind, without introducing rational
constructors. The core's special-value equations only identify new operation
applications. Semantic module imports use `including` because general
preservation and completeness have not been proved. Format metadata uses the
builtin CONVERSION interface for decimal names; it consequently imports
builtin arithmetic and string machinery as well.

The shared sequence module protects NAT and implements ordinary structural
nil/cons traversal. Its XReal, integer-code, integer-random, format, and
observation views map only element sorts; no real implementation view is
asserted. Invalid public functions returning builtin sorts are kind-level
operators. The symbolic restricted constructors have guarded membership, not
unconditional finite-value declarations. Whole-import preservation, symbolic
confluence, and preregularity remain separate proof obligations.

## Codec and queries

Signed code space partitions into the NaN code, positive half including zero,
and negative nonzero half. Extended-domain infinity codes are removed before
finite decoding. Unsigned code space reserves the final code for NaN and,
when extended, the preceding code for positive infinity. Validity guards run
before decoding fields. Finite field extraction is quotient/remainder by
`2^(P-1)`, with distinct zero-exponent and positive-exponent equations.

Datum membership never calls encode or bound queries. It derives a positive
candidate code, rejects reserved/out-of-range candidates, and requires that
decoding the candidate equals the proposed rational magnitude. A nondyadic
rational or an overflow value cannot pass merely because its rounded or
floored candidate is in range. Negative unsigned values are rejected first.
This supports the inverse-code argument without a circular encoder domain.

The positive normal exponent is the maximum of floorLog2(magnitude) and
1−bias. The significand is an integer exactly when the datum is representable
at that grid. For valid datums, quotient/remainder reconstruct the decoder's
fields. Reserved infinity/NaN cases are separately inverted. A fully formal
arbitrary-width proof is pending; all fourteen four-bit tables and the two
required F8 formats plus Fs are exhaustively decoded and round-tripped.

## Rational helper termination

`pow2` selects a natural exponent or a reciprocal with natural exponent;
zero denominators are never constructed. `floorLog2` is called only on
positive rationals. Multiplication by two below one, or division by two at
or above two, strictly decreases the number of binary scaling steps to
[1,2). In round/encode callers, intermediate exponents are bound before use.

`integerSqrt(N)` starts with interval [0,N+1). `sqrtSearch` maintains
L² <= N < H² and halves the positive integer gap H−L until it is at most
one. The constructor sequence recursion decreases length. These are manual
termination arguments under caller invariants, not tool proofs of RAT.

## Rounding and ordered saturation

Rounding partitions zero, infinities, NaN, and nonzero rational inputs. The
nonzero branch chooses the clamped exponent before significand rounding.
The P=1 parity test uses zero-significand or parity of Q+bias, rather than
ordinary integer parity. Stochastic operands are explicit and range checked.
All nine rounding modes and all three saturation modes are covered by exact
rational boundary fixtures over all fourteen four-bit formats. Additional
fixtures enumerate N=0..3 and every random integer in each range on an exact
1/16 fractional grid, for P=1,2,4 and both signs.

For saturation, with L<=H and a valid mode, rational inputs partition into
below L, inside [L,H], and above H. NaN and both infinities are separate.
Finite saturation clips both rational overflow and infinities. Propagating
saturation separates finite overflow from representable infinities. SatNone
first distinguishes finite directed clipping; only its complementary guards
reach overflow selection. Thus finite clipping never consumes an infinity,
and the finite-domain NaN fallback never consumes an in-range value.
The 21 ordered source rows are mapped individually in traceability.tsv.

The pure-constructor slice uses these six locations, three saturation tags,
four direction classes, two signedness tags, and two domain tags. `other`
represents NearestTiesToEven, NearestTiesToAway, ToOdd, and all valid
stochastic choices: saturation treats those choices identically. `up`,
`down`, and `zero` represent the three directed modes. Outcomes `low`,
`high`, and `unchanged` interpret respectively as L, H, and the original
in-range value; exceptional outcomes have their direct meanings.

CRC proves local confluence and sort decrease of that slice. SCC reports
completeness and soundness, but does not prove ground weak termination or
ground sort decrease. A manual acyclic call ordering
`decision > highNone/lowNone > highOverflow/lowOverflow` establishes slice
termination. The slice's relation to production comparisons, guards, and
builtin arithmetic is a **separate pending refinement obligation**. Neither
a constructor abstraction nor a successful SCC run proves RAT semantics.

## Scalar and ordering evidence

NaN handling, real operands, and infinity operands use distinct sorts or
explicit complementary guards. Unknown symbolic tests are never treated as
false by an `owise` arithmetic equation. The only conformance `owise`
equations are over decidable String/Nat name-and-arity metadata.

FMA is `omegaAdd(omegaMultiply(X,Y),Z)` and FAA is
`omegaAdd(omegaAdd(X,Y),Z)`, as the draft itself states. There is no projection
between these kernels. The test oracle independently transcribes the original
NaN/infinity rows and uses rational polynomials in the final finite case.
All 16³ operand tuples of Binary4p2se are checked for each fused operation,
including all seventeen initial FMA NaN rows. Core scalar wrappers, all ten
extrema, Clamp, comparisons, and predicates have independent bounded checks.

TotalOrder gives NaN the first position, including NaN<=NaN, and then uses
extended-real order. Next handles NaN and exhausted endpoints first, then
steps the sign/magnitude encoding; negative minimum magnitude crosses to
zero without stepping through the NaN code. The independent test oracle
decodes and sorts F4 and both F8 formats. It checks immediate adjacency, not
only inverse-next identities. All 528² TotalOrder pairs and both neighbors
for all 528 codes passed. Arbitrary valid widths still require a general
proof.

## Blocks

Block guards require positive B, exact lengths, valid codes, and valid
per-element random sequences. Decoding multiplies scale and element before
any output projection. Normalization checks scale/element NaN before zero
scale; infinite scale uses the product of signs, including zero's sign 0.
The supplied scale is returned unchanged by elementwise wrappers.

Seeded folds are first-order structural recursions, with seeds 0, 1, and NaN
for Add, Multiply, and MaximumFinite respectively. They preserve operand
order and do not project intermediate values. Dot product forms exact
pairwise products before the seeded sum. Scale computation decodes inputs,
takes magnitudes, folds MaximumFinite, projects the scale once, decodes that
projected scale, and normalizes each element against it.

Tests cover special scales, malformed shapes, stochastic indexing,
unit-scale equivalences for every generated family, zero-rounded scales,
and the source NOTE dispositions in deviations.md. They do not enumerate
arbitrarily long blocks or assert a universal block correctness proof.

## Symbolic interpretation

Expression meaning is the corresponding ordinary mathematical real operation.
Rational reductions and selected identities, integer powers of two, exact
rational square roots, and integer/half-integer pi multiples are executable.
General domain guards must establish their comparison; otherwise applications
remain residual. Pi-multiple order uses the positive sign of pi, without a
floating approximation. Nonzero rational arguments to cos cannot be zeros
of cos; that mathematical fact supports the rational Tan domain case.

The 17 ArcTan2 rows are checked separately in radians and pi units. Syntactic
identity of a well-sorted real expression can establish equality with itself;
different normal forms never establish mathematical inequality. The underlying
raw expression theory is not a quotient construction satisfying every real
field identity. A view from the mathematical-real contract is therefore not
provided. A future certificate evaluator would require its own weaker,
partial-evaluation contract and soundness proof.

## Conformance evidence and throughput

An independent Cartesian-product fixture enumerates all §4.5 identities for
all seven valid external subsets, plus negative parameter cases. This checks
required-set membership; it does not supply implementations for external
specializations. Declaration records validate scalar, scaled, and block identities,
including block sizes and both projection specifications where applicable.
They do not validate the truth of attached evidence claims. Symbolic
partition descriptions and complete operand coverage remain pending.

For an internal signed format with M the positive maximum-finite code and H
the sign bit, finite rank is M+C on the nonnegative half and H+M−C on the
negative half. For unsigned formats it is C. The ranks form consecutive
integers in numerical order. Absolute rank difference therefore counts the
specified half-open interval. NaN mismatch is checked before infinity
mismatch. Tests compare ranks against an independent sorted finite list.

`partition` and `partition2` are exhaustive finite set checks on their supplied
universe only. `partitioned` stores per-subset bounds; `declarationKappa`
combines declared bounds, independently of empirical observation evaluation.
`batchKappa` is a maximum over explicit observations, and mergeKappa implements
the same NaN/infinity/finite precedence for multi-result aggregation. No
candidate callback, coverage proof, or external execution is hidden there.
Annex D.1's subnormal count and Annex D.2's illustrative bound/subset size are
separate fixtures; no D.2 approximate candidate was evaluated.

The runner chunks large products into fresh processes, validates each case ID
and a completion sentinel, and reports expected/executed counts. It never
suppresses advisories. Proof processes are separately screened and isolated.
See sessions/validation.json for the final recorded run counts and profiles.

## Final phase evidence

| Plan phase | Delivered evidence | Remaining qualification |
| --- | --- | --- |
| A — interfaces | Source/tool hashes, shared sorts and container views, independent loaders, CRC/SCC smoke | No real or external implementation view |
| B — numeric slice | All 224 four-bit table entries; required eight-bit codecs; invalid domains; 11,016 projection checks | Arbitrary-width formal codec/projection proofs pending |
| C — rational scalars | 33,760 scalar checks; original FMA/FAA oracle; complete F4/F8 order and adjacency | Universal arithmetic/refinement proof obligations remain separate |
| D — rational blocks | 140 block checks; all generated core family unit-scale checks; stochastic indexing and NOTE dispositions | Arbitrary-length proof pending |
| E — symbolic layer | 194 symbolic checks, including all generated family special cases and explicit residuals | General real decisions and certified enclosure evaluation pending |
| F — conformance accounting | 5,731 checks of required products, scalar/scaled/block declarations, partitions, ranks and κ | External implementations and truth of adapter evidence remain pending |
| G — evidence and use | README, runnable examples, 89-operation inventory, labelled equations, source traces, exact proof sessions | Full note/recommendation-level trace expansion and excluded asspec criteria are not claimed |

The final Core Maude run passed 55,476 core checks. The same core checks pass
under the symbolic loader and on Maude++. Both engines pass the 194 symbolic
checks and all three independent loaders. The separate exhaustive ordering
run passed 279,840 checks: 278,784 ordered pairs and 1,056 adjacency checks.
These counts overlap the focused core ordering suite; they are not summed as
a count of distinct mathematical facts. Recorded semantic hashes identify
the exact files used for this validation.
