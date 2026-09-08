# Source findings, implementation choices, and open work

## Authorized source substitution

The request permitted only `planmaude.md` and, when needed,
`IEEE_D1_2026_09_07.pdf` as repository reference documents. The plan refers to
`asspec.md`, but that document was excluded and was not read. Its hash and
acceptance criteria cannot be claimed as verified. The permitted PDF supplies
the arithmetic semantics directly; source.json records this substitution.
Existing unrelated files under docs/Maude were not used as references or edited.

## Confirmed source findings

- K=2 is excluded by normative §3.1. Annex C's illustrative encodings do not
  override that restriction. Invalid-format tests preserve the exclusion.
- §5.4.2 NOTE 2 is consistent with the specified normalization: an infinite
  scale maps nonzero, non-NaN elements to signed unit values. The positive and
  negative sign cases, including infinite input elements, pass.
- §5.5.3 NOTE 2 conflicts with normative projection when the scale is clipped
  to a finite value but the element projection preserves infinity. With
  Binary8p4se input/scale/result, input +Inf, scale SatFinite, and element
  SatNone, the computed scale is code 126 (224) and the element is code 127
  (+Inf). The note's proposed ±1/±MaxFinite alternatives do not cover this.
  The specification follows the normative formulas and retains the regression.
- §4.16's explicit signed-NaN successor rows are shadowed by the preceding
  IsNaN row. The implementation follows first-match semantics: NaN remains
  NaN. It does not interpret the unreachable rows as negative-zero behavior.

## Implementation choices

- One additional generated `block-wrappers.maude` file per execution profile
  separates repetitive schemas from handwritten block algorithms.
- `Number` and `Infinity` are auxiliary sorts below XReal. They simplify
  disjoint exceptional cases while retaining Rat<Real<XReal.
- Public names and source operand order are preserved. Block tuple arguments
  are flattened; helper indexing is zero-based and documented.
- Rational membership uses an independently guarded positive candidate and
  decoder equality, not an encoder call or a bound-query cycle.
- FMA, FAA, subtraction, reciprocal, selected pi variants, and Softplus use
  compositions of exact omega kernels. No intermediate projected wrapper is
  called. Original FMA/FAA rows have independent test oracles.
- No user startup files, global installations, Julia source, or Julia tests
  are changed. The specification has its own Maude test harness.
- Proof targets are always rerun rather than served from a cache. Their hashes,
  component identities, exact conclusions, and inputs are recorded; no stale
  cached result can certify a changed module.

## Pending contracts and acceptance evidence

The rational core and listed symbolic special cases execute. The following
are intentionally not presented as completed capabilities or proofs:

1. External finite codecs, code-valued external bounds, and external finite
   counts require an authorized semantic source and a concrete backend view.
   Thus the required external operation declarations are not implementations.
2. The complete mathematical reals and a proof that expression interpretation
   satisfies their full laws are not constructed. General comparisons,
   domains, and projections can remain unresolved. The real theory contains
   necessary axioms and explicit additional obligations, not a complete
   executable axiomatization of the real continuum.
3. The optional certified-enclosure evaluator is omitted. Equal projection
   of both endpoints is insufficient, as the [-100,100]/NaN regression shows.
4. Production RAT modules have not been proved confluent, terminating,
   preregular, and sufficiently complete by CRC/SCC. Builtin arithmetic is
   outside the supported constructor proof profile. The smoke target and
   saturation slice have mechanical results; production refinement and other
   general proof obligations remain explicitly pending.
5. Scalar, scaled, and block declarations and arbitrary finite partitions
   are represented and checked structurally. Symbolic subset descriptions
   and universal coverage proofs remain adapter work. A partition check
   proves coverage only of its explicitly supplied finite universe; declared
   bounds and evidence tags are not automatically verified implementation
   proofs. κ aggregation handles supplied observations and multiple results.
6. Row-level traces are supplied for saturation, FMA, FAA, and ArcTan2; other
   families have operation/formula-level traces. A line-by-line accounting of
   every PDF NOTE and recommendation, and any additional asspec acceptance
   criteria, remains pending. No undocumented asspec criteria are invented.
7. Test scopes are finite and recorded. The all-width codec and order proofs,
   all-length block proof, general symbolic interpretation proof, and complete
   candidate conformance evidence remain open. Annex D.2 is a declaration
   fixture, not an experiment over 442,050,625 candidate inputs.

These boundaries are part of the delivered evidence, not successful proof
results inferred from a loader or a declarations file.
