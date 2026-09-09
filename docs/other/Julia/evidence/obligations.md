# Evidence and remaining obligations

`source-obligations.tsv` is an unchanged copy of the source proof register.
`obligations.tsv` maps every original ID to Julia evidence and its remaining
scope. `inventory/files.tsv` accounts for every proof session, Lean source,
source document and generated Lean artifact. These materials remain in the
hashed sibling source tree; they are not recast as executable Julia proofs.

Historical CRC/SCC results concern the constructor smoke and saturation slices.
Their confluence, sort-decrease and completeness conclusions retain the stated
assumptions. They do not prove the production codec, rational operators or
symbolic implementation. Structural termination arguments remain arguments;
the conversion does not introduce a theorem prover or claim mechanized proof.

The source Lean material separates native axioms, syntax, relations, embeddings
and lemma candidates. A complete successful Lean build was not established by
this conversion. Native RAT/INT/BOOL behavior maps to exact BigInt rationals,
explicit tagged exceptional values, Bool and UNKNOWN; that mapping is tested
on the finite corpus, not universally proved.

Open obligations remain: codec bijection at arbitrary widths, ordered saturation
refinement, general next-value adjacency, FMA/FAA universal equivalence, symbolic
real interpretation, backend laws, complete-domain κ coverage, and certified
irrational projection. Required-identity enumeration is finite data evidence;
it does not certify an external implementation. No unsupported external or
real implementation view has been silently supplied.

Julia 1.13.0-rc4 test evidence is recorded separately from the stable-release
rerun obligation. Historical source-plan hash drift is retained as
`BASELINE-PLAN-HASH`. The user-authorized stale-assertion removal is documented
in `deviations.md` and the current source snapshot.
