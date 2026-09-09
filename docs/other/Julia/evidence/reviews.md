# Correctness, completeness and Julia idiom review

Reviewed against the permitted Maude sources, the two original conversion plans,
`improvedconversion.md`, and the pinned local `IdiomaticJulia.md` guide.

| Finding | Correction or decision | Evidence |
| --- | --- | --- |
| Format widths and rational numerators can exceed machine integers. | Store numeric parameters and exact payloads as BigInt; codec/rank formulas avoid enumeration. | Wide-format round trips and bit-length boundary checks; source codec suite. |
| Decode has an intentional finite/special return union. | Permit that union in the inference assertion; do not mistake it for accidental instability. | Inference checks and complete package test. |
| Two external next-value domain cases initially lacked explicit rejection. | Reject unsupported external next/rank paths at the boundary. | Domain cases 40/40; independent external-boundary checks. |
| Missing external classification could become false. | Propagate explicit missing-backend residuals. | Independent NaN/finite/normal/subnormal/classification checks. |
| Distinct syntax and invalid symbolic domains could imply unsupported mathematical facts. | Keep structural equality separate, protect real membership, and propagate residual arithmetic. | Symbolic cases 194/194 and independent negative/unknown tests. |
| Borrowed stochastic sequences can change after construction. | Validate lengths/ranges again at block entry; document borrowing and positional traversal. | Mutated random input regression; views/tuples and nonmutation tests. |
| Stochastic projection repeatedly traversed its random sequence. | Zip values and policies once; retain the explicit single-position query separately. | Full block/source suites rerun; source order preserved. |
| Unresolved infinite-scale operands could lose their residual boundary. | Return a normalization residual; reject next-value calls consistently for bound external formats. | Two independent regressions and domain rerun. |
| Repeated source templates would obscure shared behavior. | Generate 156 thin adapters plus kernel/arity tables; handwritten kernels share scalar/block logic. | Deterministic generator and 193-name inventory audit; independent source arity fixture. |
| External bridge declarations need usable dispatch boundaries. | Add explicit BoundFormat binding and predicate guards; supply no concrete production backend. | Eight bridge-dispatch tests with a clearly limited test double. |
| Four legacy standalone assertions were stale. | User directed removal from source and supporting copies; omit them from Julia. | Five unaffected standalone cases retained; cleanup and capture checks. |
| Test counts or proof tags could overstate conformance. | Record per-suite counts/hashes and maintain claim-level open obligations. | Source register copied unchanged; detailed case report and obligations table. |

The design uses ordinary generic functions, owned value types, explicit imports,
runtime format values, positional iteration and one final projection. It avoids
type piracy, generated semantic bodies, macro-heavy runtime dispatch, hidden RNG,
global mutable numeric context and premature caches. Package ambiguity checks
pass. JSON/compression/formatting/benchmark packages are isolated from runtime.

Remaining performance costs are principally exact BigInt/rational allocation.
The benchmark script records first-call timing and warmed allocations/latency;
its results are workload-specific, not machine-independent performance promises.
No remaining review finding requires substituting approximate arithmetic.

Completion evidence and remaining release/backend/proof limitations are in
`checkpoint.md`, `runs/` and `obligations.tsv`. This review is engineering review,
not a formal proof of semantic equivalence for all possible inputs.
