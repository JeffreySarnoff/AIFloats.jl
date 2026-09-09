# API and implementation boundaries

## Interfaces

Use `SpecAPI` for the source's exact operation names and argument order.
[operations.tsv](inventory/operations.tsv) is the complete signature index.
Arguments describing formats and projection precede code operands. `ArcTan2`
receives y before x. Scaled operands are flattened scale/code pairs; block
operands are flattened scale/sequence pairs, matching the source.

Use `BinaryFormat`, `finite`, `decode`, `encode`, `Projection` and `project` for
direct numeric work. `scalar(kernel, formats, result_format, policy, codes)`
decodes inputs, calls a Julia function and projects once. The shared `scaled`
and `block_apply` functions apply the same kernel with source normalization.
FMA, FAA, reductions and dot products retain exact intermediate values and
perform one final projection. There is no intermediate machine float conversion.

`BlockValue` holds the returned scale code and element codes. Inputs may be
tuples or ordered vectors, including views. Traversals align by position and
return fresh output vectors. They do not mutate input arrays. Policy objects
borrow their random sequences; do not mutate them during an operation. Their
range and length are revalidated at block entry. Multidimensional broadcasting,
arbitrary lazy iterators and preserved offset axes are not promised.

## Mathematical and structural decisions

`==`/`isequal` on owned finite, policy and syntax values compare representation.
`mathematical_equal` and `mathematical_less` follow source mathematical knowledge:
NaN is not mathematically equal to itself, and distinct expression trees need
not denote distinct real numbers. `UNKNOWN` is a `Decision` value, never a Bool.
Callers must compare outcomes explicitly; they must not coerce unknown to false.

`Symbolic.expression` builds source expression syntax;
`Symbolic.elementary` performs the supported domain-sensitive reductions.
`Symbolic.real_domain` reports true, false or unknown membership.
For example, an exact rational square has an exact square root, while sqrt(2)
remains symbolic. An out-of-domain expression is not promoted to a valid real.
A `Residual` stores `operation`, `arguments`, and `reason`, such as
`:missing_backend` or `:uncertified_projection`. No approximate evaluation is
used to decide a projection boundary.

## External contracts

`BINARY16`, `BINARY32`, `BINARY64` and `BFLOAT16` are metadata declarations.
They do not install concrete external codecs. `Contracts.ExternalBackend` and
`Contracts.RealBackend` expose named extension functions corresponding to the
source theories. Default methods return missing-backend residuals.

`BoundFormat(metadata, backend)` explicitly associates external metadata with
an `ExternalBackend`; the backend must report matching metadata. Decoding and
encoding check the backend's code/datum predicates before dispatch. Concrete
backends must establish canonicalization, quiet-NaN, positive-zero, finite-count,
bound and interpretation laws listed in the source contract. The small bridge
test double establishes dispatch behavior only and is not a usable codec.
RealBackend declares the interpretation interface; it is not an automatic
certified symbolic evaluator. Internal next-value/rank algorithms do not extend
themselves to arbitrary external encodings.

Conformance records and algorithms in `conformance.jl` check supplied finite
data: specialization identities, required sets, declarations, partitions and
κ accounting. A proof-evidence tag is an assertion by the supplying adapter,
not a verified proof. Neither sampled maxima nor successful required-set checks
establish whole-domain implementation conformance.

## Organization and performance

| Files | Responsibility |
| --- | --- |
| `values.jl`, `formats.jl`, `policies.jl` | Exact carrier and validated configuration |
| `codec.jl`, `projection.jl` | Arithmetic code mapping and ordered rounding/saturation |
| `arithmetic.jl`, `symbolic.jl` | Shared exact kernels and guarded symbolic reductions |
| `operations.jl` | Scalar, scaled and block traversals; predicates, ordering and reductions |
| `conformance.jl`, `contracts.jl` | Finite conformance algorithms and explicit backend seams |
| `spec_api.jl`, generated files | Source-facing names and inventory-derived adapters/tables |

Widths are values, not type parameters; the implementation avoids compiling a
distinct method family per width. Arithmetic codecs and integer bit-length
logarithms avoid format enumeration. Large exact rationals allocate; allocation
freedom is not a goal of this reference. Tests check inference at representative
concrete boundaries while permitting the intentional finite/special result union.
BenchmarkTools measurements separate the first call from warmed medians.
Machine integers, caches, mutation and threading require a measured benefit and
new semantic checks before adoption.
