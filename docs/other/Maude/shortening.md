# Maude source shortening

The refactor replaces repeated wrapper equations with shared unary, binary,
and ternary modules. All changes and reference documents are confined to this
directory; the permitted IEEE PDF was hashed by the inventory check.

| Maude source group | Before lines | After lines |
| --- | ---: | ---: |
| Generated scalar wrappers, core and symbolic | 332 | 323 |
| Generated block/scaled wrappers, core and symbolic | 1,263 | 321 |
| Shared scalar and block templates | 0 | 161 |
| Four loaders | 67 | 69 |
| Other Maude files | 2,008 | 2,008 |
| **Total** | **3,670** | **2,882** |

Total Maude source shrank by **788 lines (21.5%)** and **44,954 bytes (19.8%)**,
including the two new template files and loader additions. There are now 49
Maude files, up from 47: the reduction is in repeated definitions, not file count.

The 52 operation families now instantiate 15 shared equations instead of
spelling out 260 equations. The generator emits kernel views, operation
renamings, and equation-label renamings. Public signatures, argument order,
map helpers, validation guards, singleton scaled behavior, and existing trace
labels are preserved. Shared metadata cites the wrapper schema; individual
operation clauses remain in `inventory/operations.json` and `inventory/traceability.tsv`.
The inventory checker recognizes and validates the renamed exports and labels.

Other groups were retained after inspection. Conformance already generates its
three arity tables from the inventory; its remaining declaration, partition,
and required-specialization rules serve distinct purposes. Codecs, projection,
arithmetic, and elementary expressions contain distinct domain and exceptional
cases. Contracts, proof slices, loaders, and examples preserve useful boundaries.
The existing generic sequence module already removes collection boilerplate.
Lean translation files and build artifacts were not changed.

Validation performed after the refactor:

- Core suite: 67,541 checks passed.
- Core suite under the symbolic profile: 67,541 checks passed.
- Symbolic suite: 194 checks passed.
- All four loaders and both examples passed on Maude and Maude++.
- Nine Python tooling tests passed, including a new test for renamed exports
  and invalid rename sources. Deterministic wrapper/table generation passed.
- Compared Maude's `show all P3109-SPEC` output against a snapshot taken before
  editing: all 1,703 declarations/statements match after ignoring formatting
  and metadata. The 1,019 equations/memberships also retain their exact order.

The inventory command reports the same pre-existing `planmaude.md` provenance
hash mismatch as before the change, with no additional errors. That historical
hash was left intact. This refactor shortens source; instantiation still expands
the same definitions, so it does not establish a smaller Lean translation or
additional mathematical proof results.
