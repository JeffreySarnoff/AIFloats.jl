# Recorded decisions and source changes

| ID | Decision and scope |
| --- | --- |
| BASELINE-PLAN-HASH | Before conversion, source inventory checking reported `Source hash changed: planmaude.md`. Current source bytes are pinned independently. The historical manifest remains unchanged. |
| SOURCE-CLEANUP | At the user's request, four stale standalone assertions were removed from `tests/{codec,projection,blocks,symbolic}.maude` in both Maude trees. Their files remain load-only scripts with `suiteComplete(0)`. Corresponding YAML/JSON source records, counts, references and hashes are refreshed. No adapted versions enter Julia fixtures. |
| DOMAIN-BOUNDARY | Julia public constructors and operations reject invalid arguments; the test adapter retains invalid raw source terms for membership tests. Valid undecidable terms remain residual/unknown. |
| FIXTURE-TRANSPORT | Frozen compressed JSONL stores exact source assertions and their original IDs; no floating-point JSON numbers approximate rationals. Per-suite index plus JSONL records replaces a redundant full-size cases TSV. |
| PACKAGE-CHOICE | Base exact arithmetic supplies the runtime. JSON, CodecZlib, JuliaFormatter and BenchmarkTools reduce tool code. General symbolic algebra would require semantic adapters that outweigh its benefit here. |
| RELEASE-EVIDENCE | Validation uses the available Julia 1.13.0-rc4. Stable 1.13 must be tested before claiming stable-release validation. |
| PROOF-SCOPE | Source proof and Lean materials are retained with their original scope; finite Julia test success does not discharge universal claims. |

The source-cleanup exception extends the original output-only scope by explicit
user instruction. Other existing repository changes are preserved. The existing
repository Julia implementation and related documentation were not used.
