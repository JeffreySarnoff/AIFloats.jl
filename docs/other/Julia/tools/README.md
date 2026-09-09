# Conversion tools

Run commands from `docs/other/Julia/` using Julia 1.13 and the pinned workspace.

| Command | Purpose |
| --- | --- |
| `julia --project=tools tools/audit.jl` | Verify current source hashes, all file/rule targets and 193 public API names |
| `julia --project=tools tools/generate.jl --check` | Compare generated adapters/tables without writing |
| `julia --project=tools tools/generate.jl` | Explicitly regenerate three files from copied operations inventory |
| `julia --project=tools tools/run-cases.jl` | Check every frozen source assertion, count, unique ID and hash |
| `julia --project=tools tools/run-cases.jl symbolic domains` | Run named affected suites |
| `julia --project=tools tools/run-cases.jl --report evidence/runs/julia-cases.json` | Write runtime, input/implementation hashes and suite results |
| `python3 -B tools/capture-source.py --check` | Optional migration check against sibling Python source oracles; no writes |
| `python3 -B tools/capture-source.py` | Explicitly recapture the corpus, preserving IDs and exact source assertions |

Normal package tests do not invoke Python or Maude. The Python capture adapter
is retained only because the independent oracle is implemented in Python. Its
expectations must not be regenerated from Julia results. CodecZlib compresses
the checked-in JSONL files; hashes cover uncompressed bytes. Suite-local IDs
plus suite names are the case keys. The suite index in `inventory/cases.tsv`
points to the complete per-case records, avoiding a second 347,580-row copy.

The bounded source-expression parser accepts an allowlist of constructors,
operators and specification calls. It consumes all tokens and never uses `eval`
or executes source text. Raw invalid constructors exist only in this test adapter
so source membership/validity tests can be compared with validated Julia APIs.
False, unknown, unsupported syntax and exceptions fail ordinary assertions.
Known invalid calls are represented distinctly, preserving source domain tests.

Source tool responsibilities map as follows: `generate-wrappers.py` to
`generate.jl`; inventory checks to `audit.jl`; source fixtures/reference/regressions
to the frozen corpus and `run-cases.jl`; loader checks to package import, examples
and ambiguity checks; source proof commands to retained evidence and explicit
obligations. A Julia execution test does not replace Maude CRC/SCC or Lean.

For fresh source comparison, run the sibling `tools/check-loads.py`,
`tools/run-tests.py --suite core`, `--suite symbolic`, and `--suite order-full`.
Source and Julia must independently accept the same captured assertions. Current
source `check-inventory.py` has the recorded historical plan-hash discrepancy;
do not silently bless a changed plan by rewriting that historical hash.

Dependencies simplify tooling: [JSON.jl](https://github.com/JuliaIO/JSON.jl)
handles structured data, [CodecZlib.jl](https://github.com/JuliaIO/CodecZlib.jl)
handles compressed fixtures, [JuliaFormatter.jl](https://github.com/JuliaEditorSupport/JuliaFormatter.jl)
formats generated adapters, and [BenchmarkTools.jl](https://juliaci.github.io/BenchmarkTools.jl/stable/manual/)
measures warmed workloads. Runtime code needs no third-party dependency.
