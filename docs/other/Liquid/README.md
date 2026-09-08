# Liquid sources for Maude

Each `*.maude.liquid` entry point generates the matching file under
`../Maude/`. Render with an empty context and this directory as the Liquid
loader root; shared partial names use the `.liquid` extension automatically.

```sh
python3 -m pip install -r docs/other/Liquid/requirements.txt
python3 docs/other/Liquid/render.py --check
python3 docs/other/Liquid/render.py --output-dir /tmp/generated-maude
```

The default checks all 32 entry points byte-for-byte and requires a template
for every Maude file in `lib/`, `symbolic/`, and `contracts/`, plus
`proofs/slices/saturation-cases.maude`. `--output-dir` writes the
matching directory tree. Generation uses only templates; check mode reads
Maude source as the comparison reference.

Shared content is grouped by purpose across source directories:

- `shared/operations.liquid` holds ordered core/symbolic operation data, including
  primitive expression labels and domain guards. `wrappers.liquid` uses it for
  both wrapper profiles; `elementary.liquid` uses it for unary declarations and
  primitive expression rules. Operation names and domain conditions are stored once.
- `shared/statements.liquid` renders rules from library, symbolic, contract, and
  proof templates. Inline rows use `kind~label~body~metadata[~attributes]`.
  Formatted rows use `kind~label~lhs~rhs~guard~metadata`; each rule occupies one
  data row instead of storing the generated line breaks.
- `shared/wrap-term.liquid` supplies the common 100-column formatting for the
  formatted rules. `arity-table.liquid` expands grouped names and arities into
  nested lists, using that same statement-formatting path.

Rows are separated by `|`; these separators and `~` are reserved in rule data.
A metadata field of `-` selects the module default; a guard of `-` means no
condition. Full `p3109-` labels bypass the module prefix. An empty default omits
metadata for proof slices; inline attributes retain `nonexec`. Rows beginning
with `!` preserve literal blocks such as module/view boundaries. Small files
retain literal text where additional abstraction would add overhead.

The regrouping reduced aggregate Liquid content, including all shared partials:

| Measure | Before | After |
| --- | ---: | ---: |
| Physical lines (including final lines without a newline) | 1,898 | 1,588 |
| Bytes | 98,694 | 95,773 |

That is **310 fewer lines (16.3%)**, with six shared partials serving the same
32 entry points. This factors schemas and generated formatting; it does not
pack unrelated declarations onto fewer lines or move content into non-Liquid
data files.

Validation compared every old template output, new template output, and Maude
source byte-for-byte, then checked all 32 written files from `--output-dir`.
Labels, equation order, guards, metadata, comments, whitespace, and trailing
newlines are preserved.
