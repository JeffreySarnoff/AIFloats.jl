
❯ maude2lean --help

  Ran 2 shell commands

Already installed via pipx (~/.local/share/pipx/venvs/maude2lean), Lean at ~/.elan. Help output:

usage: maude2lean [-h] [--verbose] [--no-advise] [--dump] [-o O]
                  [--module NAME] [--metamodule NAME] [--prefer-quotes YN]
                  [--use-notation NAMES ...] [--declare-notation NAMES ...]
                  [--with-ctor-predicate YN] [--with-error-free-opt YN]
                  [--with-lemmas YN] [--with-aliases YN] [--with-repr YN]
                  [--with-rules YN] [--with-frozen YN] [--with-simp YN]
                  [--with-axiom-simp YN] [--with-sort2kind YN]
                  [--with-derived-as-consts YN] [--with-derived-as-defs YN]
                  [--with-native-bool YN] [--split-eqe NAMES ...]
                  [--has-sort-symbol NAME] [--eqa-symbol NAME]
                  [--eqe-symbol NAME] [--rw-one-symbol NAME]
                  [--rw-star-symbol NAME] [--outermost-namespace NAME]
                  [--with-original-stmt YN] [--lean-version VALUE]
                  source [source ...]

Translate Maude specifications to Lean programs

Key options:
- source — Maude files. -o FILE output. --module NAME module to translate. --metamodule NAME translate a metarepresentation instead.
- --lean-version VALUE — default 3. Use --lean-version 4 for current Lean.
- --with-rules YN include rewrite rules and =>1 / =>* relations (default yes).
- --with-lemmas, --with-aliases, --with-repr, --with-simp, --with-sort2kind, --with-ctor-predicate — all default yes.
- --with-derived-as-consts / --with-derived-as-defs — non-constructor ops outside inductive type (default no).
- --with-native-bool YN map Maude Bool to Lean bool (default no).
- --with-error-free-opt YN drop sort-membership premises for error-free kinds (default no).
- --use-notation / --declare-notation NAMES infix for relations; symbols set via --has-sort-symbol (⊳), --eqa-symbol (=A), --eqe-symbol (=E), --rw-one-symbol (=>1), --rw-star-symbol (=>*).
- --split-eqe NAMES split top-level equation application as subrelation of eqe for given kinds.
- --outermost-namespace NAME (default Maude). --with-original-stmt YN keep Maude statement as comment. --prefer-quotes YN.
- --dump print auxiliary file. -v, --no-advise.

Typical:
maude2lean --lean-version 4 --module MYNAT -o MyNat.lean mynat.maude



❯ how to use maude2lean with a Maude specification that spans mutiple directorys and many source files?

  Ran 3 shell commands

Tested with nested dirs; works. Mechanism: maude2lean does no file discovery itself. It calls Maude's load on each source you give, then translates one module (--module) with all its imports flattened. So Maude's own loading rules apply.

Option 1: top-level file (simplest). Make one entry file that loads/sloads everything, relative paths resolve to including file's directory, as in normal Maude:
*** app/main.maude
sload ../lib/list
fmod MAIN is pr LIST . ... endfm
maude2lean --lean-version 4 --module MAIN -o Main.lean app/main.maude
Works from any cwd. Prefer sload over load for shared deps; avoids "redefining module" advisories when many files pull same base file.

Option 2: list files on command line, dependency order. Loaded in given order:
maude2lean --lean-version 4 --module MAIN -o Main.lean lib/base/elem.maude lib/list.maude app/main.maude

Option 3: spec file (JSON/YAML/TOML). Holds source list plus all options; relative paths resolve against spec file's dir:
{
  "source": ["../lib/base/elem.maude", "../lib/list.maude", "main.maude"],
  "module": "MAIN",
  "lean-version": 4,
  "with-original-stmt": true
}
maude2lean -o Main.lean app/main.json
Spec also supports sort-renaming, kind-renaming, op-renaming (not on CLI). Schema: maude2lean --dump schema. Command-line flags override spec values. Can mix: maude2lean app/main.json extra.maude.

Shared library dirs: set MAUDE_LIB=/path/to/lib:...; bare sload list resolves there. Note the pip maude bindings ship own prelude; existing /etc/profile.d/maude.sh MAUDE_LIB (stock + ITP) fine to extend.

Output: one .lean for one module. Big spec spanning many modules: run once per top module of interest, each output self-contained (imports flattened, so overlapping modules get duplicated across outputs; use --outermost-namespace to keep them apart).


❯ how to use maude2lean with a Maude specification that spans mutiple directorys and many source files to obtain a Lean specification that reflects the same organization?

Short answer: not possible directly. maude2lean translates exactly one module into one self-contained .lean file. Imports get flattened; no import lines generated, no per-Maude-module namespaces. Only namespaces emitted: Maude (outer) and one per kind (kList, kBool).

Why flattening is fundamental, not just missing feature. Each Maude kind becomes one Lean inductive holding all operators of that kind. A module importing LIST and adding op twice : List -> List extends the same kind. Lean inductives are closed: cannot add constructors to kList in a later file. Same for eqe/=>1 relations: closed inductive Props. So MAIN.lean cannot import LIST.lean and extend it. Only escape: --with-derived-as-consts yes / --with-derived-as-defs yes puts non-constructor ops outside inductive, but constructors and the rewrite relations still must be complete per module.

Nearest workable layout: one Lean file per Maude module, mirroring directories, each self-contained.

1. Spec files alongside Maude sources, one per module you care about:
lib/base/elem.json   {"source":"elem.maude","module":"ELEM","outermost-namespace":"Elem","lean-version":4}
lib/list.json        {"source":"list.maude","module":"LIST","outermost-namespace":"List","lean-version":4}
app/main.json        {"source":"main.maude","module":"MAIN","outermost-namespace":"Main","lean-version":4}
   Distinct outermost-namespace per module. Otherwise all outputs open namespace Maude and clash if imported together.
2. Driver, mirrors tree into Lean project:
#!/bin/sh
# usage: ./gen.sh <maude-root> <lean-root>
find "$1" -name '*.json' | while read spec; do
  rel=${spec#"$1"/}; out="$2/${rel%.json}.lean"
  mkdir -p "$(dirname "$out")"
  maude2lean -o "$out" "$spec"
done
   Result: Lean/lib/base/elem.lean, Lean/lib/list.lean, Lean/app/main.lean. Each file duplicates the closed-over content of its imports under its own namespace.
3. Lean side: lakefile with those as library roots. Theorems about LIST go next to list.lean; theorems about MAIN re-prove or restate against Main.kList, since Main.kList and List.kList are different types. Bridge lemmas (embedding List.kList → Main.kList) you write by hand if needed.

Alternative if you want a single coherent theory: translate only top module(s), get one big file per entry point, organize proofs by directory instead of the generated definitions. Simpler, no duplicated types, loses file-level mirroring of definitions only.

Renaming to reduce clutter: spec keys sort-renaming, kind-renaming, op-renaming (maps Maude names to Lean names; see maude2lean --dump schema).


=====

how best to use maude2lean with load-core.maude?

The translation succeeds and outputs a 1 MB Lean file, but core rational operations (floor, sum, mul, pow2, gteq) all come through as uninterpreted constructors — the 75 "special operators" warning. I'll check whether the file actually type-checks and look into how maude2lean handles builtin mappings.

I found that the literal 16 is being incorrectly translated to just 1, suggesting maude2lean is collapsing iterated successor literals and mangling numeric constants across the spec. I'll verify this against other literals and check maude2lean's source

All numeric constants (64, 53, 1023, 32) and string literals get wiped out during translation into a placeholder or "s zero." I'll check if the Maude bindings expose the iterated-s_ exponent to fix this, and identify which modules are builtin-free

Short answer: don't run it on P3109-CORE as-is. I ran it, and the output has three independent defects, two of them silent.

What happened

maude2lean --lean-version 4 --module P3109-CORE -o P3109Core.lean load-core.maude
Runs, emits 8,774 lines / 1 MB, one warning: 75 special operators like s_ whose behavior is not equationally defined. Then:

Every numeric literal is destroyed. BitwidthOf(binary64) = 64, PrecisionOf(binary64) = 53, ExponentBiasOf(binary64) = 1023, = 16, = 32 — all emit as kXReal.s kXReal.zero, i.e. 1. Maude stores literals as iterated s_^n(0); the bindings expose Term.getIterExponent(), but maude2lean never calls it (grep of the package: no hit). Silent, and fatal for a numeric spec.
All 32 string literals collapse to one placeholder ltStringsgt.
Rational arithmetic is uninterpreted. special.py handles only if_then_else_fi and ==/=/=. sum, mul, slash, floor, pow, gteq — the whole of ROUND/SATURATE/CODEC — become opaque constructors with no equations. Nothing reduces.
And it doesn't type-check anyway: Lean 4.33.1 stops at 100 errors, first is Unknown constant Maude.kProjSpec.eqe at line 2076 — a forward reference the Lean-4 writer doesn't order.
Point 3 is the same boundary planmaude.md §9 and run-proofs.py already draw for CRC/SCC: built-in RAT is outside every tool's scope. maude2lean is no different.

Where the builtins enter
Only four files: xreal.maude (RAT), projection-spec.maude and sequences.maude (INT), format-core.maude (CONVERSION, for formatName only). But flattening pulls them into every top module, so "translate the builtin-free part" needs a split first.

How to actually use it
1. Patch the literal bug before anything else. In maude2lean's term emitter, when term.symbol() is an iter symbol (s_), read term.getIterExponent() and emit a Lean numeral (or n nested s). Small change; without it no output is trustworthy. Report upstream with 64 → s zero as the repro. Same for strings if you need them.

2. Split the spec at the builtin boundary and translate only above it. Candidates with no arithmetic in their own equations: format syntax/validity (once formatName/CONVERSION is moved out), projection-spec constructors, sequences, block shapes, conformance data, the ω special-value case tables, Class, TotalOrder. Give each its own spec file and --outermost-namespace, per your maude2lean.md notes. Keep --with-original-stmt yes; equation labels survive (eq_p3109-format-core-041), so the traceability matrix carries straight into Lean.

3. Write the rational core directly in Lean over ℚ, not through maude2lean: ωRoundToPrecision, ωSaturate, ωDecode/ωEncode, ωProject, and the finite branches of the ω-ops. This is the honest route the plan already implies: the Maude side is executable-exact over RAT, the Lean side is provable over ℚ, and the bridge is the shared test corpus — tests/vectors/tables-3-7.json and the property rows evaluated on both. A hand-written toRat : kXReal → Option ℚ plus per-op agreement lemmas connects the translated layers to the hand-written core.

4. Then debug the Lean-4 writer error on a small translated module first, not the 1 MB file — the kProjSpec.eqe forward reference may vanish once RAT is out, or may need a flag bisect (--with-lemmas, --with-simp, --split-eqe). I did not chase it; unknown whether it's input-dependent.

What maude2lean is good for here: extracting sorts, subsort graph, constructor signatures, and equation shapes with labels — a scaffold. Not a semantics-preserving translation of this spec.

Scratch outputs are in the session scratchpad only; nothing in the repo changed.

