# Validation results

Checked on 2026-09-08 with Lean 4.33.1, pinned by `lean-toolchain`.

## Passed

- `python3 reorganize.py`: all 24 extracted modules, the public entry point,
  and manifest match the reviewed generation. The bodies reconstruct all
  20,920 source lines byte for byte; the original source SHA-256 remains
  `2a94d856a75b61df1bb3a59a48d9c4b602067a6d00af5b1e48cf2533071b24b6`.
- Source and extracted modules contain the same six mutual blocks, 550
  explicit axioms, 2,148 theorems, and 149 attribute commands. Neither has
  a `sorry` token.
- Lean compiled `P3109.Foundations`, `P3109.Syntax`,
  `P3109.Native.Operators`, `P3109.Predicates`, and
  `P3109.Relations.AxiomaticEquality`. The predicate module retains the
  source's unused-variable warnings.
- `lake env lean CheckFoundations.lean`: an independent client imports the
  completed foundation, checks type aliases, kind assignment and axiomatic
  equality, and resolves all five native operator names discussed earlier.

## Incomplete: full compilation

`lake build` was interrupted with exit 130 while compiling
`P3109.Relations.EquationalEquality`. No Lean errors had been reported.
Compilation spent over ten minutes in that large mutual definition while
system memory pressure increased. Near interruption, the environment reported
about 84 GiB used out of 93 GiB RAM and almost all 8 GiB of swap occupied.
These are whole-system figures, not a measurement of Lean's individual RSS.

An earlier concurrent compilation of the unchanged original was also
interrupted (exit 130) to recover memory. It is not a passing baseline.
Stopping that duplicate did not remove the subsequent resource pressure.

Consequently, the later modules and the full `Check.lean` importing client
have **not** been validated by compilation. Textual preservation is not a
claim that the complete source or split library compiles successfully.
No axioms, proofs, or mutual definitions were weakened to work around this.

A subsequent isolated attempt used one Lean thread, an 8 GiB Lean memory
limit, and a five-minute wall-clock limit:

```sh
timeout 300 lake env lean -j1 -M8192 P3109/Relations/EquationalEquality.lean
```

It reached the wall-clock limit (exit 124) without reporting a Lean error.
This bounded attempt also did not establish successful compilation.

## Remaining checks

In an environment with sufficient available memory, run these sequentially
from this directory:

```sh
lake build
lake env lean Check.lean
python3 reorganize.py
```

The Lake cache retains the completed modules. Avoid running an original-file
baseline alongside the full library build. If compilation remains impractical,
reducing the generated mutual definitions is a separate design task: it can
change recursors and declaration dependencies and is outside this lossless
reorganization.
