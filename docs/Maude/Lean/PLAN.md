# Lean source reorganization

## Source and scope

The requested `../spect2.lean` does not exist; use `../spec2.lean` (20,920
lines) as the source. Leave it unchanged. This is a structural reorganization,
not a revision of the translated specification, its axioms, or its proofs.
Keep all public names in the existing `Maude` namespace.

## Plan

1. Establish whether the original compiles with the installed Lean 4.33.1.
2. Create a self-contained Lake library, `P3109`, with no external packages
   and a pinned toolchain. Its single public entry point is `import P3109`.
3. Separate the foundations, syntax, native operator declarations, kind and
   constructor predicates, equality modulo axioms, membership/equality modulo
   equations, native equations, rewriting relations, and generic congruence.
4. Group equational lemmas and aliases into Boolean, extended-real, format,
   sequence/block, conformance, and native-attribute modules. Group rewriting
   lemmas similarly, with separate block, rational, and string modules.
5. Put string representations and `Repr` instances in the final module.
6. Generate modules from contiguous source spans. Add only imports and outer
   namespace wrappers. Record source hashes and spans in a manifest; provide
   a deterministic generator with a read-only verification mode.
7. Build the entire library and check an importing client. Verify that
   concatenating the module bodies reconstructs the original byte for byte.
   Record the actual results and any inherited limitations.

## Plan review (before implementation)

**Accepted with constraints.** Splitting by IEEE operation alone would break
the six mutually recursive groups. Keep each `mutual ... end` group intact,
including the large equality/membership and rewriting relation definitions.
Consequently some kernel files remain large. Splitting these further would
change the translation rather than merely organize it.

Namespace boundaries are safe places to split lemma families. Preserve their
source order through an explicit import chain: generated aliases and global
`simp`/`congr` attributes can affect later elaboration. This initial structure
prioritizes faithful elaboration over maximum independent compilation.
Each file also remains directly importable with its prerequisites.

Do not rename `MRat`, replace axioms with implementations, remove unused
operators, or fix inherited warnings as part of this task. In particular,
`ascii`, `char`, `find`, `modExp`, and `rfind` retain their source status.

The generator must reject a changed source hash, missing/extra module files,
or altered generated contents when verifying. Regeneration is explicit;
ordinary builds never overwrite files. The unchanged source plus a lossless
content check establishes textual preservation; Lean compilation and an
importing client check validate the new module boundaries.

## Acceptance criteria

- Every original source line occurs once and in order, apart from the outer
  namespace wrapper reproduced around each module.
- All generated Lean modules compile under the pinned toolchain.
- A client can import `P3109` and use representative original declarations,
  relation lemmas, native axioms, and representation instances.
- The source file is unchanged, and all new project files are under this
directory. No other repository documents or specifications supply content.

## Implemented structure

The reviewed boundaries produce 24 source modules plus `P3109.lean` as the
entry point. `README.md` groups these by purpose; `manifest.json` records
every exact boundary and import. `Check.lean` is a separate importing client,
not part of the translated specification. Build artifacts remain in the
ignored `.lake/` directory.

## Validation adjustment

The original-file baseline and library build were initially run together.
Both reached the large relation definitions, but combined memory demand
exhausted available RAM and swap. The duplicate baseline was interrupted
(exit 130), with unused-variable warnings and no reported Lean errors at
that point. It is not recorded as a successful baseline compilation.
Continue with the library build alone and the lossless source comparison;
do not run these two expensive checks concurrently.

The single library build subsequently encountered renewed memory pressure
and was also interrupted. Structural implementation and lossless verification
are complete; the full-compilation and full-client acceptance criteria remain
unverified. A bounded single-thread attempt also timed out. See
`VALIDATION.md` for the passing subset and remaining checks.
