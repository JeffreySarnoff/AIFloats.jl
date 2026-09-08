#!/usr/bin/env python3
"""Reproduce the reviewed split of spec2.lean; default to read-only verification."""
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT.parent / "spec2.lean"
SOURCE_SHA256 = "2a94d856a75b61df1bb3a59a48d9c4b602067a6d00af5b1e48cf2533071b24b6"
# Inclusive source starting lines; the next start determines the preceding end.
SECTIONS = [
    ("Foundations", 2),
    ("Syntax", 74),
    ("Native/Operators", 550),
    ("Predicates", 725),
    ("Relations/AxiomaticEquality", 962),
    ("Relations/EquationalEquality", 1505),
    ("Native/Equations", 3335),
    ("Relations/Rewriting", 3735),
    ("Lemmas/Congruence", 7871),
    ("Lemmas/Equations/Bool", 7889),
    ("Lemmas/Equations/XReal", 8438),
    ("Lemmas/Equations/Formats", 8979),
    ("Lemmas/Equations/SequencesAndBlocks", 9267),
    ("Lemmas/Equations/Conformance", 9764),
    ("Lemmas/Equations/Native", 10251),
    ("Lemmas/Rewriting/Bool", 10261),
    ("Lemmas/Rewriting/XReal", 11233),
    ("Lemmas/Rewriting/Formats", 11923),
    ("Lemmas/Rewriting/Sequences", 12258),
    ("Lemmas/Rewriting/Blocks", 12928),
    ("Lemmas/Rewriting/Conformance", 15843),
    ("Lemmas/Rewriting/Rationals", 16528),
    ("Lemmas/Rewriting/Strings", 20396),
    ("Representation", 20414),
]


def digest(data):
    return hashlib.sha256(data).hexdigest()


def expected_files():
    original = SOURCE.read_bytes()
    if digest(original) != SOURCE_SHA256:
        raise ValueError("Source changed: review the section boundaries and source hash first.")
    lines = original.splitlines(keepends=True)
    if len(lines) != 20920 or lines[0] != b"namespace Maude\n" or lines[-1] != b"end Maude\n":
        raise ValueError("Unexpected source layout")
    files, entries, bodies = {}, [], []
    previous = None
    for index, (section, start) in enumerate(SECTIONS):
        stop = SECTIONS[index + 1][1] if index + 1 < len(SECTIONS) else len(lines)
        body = b"".join(lines[start - 1:stop - 1])
        module = "P3109." + section.replace("/", ".")
        path = "P3109/" + section + ".lean"
        header = (f"-- Extracted from ../spec2.lean, lines {start}-{stop - 1}.\n"
                  "-- See PLAN.md and manifest.json for provenance.\n")
        if previous:
            header += f"import {previous}\n"
        header += "\nnamespace Maude\n"
        files[path] = header.encode() + body + b"end Maude\n"
        entries.append({"module": module, "file": path, "source_start": start,
                        "source_end": stop - 1, "imports": [previous] if previous else [],
                        "body_sha256": digest(body)})
        bodies.append(body)
        previous = module
    if lines[0] + b"".join(bodies) + lines[-1] != original:
        raise ValueError("Split does not reconstruct source")
    files["P3109.lean"] = (
        "-- Public entry point for the complete, unchanged Maude translation.\n"
        f"import {previous}\n").encode()
    manifest = {"source": "../spec2.lean", "source_sha256": SOURCE_SHA256,
                "source_lines": len(lines), "namespace": "Maude", "modules": entries}
    files["manifest.json"] = (json.dumps(manifest, indent=2) + "\n").encode()
    return files


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="explicitly regenerate the reviewed modules")
    args = parser.parse_args()
    try:
        expected = expected_files()
        actual = {str(p.relative_to(ROOT)) for p in (ROOT / "P3109").rglob("*.lean")}
        extra = actual - set(expected)
        if extra:
            raise ValueError("Unexpected modules: " + ", ".join(sorted(extra)))
        for name, data in expected.items():
            path = ROOT / name
            if args.write:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(data)
            elif not path.is_file() or path.read_bytes() != data:
                raise ValueError(f"Missing or changed generated file: {name}")
        verb = "Generated" if args.write else "Verified"
        print(f"{verb} {len(SECTIONS)} modules and P3109.lean; all 20,920 source lines preserved.")
    except (OSError, ValueError) as exc:
        parser.exit(1, f"error: {exc}\n")


if __name__ == "__main__":
    main()
