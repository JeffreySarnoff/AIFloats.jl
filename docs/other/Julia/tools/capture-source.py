#!/usr/bin/env python3
"""Optional migration-only capture of the independent Python/Maude fixture corpus.

Normal Julia tests use frozen fixtures and do not invoke this script or Maude.
--check compares decompressed bytes without writing. Regeneration is explicit.
"""
import argparse
import gzip
import hashlib
import importlib.util
import json
import re
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT.parent / "Maude"
SUITES = ["smoke", "domains", "codec", "projection", "scalar", "order-next",
          "blocks", "conformance", "symbolic", "order-full", "standalone"]


def standalone():
    for path in sorted((SOURCE / "tests").glob("*.maude")):
        for match in re.finditer(r'check\("([^"]+)", \((.*)\)\) \.', path.read_text()):
            case, expression = match.groups()
            yield case, expression


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    sys.path.insert(0, str(SOURCE / "tools"))
    spec = importlib.util.spec_from_file_location("source_suites", SOURCE / "tools/run-tests.py")
    suites = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(suites)
    target = ROOT / "test/vectors"
    summary = {}
    for suite in SUITES:
        rows = list(standalone() if suite == "standalone" else suites.fixtures(suite))
        ids = [row[0] for row in rows]
        if len(ids) != len(set(ids)):
            raise RuntimeError(f"duplicate source case IDs in {suite}")
        body = "".join(json.dumps({"id": i, "expression": e}, separators=(",", ":")) + "\n"
                       for i, e in rows).encode()
        path = target / (suite + ".jsonl.gz")
        if args.check:
            if gzip.decompress(path.read_bytes()) != body:
                raise RuntimeError(f"source fixtures changed: {suite}")
        else:
            path.write_bytes(gzip.compress(body, mtime=0))
        summary[suite] = {"cases": len(rows), "sha256": hashlib.sha256(body).hexdigest(),
                          "duplicate_ids": 0}
    manifest = json.dumps(summary, indent=2) + "\n"
    if args.check:
        if (target / "manifest.json").read_text() != manifest:
            raise RuntimeError("fixture manifest changed")
    else:
        (target / "manifest.json").write_text(manifest)
    print("PASS source fixture capture:", sum(s["cases"] for s in summary.values()), "cases")


if __name__ == "__main__":
    main()
