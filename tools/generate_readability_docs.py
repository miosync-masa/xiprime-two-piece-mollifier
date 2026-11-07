#!/usr/bin/env python3
"""Regenerate every readability document under docs/ (or verify them).

    python3 tools/generate_readability_docs.py --af <pinned AF checkout>
    python3 tools/generate_readability_docs.py --check   # fail if any output would change

The generators are deterministic: identical inputs give byte-identical files.
Pass the same ``--af`` to ``--check`` as to the generating run; without it the
trust base omits the lake-manifest cross-check and therefore differs.
Human correspondence input is read-only unless --sync-manual is explicitly
requested; --check rejects that writing option.
"""
import argparse
import hashlib
import subprocess
import sys
import tempfile
from pathlib import Path

import readability_common as rc

ROOT = Path(__file__).resolve().parents[1]
TOOLS = ROOT / "tools"
OUTPUTS = ["docs/dependency-graph.json", "docs/dependency-graph.dot", "docs/dependency-graph.svg",
           "docs/dependency-graph.md", "docs/modules.md", "docs/paper-correspondence.md", "docs/trust-base.md"]


def run(script, *args):
    subprocess.run([sys.executable, "-B", str(TOOLS / script), *args], cwd=ROOT, check=True)


def generate(docs, af, sync_manual=False):
    # Validate before any generator writes an artifact or synchronizes input.
    rc.load_verified_record(rc.load_modules())
    run("gen_dependency_graph.py", "--out", str(docs))
    run("gen_modules_table.py", "--out", str(docs / "modules.md"))
    run("gen_paper_correspondence.py", "--out", str(docs / "paper-correspondence.md"),
        *(["--sync-manual"] if sync_manual else []))
    run("gen_trust_base.py", "--out", str(docs / "trust-base.md"), *(["--af", af] if af else []))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--af", help="pinned AF checkout for lake-manifest.json / lean-toolchain")
    ap.add_argument("--check", action="store_true", help="regenerate into a temporary directory and compare")
    ap.add_argument("--sync-manual", action="store_true",
                    help="explicitly synchronize labels in the human correspondence JSON")
    args = ap.parse_args()
    if args.check and args.sync_manual:
        ap.error("--check is read-only and cannot be combined with --sync-manual")
    if not args.check:
        generate(ROOT / "docs", args.af, args.sync_manual)
        return
    with tempfile.TemporaryDirectory() as tmp:
        generate(Path(tmp), args.af)
        changed = []
        for rel in OUTPUTS:
            a = (ROOT / rel).read_bytes() if (ROOT / rel).exists() else b""
            b = (Path(tmp) / Path(rel).name).read_bytes()
            if hashlib.sha256(a).digest() != hashlib.sha256(b).digest():
                changed.append(rel)
        if changed:
            print("STALE: " + ", ".join(changed))
            sys.exit(1)
        print("OK: all generated documents are up to date")


if __name__ == "__main__":
    main()
