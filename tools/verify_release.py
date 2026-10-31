#!/usr/bin/env python3
"""Verify, never regenerate, the finite certificate and distribution manifest."""
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
RUNTIME_DIRS = {".git", ".venv", "venv", "af", ".lake", "build", "dist",
                "__pycache__", ".vscode", ".idea"}
RUNTIME_SUFFIXES = {".pyc", ".pyo", ".aux", ".log", ".out", ".toc", ".fls",
                    ".fdb_latexmk", ".olean", ".ilean", ".trace"}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def distributable_files():
    for parent, dirs, files in os.walk(ROOT, followlinks=False):
        dirs[:] = sorted(d for d in dirs if d not in RUNTIME_DIRS)
        for name in dirs + sorted(files):
            path = Path(parent) / name
            require(not path.is_symlink(), f"Symlink not allowed: {path.relative_to(ROOT)}")
        for name in sorted(files):
            path = Path(parent) / name
            if (name == ".DS_Store" or path.suffix in RUNTIME_SUFFIXES
                    or name.endswith(".synctex.gz")):
                continue
            require(not name.startswith(".env"), "Remove environment files from the distribution")
            rel = path.relative_to(ROOT).as_posix()
            if rel != "SHA256SUMS":
                yield rel


def verify_manifest():
    manifest = {}
    for line in (ROOT / "SHA256SUMS").read_text().splitlines():
        match = re.fullmatch(r"([0-9a-f]{64})  (.+)", line)
        require(match is not None, "Malformed SHA256SUMS line")
        digest, rel = match.groups()
        path = PurePosixPath(rel)
        require(not path.is_absolute() and ".." not in path.parts and "\\" not in rel,
                f"Unsafe manifest path: {rel}")
        require(rel not in manifest, f"Duplicate manifest path: {rel}")
        manifest[rel] = digest
    actual = set(distributable_files())
    require(actual == set(manifest),
            f"Manifest coverage differs: unlisted={sorted(actual-set(manifest))}, "
            f"missing={sorted(set(manifest)-actual)}")
    for rel, expected in manifest.items():
        require(hashlib.sha256((ROOT / rel).read_bytes()).hexdigest() == expected,
                f"Hash mismatch: {rel}")
    return len(manifest)


def verify_links():
    for rel in distributable_files():
        if not rel.endswith(".md"):
            continue
        source = ROOT / rel
        for target in re.findall(r"\[[^\]\n]+\]\(([^)\s]+)\)", source.read_text()):
            if "://" in target or target.startswith(("#", "mailto:")):
                continue
            target = target.split("#", 1)[0]
            require((source.parent / target).is_file(), f"Broken link in {rel}: {target}")


def main():
    require(not sys.flags.optimize and not os.environ.get("PYTHONOPTIMIZE"),
            "Run without Python optimization: the original certificate uses assertions")
    count = verify_manifest()
    verify_links()
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
    proc = subprocess.run([sys.executable, "-B", "verify.py", "--manifest"],
                          cwd=ROOT / "paper", env=env, capture_output=True, check=False)
    require(proc.returncode == 0, "Finite verifier failed:\n" + proc.stderr.decode())
    require(proc.stdout == (ROOT / "paper/certificate.json").read_bytes(),
            "Fresh output differs from the stored finite certificate")
    json.loads(proc.stdout)
    print(f"PASS: {count} distribution hashes and local Markdown link targets")
    print("PASS: exact rational checks and all four interval runs")
    print("PASS: fresh certificate JSON matches the saved file byte-for-byte")
    print("Scope: Python finite certificate only; the Lean proportion theorem and its external PRZZ input are audited separately.")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        sys.exit(1)
