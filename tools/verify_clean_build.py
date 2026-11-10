#!/usr/bin/env python3
"""Fresh local and required pinned AF build, reusing only package caches.

Creates and retains a detached AF worktree and empty local output directory.
Never deletes outputs, updates pins, or accepts historical local compiler rows.
Use a new output prefix: existing verification records are never overwritten.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def command(argv, cwd, env):
    result = subprocess.run(argv, cwd=cwd, env=env, text=True,
                            capture_output=True, check=False)
    require(result.returncode == 0,
            f"{argv!r}\n{result.stdout}\n{result.stderr}")
    return result.stdout.strip()


def imports(path):
    # Current repository and pinned AF use one module name per import line.
    # Reuse the auditor's comment/string masker before scanning.
    from verify_lean import lean_code_only
    return re.findall(r"^import\s+([A-Za-z0-9_.]+)",
                      lean_code_only(path.read_text()), re.MULTILINE)


def logged(argv, cwd, env, path):
    started = datetime.now(timezone.utc).isoformat()
    tick = time.monotonic()
    print(f"START {started}: {argv!r}; log={path}", flush=True)
    with path.open("w") as log:
        result = subprocess.run(argv, cwd=cwd, env=env, stdout=log,
                                stderr=subprocess.STDOUT, check=False)
    elapsed = time.monotonic() - tick
    require(result.returncode == 0,
            f"Build failed ({result.returncode}); inspect {path}")
    print(f"PASS after {elapsed:.1f}s: {path.name}", flush=True)
    return {"command": argv, "working_directory": str(cwd),
            "started_at": started, "elapsed_seconds": round(elapsed, 3),
            "exit_code": result.returncode, "log_sha256": sha(path)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--af", type=Path, required=True,
                        help="Git checkout used only to create pinned detached worktree")
    parser.add_argument("--packages", type=Path, required=True,
                        help="Existing pinned .lake/packages cache directory")
    parser.add_argument("--lake", default=str(Path.home() / ".elan/bin/lake"))
    parser.add_argument("--output-prefix", type=Path, required=True)
    parser.add_argument("--jobs", type=int, default=6)
    args = parser.parse_args()
    require(args.jobs > 0, "Positive jobs required")
    prefix = args.output_prefix.resolve()
    af_record = Path(str(prefix) + "-af.json")
    local_record = Path(str(prefix) + "-local.json")
    require(not af_record.exists() and not local_record.exists(),
            "Refusing to overwrite a verification record")
    pins = json.loads((ROOT / "lean/dependencies.json").read_text())
    env = dict(os.environ)
    env.pop("LEAN_PATH", None)
    env.pop("LEAN_SRC_PATH", None)
    # Bound threads inside each Lean process; local processes are bounded by --jobs.
    env["LEAN_NUM_THREADS"] = "2"
    packages = args.packages.resolve()
    manifest = json.loads((args.af / "lake-manifest.json").read_text())
    package_pins = {}
    for package in manifest["packages"]:
        path = packages / package["name"]
        actual = command(["git", "rev-parse", "HEAD"], path, env)
        require(actual == package["rev"], f"Package pin: {package['name']}")
        command(["git", "diff", "--exit-code", "HEAD", "--"], path, env)
        package_pins[package["name"]] = actual
    require(package_pins["mathlib"] == pins["mathlib_commit"], "Mathlib pin")
    initial_sources = {p.name: sha(p) for p in sorted((ROOT / "lean").glob("*.lean"))}
    work = Path(tempfile.mkdtemp(prefix="przz-clean-20261110-"))
    print(f"BUILD_ROOT={work}", flush=True)
    af = work / "af"
    command(["git", "worktree", "add", "--detach", str(af), pins["af_commit"]],
            args.af.resolve(), env)
    require((af / "lean-toolchain").read_text().strip() == pins["lean_toolchain"],
            "Lean toolchain pin")
    require(json.loads((af / "lake-manifest.json").read_text()) == manifest,
            "Package-cache manifest differs from pinned AF manifest")
    (af / ".lake").mkdir()
    (af / ".lake/packages").symlink_to(packages, target_is_directory=True)
    require(not (af / ".lake/build").exists(), "AF output directory not empty")
    local = work / "local"
    require(not local.exists(), "Local output directory not empty")
    roots = sorted({n for p in (ROOT / "lean").glob("*.lean")
                    for n in imports(p) if n.startswith("Zeta23.")})
    sources = {}

    def visit(name):
        if name in sources:
            return
        path = af / (name.replace(".", "/") + ".lean")
        require(path.is_file(), f"Missing pinned AF source: {name}")
        sources[name] = sha(path)
        for dependency in imports(path):
            if dependency.startswith("Zeta23."):
                visit(dependency)

    for name in roots:
        visit(name)
    require(roots, "No AF imports found")
    prefix.parent.mkdir(parents=True, exist_ok=True)
    stage = logged([args.lake, "--no-cache", "build"] +
                   [n + ":olean" for n in roots], af, env, work / "af-build.log")
    artifacts = {}
    for name, digest in sources.items():
        path = af / (name.replace(".", "/") + ".lean")
        require(sha(path) == digest, f"AF source changed: {name}")
        olean = af / ".lake/build/lib/lean" / (name.replace(".", "/") + ".olean")
        require(olean.is_file(), f"Missing new AF artifact: {name}")
        artifacts[name] = sha(olean)
    command(["git", "diff", "--exit-code", "HEAD", "--"], af, env)
    af_data = {
        "date": datetime.now(timezone.utc).date().isoformat(),
        "scope": "Fresh complete required AF source closure; pinned Mathlib/package caches reused",
        "af_commit": pins["af_commit"], "mathlib_commit": pins["mathlib_commit"],
        "package_pins": package_pins, "lean_toolchain": pins["lean_toolchain"],
        "af_tracked_sources_clean": True, "af_output_directory_initially_absent": True,
        "inherited_LEAN_PATH_unset": True, "old_af_build_outputs_used": False,
        "mathlib_source_rebuilt": False, "af_roots": roots,
        "af_source_module_count": len(sources),
        "af_newly_built_module_count": len(artifacts),
        "af_source_sha256": sources, "af_olean_sha256": artifacts,
        "build": stage, "build_root": str(work),
        "runner_sha256": sha(Path(__file__)),
    }
    af_record.write_text(json.dumps(af_data, indent=2) + "\n")
    stage = logged([sys.executable, "-B", str(ROOT / "tools/verify_finite_family_rows.py"),
                    "--af", str(af), "--lake", args.lake, "--target", "WuProportion",
                    "--all-local", "--build", str(local), "--jobs", str(args.jobs),
                    "--output", str(local_record)], ROOT, env, work / "local-build.log")
    data = json.loads(local_record.read_text())
    require(data["full_project_rebuilt"] and
            data["fresh_module_count"] == data["module_count"] == len(initial_sources),
            "Not every local module was freshly compiled")
    require({p.name: sha(p) for p in (ROOT / "lean").glob("*.lean")} == initial_sources,
            "Local source set changed during build")
    require(all(row["sha256"] == initial_sources[name] and not row["reused_this_run"]
                for name, row in data["checks"].items()), "Source or reuse mismatch")
    # The scoped auditor already checked all recorded outputs and headline types.
    data.update({
        "scope": "All local sources freshly compiled against freshly built required AF closure; fixed Mathlib/package caches reused",
        "date": datetime.now(timezone.utc).date().isoformat(),
        "local_output_directory_initially_absent": True, "prebuilt_used": False,
        "clean_upstream_build_performed": True,
        "upstream_verification_record": af_record.name,
        "upstream_verification_sha256": sha(af_record),
        "clean_build": stage, "build_root": str(work),
        "clean_runner_sha256": sha(Path(__file__)),
        "axiom_audit_count": sum(len(re.findall(
            r"^'.*' (?:depends on axioms:|does not depend on any axioms)",
            row["output"], re.MULTILINE)) for row in data["checks"].values()),
    })
    local_record.write_text(json.dumps(data, indent=2) + "\n")
    print(f"PASS: {len(sources)} fresh AF modules; {data['fresh_module_count']} fresh local modules; "
          f"{data['axiom_audit_count']} axiom audits", flush=True)


if __name__ == "__main__":
    main()
