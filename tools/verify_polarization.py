#!/usr/bin/env python3
"""Freshly compile only the polarization bridge and its local import closure.

AF/Mathlib package caches are reused. This is not a full project rebuild.
The previous 698-module verification record is never overwritten.
"""
import argparse
import json
import os
from pathlib import Path
import subprocess
import tempfile

from verify_lean import ROOT, audit_polarization, require, run, sha


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--af", type=Path, required=True)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    af = args.af.resolve()
    pins = json.loads((ROOT / "lean/dependencies.json").read_text())
    require(run(["git", "rev-parse", "HEAD"], af).strip() == pins["af_commit"],
            "AF commit mismatch")
    require(run(["git", "rev-parse", "HEAD"], af / ".lake/packages/mathlib").strip()
            == pins["mathlib_commit"], "Mathlib commit mismatch")
    require((af / "lean-toolchain").read_text().strip() == pins["lean_toolchain"],
            "Lean toolchain mismatch")
    checks = {}
    with tempfile.TemporaryDirectory(prefix="przz-polarization-") as directory:
        env = dict(os.environ)
        env["LEAN_PATH"] = directory  # Do not inherit unrelated local oleans.
        for name in ("PRZZInterface", "PRZZCoefficientPolarization"):
            source = ROOT / "lean" / (name + ".lean")
            command = [args.lake, "env", "lean", "--root=" + str(ROOT / "lean"),
                       "-o", str(Path(directory) / (name + ".olean")), str(source)]
            result = subprocess.run(command, cwd=af, env=env, text=True,
                                    capture_output=True, check=False)
            output = result.stdout + result.stderr
            require(result.returncode == 0 and "sorryAx" not in output
                    and "error:" not in output, output)
            # The definitions-only interface and coefficient bridge have
            # no local analytic axiom declarations.
            if name == "PRZZCoefficientPolarization":
                audit_polarization(output)
            checks[name + ".lean"] = {"sha256": sha(source), "exit_code": 0,
                                       "output": output}
    record = {
        "scope": "Fresh two-module local closure; fixed package caches reused",
        "full_project_rebuilt": False,
        "analytic_square_uniformity_proved": False,
        "public_switch_audited_by_this_run": False,
        "scope_note": "Polarization only; public Weil/DI switch audited separately",
        "general_profile_input_removed": True,
        "af_commit": pins["af_commit"], "mathlib_commit": pins["mathlib_commit"],
        "lean_toolchain": pins["lean_toolchain"],
        "runner_sha256": sha(Path(__file__)),
        "audit_runner_sha256": sha(ROOT / "tools/verify_lean.py"),
        "checks": checks,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2, ensure_ascii=False) + "\n")
    print("PASS: fresh two-module closure; 15 standard-only polarization audits")


if __name__ == "__main__":
    main()
