#!/usr/bin/env python3
"""Compile the supplied probes in a separately installed, pinned AF environment.

No fetch, reset or source edit is performed. This is not a clean AF build.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
AF_PATHS = [
    "Zeta23/Analytic/RectangleLogDeriv.lean",
    "Zeta23/XiPrime/Defs.lean",
    "Zeta23/XiPrime/Seam.lean",
    "Zeta23/XiPrime/ZeroCount/ArgBound.lean",
    "Zeta23/XiPrime/ZeroCount/Generic.lean",
    "Zeta23/XiPrime/ZeroCount/GenericRvM.lean",
    "Zeta23/XiPrime/ZeroCount/Contour.lean",
    "Zeta23/XiPrime/ZeroCount.lean",
    "Zeta23/XiPrime/Final.lean",
]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def run(args, cwd):
    proc = subprocess.run(args, cwd=cwd, text=True, capture_output=True, check=False)
    require(proc.returncode == 0, f"Command failed: {args[0]}\n{proc.stdout}\n{proc.stderr}")
    return proc.stdout


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--af", type=Path, required=True, help="Pinned, already-built AF checkout")
    parser.add_argument("--lake", default=shutil.which("lake") or str(Path.home() / ".elan/bin/lake"))
    parser.add_argument("--output", type=Path, help="Optional generated JSON output; otherwise stdout")
    args = parser.parse_args()
    af = args.af.resolve()
    pins = json.loads((ROOT / "lean/dependencies.json").read_text())
    require(run(["git", "rev-parse", "HEAD"], af).strip() == pins["af_commit"], "AF commit mismatch")
    mathlib = af / ".lake/packages/mathlib"
    require(run(["git", "rev-parse", "HEAD"], mathlib).strip() == pins["mathlib_commit"],
            "mathlib commit mismatch")
    require((af / "lean-toolchain").read_text().strip() == pins["lean_toolchain"],
            "Lean toolchain mismatch")
    run(["git", "diff", "--exit-code", pins["af_commit"], "--", *AF_PATHS], af)
    checks = {}
    for name in ("KernelAlgebra.lean", "PRZZInterface.lean", "AFProbe.lean"):
        path = ROOT / "lean" / name
        output = run([args.lake, "env", "lean", str(path)], af)
        require("sorryAx" not in output and "error:" not in output, f"Proof check failed: {name}")
        explicit = sum(line.startswith("axiom ") for line in path.read_text().splitlines())
        require(explicit == (1 if name == "PRZZInterface.lean" else 0),
                f"Unexpected explicit axiom count: {name}")
        # Make captured diagnostics portable; do not disclose workstation paths.
        output = output.replace(str(ROOT), "<package>").replace(str(af), "<af>")
        checks[name] = {"exit_code": 0, "sha256": sha(path), "output": output,
                        "explicit_axiom_declarations": explicit}
        print(f"PASS: {name}", file=sys.stderr, flush=True)
    result = {
        "af_commit": pins["af_commit"], "mathlib_commit": pins["mathlib_commit"],
        "lean_version": run([args.lake, "env", "lean", "--version"], af).strip(),
        "selected_af_sources_match_pin": True,
        "source_sha256": {name: sha(af / name) for name in AF_PATHS},
        "checks": checks, "runner_sha256": sha(Path(__file__)),
        "existing_build_used": True, "clean_upstream_build_performed": False,
        "coefficient_subpower_formal_proof_complete": False,
        "inverse_mellin_analytic_identification_proved": False,
        "przz_external_axiom_count": 1, "final_proportion_formalized": False,
    }
    content = json.dumps(result, indent=2, ensure_ascii=False) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(content)
        print("Saved verification JSON.", file=sys.stderr)
    else:
        print(content, end="")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        sys.exit(1)
