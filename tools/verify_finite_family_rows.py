#!/usr/bin/env python3
"""Verify the exact local closure of the independent-label Weil/DI bridge.

An explicit scratch build directory can reuse previously compiled modules
only when source, direct-dependency fingerprints and olean hashes match.
An optional historical prebuilt directory requires source hashes to match
the recorded 698-module baseline. Conflicting prebuilt oleans are not used:
a fingerprint-verified fresh result supersedes them, or source is rebuilt.
The target is always freshly compiled. No full-project rebuild is claimed.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import re
import subprocess

from verify_lean import (ROOT, audit_diagonal_kernel, audit_finite_family_rows,
                         audit_witness_proportion, audit_witness_basis, audit_profile_uniform, audit_moment_bridge,
                         require, run, sha, audit_standard_module)

TARGET = "PRZZFiniteFamilyRows"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--af", type=Path, required=True)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--build", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--prebuilt", type=Path)
    parser.add_argument("--target", choices=(TARGET, "PRZZDiagonalKernel", "WuProportion",
                                           "PRZZWitnessBasis", "PRZZWitnessMass",
                                           "PRZZProfileSmooth", "PRZZProfileScale", "PRZZPrimitiveKernel",
                                           "PRZZGammaMultiplier", "PRZZKernelComparison", "PRZZFamilyMoment",
                                           "PRZZMellinInterval", "PRZZProfileMellin",
                                           "PRZZClassSources", "PRZZClassVariation", "PRZZClassDI",
                                           "PRZZClassFreeLength", "PRZZClassTypeI", "PRZZClassCases",
                                           "PRZZClassRows", "PRZZMixedLiteral", "PRZZClassLiteral",
                                           "PRZZMixedReplacement", "PRZZMixedDefect", "PRZZMixedPoisson", "PRZZMixedMoment", "PRZZClassPoisson",
                 "PRZZClassWideLiteral", "PRZZClassWidePoisson", "PRZZClassPositiveGrid",
                 "PRZZClassDualProfile", "PRZZClassPairedGrid",
                 "PRZZClassSpatialSources", "PRZZClassSpatialDI", "PRZZClassSpatialTypeI", "PRZZClassSpatialCases", "PRZZClassSpatialRows", "PRZZClassNegativeLiteral", "PRZZClassNegativePoisson", "PRZZClassNegativeGrid", "PRZZClassSignedGrid", "PRZZClassPairedSignedGrid", "PRZZClassZeroBoundary", "PRZZClassZeroTail", "PRZZClassZeroPrimalGap", "PRZZClassZeroCorrection", "PRZZCappedPrefactor", "PRZZCappedTailMass", "PRZZCappedWindowMass", "PRZZCappedWindowTime", "PRZZCappedWindowField", "PRZZCappedFreezeMoment", "PRZZCappedFreezeBudget", "PRZZCappedNativeTail", "PRZZCappedStrictTail", "PRZZCappedBandOuter", "PRZZCappedSameMask", "PRZZCappedTailBand", "PRZZCappedStrictFreeze", "PRZZCappedLarge", "PRZZCappedDiscardedIBP", "PRZZCappedDiscarded", "PRZZCappedFreezeCollector", "PRZZCappedDiscardedFamily", "PRZZCappedRemainder", "PRZZCappedMomentBridge", "PRZZCappedMainTerm", "PRZZCentralGridIdentity", "PRZZBasisGridCutoff", "PRZZBasisGridBound", "PRZZCappedWindowBand", "PRZZCappedSubunitMass", "PRZZCappedBodyMass", "PRZZCappedBodyTail", "PRZZCappedGammaDefect", "PRZZBasisPairedBody", "PRZZFamilyMomentOptimal", "PRZZWitnessBridge"), default=TARGET)
    parser.add_argument("--all-local", action="store_true",
                        help="Also source/fingerprint-check every local module, not just the target closure")
    parser.add_argument("--jobs", type=int, default=4)
    args = parser.parse_args()
    target = args.target
    af = args.af.resolve()
    pins = json.loads((ROOT / "lean/dependencies.json").read_text())
    require(run(["git", "rev-parse", "HEAD"], af).strip() == pins["af_commit"], "AF pin")
    require(run(["git", "rev-parse", "HEAD"], af / ".lake/packages/mathlib").strip()
            == pins["mathlib_commit"], "Mathlib pin")
    require((af / "lean-toolchain").read_text().strip() == pins["lean_toolchain"], "Lean pin")
    args.build.mkdir(parents=True, exist_ok=True)
    local_path = str(args.build.resolve())
    baseline_path = ROOT / "checks/clean-project-verification-2026-11-07.json"
    baseline = json.loads(baseline_path.read_text())["checks"] if args.prebuilt else {}
    if args.prebuilt:
        local_path += os.pathsep + str(args.prebuilt.resolve())
    env = dict(os.environ, LEAN_PATH=local_path)
    sources, dependencies, baseline_compatible = {}, {}, {}

    def visit(name):
        if name in sources:
            return
        source = ROOT / "lean" / (name + ".lean")
        require(source.is_file(), f"Missing source: {source}")
        sources[name] = source
        imports = re.findall(r"^import\s+([A-Za-z0-9_.]+)", source.read_text(), re.MULTILINE)
        dependencies[name] = [n for n in imports if (ROOT / "lean" / (n + ".lean")).is_file()]
        for dependency in dependencies[name]:
            visit(dependency)
        old = baseline.get(name + ".lean")
        baseline_compatible[name] = bool(old and old["sha256"] == sha(source) and
                                        all(baseline_compatible[n] for n in dependencies[name]))

    visit(target)
    if args.all_local:
        for source in sorted((ROOT / "lean").glob("*.lean")):
            visit(source.stem)
    pending = {}
    resolved_prebuilt_conflicts = []
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        def enqueue(name):
            if name in pending:
                return pending[name]
            deps = {n: enqueue(n) for n in dependencies[name]}

            def compile_module():
                rows = {n: future.result() for n, future in deps.items()}
                fingerprint = {n: row["olean_sha256"] for n, row in rows.items()}
                olean = args.build / (name + ".olean")
                cache = args.build / (name + ".json")
                if args.prebuilt and baseline_compatible[name]:
                    old = baseline[name + ".lean"]
                    prior = args.prebuilt / (name + ".olean")
                    require(old["sha256"] == sha(sources[name]), f"Stale baseline: {name}")
                    if prior.is_file() and olean.is_file() and sha(olean) != sha(prior):
                        # Do not silently prefer a conflicting historical cache.
                        # A previously compiled, fingerprint-verified fresh result
                        # may supersede it; otherwise compile the current source.
                        if cache.is_file():
                            verified = json.loads(cache.read_text())
                            if (verified["sha256"] == sha(sources[name]) and
                                    verified["dependency_fingerprints"] == fingerprint and
                                    verified["olean_sha256"] == sha(olean)):
                                resolved_prebuilt_conflicts.append(name)
                                return dict(verified, reused_this_run=True)
                    elif prior.is_file():
                        return dict(old, olean_sha256=sha(prior),
                                    dependency_fingerprints=fingerprint, reused_this_run=True)
                if name != target and cache.is_file() and olean.is_file():
                    old = json.loads(cache.read_text())
                    if (old["sha256"] == sha(sources[name]) and
                            old["dependency_fingerprints"] == fingerprint and
                            old["olean_sha256"] == sha(olean)):
                        return dict(old, reused_this_run=True)
                command = [args.lake, "env", "lean", "--root=" + str(ROOT / "lean"),
                           "-o", str(olean), str(sources[name])]
                result = subprocess.run(command, cwd=af, env=env, text=True,
                                        capture_output=True, check=False)
                output = result.stdout + result.stderr
                require(result.returncode == 0 and "sorryAx" not in output
                        and "error:" not in output, f"{name}:\n{output}")
                row = {"sha256": sha(sources[name]), "exit_code": 0, "output": output,
                       "olean_sha256": sha(olean), "dependency_fingerprints": fingerprint,
                       "reused_this_run": False}
                cache.write_text(json.dumps(row, indent=2) + "\n")
                print(f"PASS {name}", flush=True)
                return row

            pending[name] = pool.submit(compile_module)
            return pending[name]

        enqueue(target).result()
        for name in sources:
            enqueue(name).result()
        checks = {name + ".lean": future.result() for name, future in pending.items()}
    output = checks[target + ".lean"]["output"]
    audit = {"PRZZDiagonalKernel": audit_diagonal_kernel,
             "PRZZFiniteFamilyRows": audit_finite_family_rows,
             "WuProportion": audit_witness_proportion,
             "PRZZWitnessBasis": audit_witness_basis,
             "PRZZWitnessMass": lambda o: audit_witness_basis(o, "PRZZWitnessMass"),
             "PRZZProfileSmooth": audit_profile_uniform,
             "PRZZProfileScale": lambda o: audit_profile_uniform(o, "PRZZProfileScale"),
             **{n: (lambda o, n=n: audit_moment_bridge(o, n)) for n in (
                 "PRZZPrimitiveKernel", "PRZZGammaMultiplier", "PRZZKernelComparison", "PRZZFamilyMoment",
                 "PRZZMellinInterval", "PRZZProfileMellin",
                 "PRZZClassSources", "PRZZClassVariation", "PRZZClassDI",
                 "PRZZClassFreeLength", "PRZZClassTypeI", "PRZZClassCases", "PRZZClassRows",
                 "PRZZMixedLiteral", "PRZZClassLiteral", "PRZZMixedReplacement", "PRZZMixedDefect", "PRZZMixedPoisson", "PRZZMixedMoment", "PRZZClassPoisson",
                 "PRZZClassWideLiteral", "PRZZClassWidePoisson", "PRZZClassPositiveGrid",
                 "PRZZClassDualProfile", "PRZZClassPairedGrid",
                 "PRZZClassSpatialSources", "PRZZClassSpatialDI", "PRZZClassSpatialTypeI", "PRZZClassSpatialCases", "PRZZClassSpatialRows", "PRZZClassNegativeLiteral", "PRZZClassNegativePoisson", "PRZZClassNegativeGrid", "PRZZClassSignedGrid", "PRZZClassPairedSignedGrid", "PRZZClassZeroBoundary", "PRZZClassZeroTail", "PRZZClassZeroPrimalGap", "PRZZClassZeroCorrection", "PRZZCappedPrefactor", "PRZZCappedTailMass", "PRZZCappedWindowMass", "PRZZCappedWindowTime", "PRZZCappedWindowField", "PRZZCappedFreezeMoment", "PRZZCappedFreezeBudget", "PRZZCappedNativeTail", "PRZZCappedStrictTail", "PRZZCappedBandOuter", "PRZZCappedSameMask", "PRZZCappedTailBand", "PRZZCappedStrictFreeze", "PRZZCappedLarge", "PRZZCappedDiscardedIBP", "PRZZCappedDiscarded", "PRZZCappedFreezeCollector", "PRZZCappedDiscardedFamily", "PRZZCappedRemainder", "PRZZCappedMomentBridge", "PRZZCappedMainTerm", "PRZZCentralGridIdentity", "PRZZBasisGridCutoff", "PRZZBasisGridBound", "PRZZCappedWindowBand", "PRZZCappedSubunitMass", "PRZZCappedBodyMass", "PRZZCappedBodyTail", "PRZZCappedGammaDefect", "PRZZBasisPairedBody", "PRZZFamilyMomentOptimal", "PRZZWitnessBridge")}}[target]
    audit(output)
    names = re.findall(r"^#print axioms (\w+)$", sources[target].read_text(), re.MULTILINE)
    audits = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output)
    namespace = "XiPrime8845." + ("PRZZZeroGammaBound" if target == "PRZZGammaMultiplier" else target) + "."
    require(len(audits) == len(names) and {n for n, _ in audits} ==
            {namespace + n for n in names}, "Target audit coverage")
    for name, axioms in audits:
        allowed = {"propext", "Classical.choice", "Quot.sound"}
        require({a.strip() for a in axioms.split(",")} <= allowed, f"Target axioms: {name}")
    # Check every emitted audit, not merely the target: no analytic axiom
    # may hide in an intermediate module. Include empty axiom lists.
    for name, row in checks.items():
        source = (ROOT / "lean" / name).read_text()
        audit_standard_module(source, row["output"], name)
    if target == "WuProportion":
        for premise in ("WeilIncomplete", "DeshouillersIwaniecLemma1"):
            require(premise in output, f"Missing printed headline hypothesis: {premise}")
    record = {"scope": ("All local sources" if args.all_local else "Exact local closure") +
              "; source/dependency/artifact-checked local and pinned external caches reused",
              "full_project_rebuilt": args.all_local and all(not row["reused_this_run"] for row in checks.values()),
              "all_local_sources_checked": args.all_local,
              "no_local_axiom_declarations": True,
              "lean_version": run([args.lake, "env", "lean", "--version"], af).strip(),
              "headline_hypotheses": ["WeilIncomplete", "DeshouillersIwaniecLemma1"] if target == "WuProportion" else None,
              "target": target,
              "af_commit": pins["af_commit"], "mathlib_commit": pins["mathlib_commit"],
              "lean_toolchain": pins["lean_toolchain"], "runner_sha256": sha(Path(__file__)),
              "audit_runner_sha256": sha(ROOT / "tools/verify_lean.py"),
              "historical_baseline_sha256": sha(baseline_path) if args.prebuilt else None,
              "fresh_module_count": sum(not row["reused_this_run"] for row in checks.values()),
              "prebuilt_conflicts_resolved_by_verified_fresh_cache": sorted(resolved_prebuilt_conflicts),
              "module_count": len(checks), "checks": checks}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2) + "\n")
    print(f"PASS: {len(checks)} local closure modules, {len(audits)} target axiom audits")


if __name__ == "__main__":
    try:
        main()
    except ValueError as error:
        raise SystemExit(str(error))
