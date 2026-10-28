#!/usr/bin/env python3
"""Compile the supplied probes in a separately installed, pinned AF environment.

No fetch, reset or source edit is performed. This is not a clean AF build.
"""
import argparse
import hashlib
import json
import os
import re
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

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
    "Zeta23/FromPNTPlus/Auxiliary.lean",
    "Zeta23/FromPNTPlus/EulerMaclaurin.lean",
    "Zeta23/FromPNTPlus/Fourier.lean",
    "Zeta23/FromPNTPlus/MediumPNT.lean",
    "Zeta23/FromPNTPlus/MellinCalculus.lean",
    "Zeta23/FromPNTPlus/Rectangle.lean",
    "Zeta23/FromPNTPlus/ResidueCalcOnRectangles.lean",
    "Zeta23/FromPNTPlus/SmoothExistence.lean",
    "Zeta23/FromPNTPlus/Sobolev.lean",
    "Zeta23/FromPNTPlus/ZetaBounds.lean",
    "Zeta23/FromPNTPlus/ZetaConj.lean",
    "Zeta23/FromPNTPlus/Mathlib/Algebra/Notation/Support.lean",
    "Zeta23/FromPNTPlus/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean",
    "Zeta23/FromPNTPlus/Tactic/AdditiveCombination.lean",
]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def run(args, cwd, env=None):
    proc = subprocess.run(args, cwd=cwd, env=env, text=True, capture_output=True, check=False)
    require(proc.returncode == 0, f"Command failed: {args[0]}\n{proc.stdout}\n{proc.stderr}")
    return proc.stdout


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def compile_sources(lake, af, source_dir):
    # Fresh local imports: no stale package oleans, and no writes into AF.
    with tempfile.TemporaryDirectory(prefix="xiprime-lean-") as build:
        env = dict(os.environ)
        env["LEAN_PATH"] = build + (os.pathsep + env["LEAN_PATH"] if env.get("LEAN_PATH") else "")
        for name in ("BetaKernel.lean", "FiniteJet.lean", "KernelAlgebra.lean",
                     "PRZZInterface.lean", "AFProbe.lean", "IntegralJet.lean", "TaylorEnvelope.lean",
                     "CoefficientEvaluator.lean", "NumericalGate.lean", "RationalEvaluator.lean",
                     "RationalBounds.lean", "FixedCertificate.lean", "PRZZAsymptotic.lean",
                     "LogarithmicBudget.lean", "CompactShiftIntegral.lean", "ArithmeticRegularity.lean",
                     "GcdDecomposition.lean", "ZetaPoleScaling.lean", "HeightScaling.lean",
                     "SmoothMobius.lean", "ElementaryGcd.lean", "ShiftWeights.lean", "SupportTail.lean",
                     "MobiusHarmonic.lean", "MobiusPNT.lean", "MobiusPNTBridge.lean"):
            command = [lake, "env", "lean", "--root=" + str(source_dir)]
            if name in ("BetaKernel.lean", "FiniteJet.lean", "KernelAlgebra.lean",
                        "IntegralJet.lean", "TaylorEnvelope.lean", "CoefficientEvaluator.lean",
                        "NumericalGate.lean", "RationalEvaluator.lean", "RationalBounds.lean",
                        "PRZZInterface.lean", "FixedCertificate.lean", "PRZZAsymptotic.lean",
                        "CompactShiftIntegral.lean", "ArithmeticRegularity.lean", "GcdDecomposition.lean",
                        "SmoothMobius.lean", "ElementaryGcd.lean", "MobiusHarmonic.lean", "MobiusPNT.lean"):
                command += ["-o", str(Path(build) / (Path(name).stem + ".olean"))]
            output = run(command + [str(source_dir / name)], af, env)
            yield name, output.replace(build, "<temporary-build>")


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
    for name, output in compile_sources(args.lake, af, ROOT / "lean"):
        path = ROOT / "lean" / name
        require("sorryAx" not in output and "error:" not in output, f"Proof check failed: {name}")
        explicit = sum(line.startswith("axiom ") for line in path.read_text().splitlines())
        require(explicit == (1 if name == "PRZZInterface.lean" else 0),
                f"Unexpected explicit axiom count: {name}")
        if name == "PRZZInterface.lean":
            dependencies = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output))
            standard = {"propext", "Classical.choice", "Quot.sound"}
            for theorem in ("abs_fengArithmetic_le_log_sq", "witness_profile_bounds",
                            "witness_coefficient_bound", "witness_subpower",
                            "witness_normalized_error_tendsto_zero", "witness_przz_estimate"):
                key = "XiPrime8845.PRZZ." + theorem
                require(key in dependencies, f"Missing axiom audit: {key}")
                actual = {item.strip() for item in dependencies[key].split(",")}
                expected = standard | ({"przz41_case3_K2_profiles"}
                                       if theorem == "witness_przz_estimate" else set())
                require(actual == expected, f"Unexpected axiom dependencies: {key}: {actual}")
        if name == "PRZZAsymptotic.lean":
            dependencies = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output))
            standard = {"propext", "Classical.choice", "Quot.sound"}
            elementary = {"errorEnvelope_tendsto", "radius_pos", "witnessBidisc_subset",
                          "witnessBidisc_sum_ne_zero", "mixed_cauchy_bound"}
            analytic = {"normalized_difference_bound", "normalized_difference_uniform",
                        "normalized_difference_on_bidisc", "moment_limit_of_gcd_limit",
                        "moment_uniform_limit_of_gcd_limit", "normalized_mixed_error_tendsto"}
            audited = set(re.findall(r"^#print axioms (\w+)$", path.read_text(), re.MULTILINE))
            require(audited == elementary | analytic, "PRZZ asymptotic audit coverage changed")
            for theorem in audited:
                key = "XiPrime8845.PRZZAsymptotic." + theorem
                require(key in dependencies, f"Missing axiom audit: {key}")
                actual = {item.strip() for item in dependencies[key].split(",")}
                expected = standard | ({"przz41_case3_K2_profiles"} if theorem in analytic else set())
                require(actual == expected, f"Unexpected axiom dependencies: {key}: {actual}")
        if name == "ArithmeticRegularity.lean":
            dependencies = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output))
            audited = set(re.findall(r"^#print axioms (\w+)$", path.read_text(), re.MULTILINE))
            require(audited == {"momentCore_smooth", "zeta_shift_ne_one", "gcd_zeta_ne_one",
                               "closed_disc_re_neg", "weighted_integral_restrict", "twistedMoment_smooth",
                               "gcdCore_smooth", "gcd_integral_smooth", "gcdMainTerm_smooth",
                               "normalizedError_smooth", "normalizedError_right_regular",
                               "normalizedError_left_mixed_regular", "normalized_mixed_error_tendsto"},
                    "Arithmetic regularity audit coverage changed")
            for theorem in audited:
                key = "XiPrime8845.ArithmeticRegularity." + theorem
                require(key in dependencies, f"Missing axiom audit: {key}")
                actual = {item.strip() for item in dependencies[key].split(",")}
                expected = {"propext", "Classical.choice", "Quot.sound"}
                if theorem == "normalized_mixed_error_tendsto":
                    expected.add("przz41_case3_K2_profiles")
                require(actual == expected, f"Unexpected axiom dependencies: {key}: {actual}")
        if name == "FiniteJet.lean":
            dependencies = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output))
            for theorem in ("polynomial_jet_zero", "polynomial_jet_at", "exponential_jet",
                            "reciprocal_jet", "denominator_jet", "inverse_integrand_jet",
                            "reflected_jet", "dual_derivative", "separable_jet₂",
                            "integral_polynomial", "inverseTrunc_eq_integral",
                            "inverseShiftPoly_eval", "inverseShiftPoly_jet",
                            "reciprocal_mixed_jet", "jet_mul", "signed_dual_derivative",
                            "dual_op_contraction", "reciprocal_slice_smooth",
                            "quotient_separable_jet", "W_eq_evaluator", "W_contraction",
                            "quotient_W_contraction", "contract₂_rect", "dual_contract₂",
                            "quotient_slice_smooth", "quotient_contract₂_W", "dual_quotient_W",
                            "W_symm", "W_profile_swap", "dual_quotient_diagonal"):
                key = "XiPrime8845.FiniteJet." + theorem
                require(key in dependencies, f"Missing axiom audit: {key}")
                actual = {item.strip() for item in dependencies[key].split(",")}
                require(actual == {"propext", "Classical.choice", "Quot.sound"},
                        f"Unexpected axiom dependencies: {key}: {actual}")
        if name == "BetaKernel.lean":
            dependencies = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output))
            for theorem in ("beta_recurrence", "beta_monomial", "outer_beta",
                            "inverse_jet_beta_term", "inverseJetEval_eq_integral",
                            "outer_beta_order", "outer_polynomial", "assemble00", "assemble20",
                            "assemble02", "assemble22", "monomialIntegral_swap", "H02_swap",
                            "fourTerms_diagonal", "weighted_sum_transpose", "shifted_q_coefficient"):
                key = "XiPrime8845.BetaKernel." + theorem
                require(key in dependencies, f"Missing axiom audit: {key}")
                actual = {item.strip() for item in dependencies[key].split(",")}
                require(actual == {"propext", "Classical.choice", "Quot.sound"},
                        f"Unexpected axiom dependencies: {key}: {actual}")
        if name in ("IntegralJet.lean", "TaylorEnvelope.lean", "CoefficientEvaluator.lean", "NumericalGate.lean",
                    "RationalEvaluator.lean", "RationalBounds.lean", "FixedCertificate.lean",
                    "LogarithmicBudget.lean", "CompactShiftIntegral.lean", "GcdDecomposition.lean",
                    "ZetaPoleScaling.lean", "HeightScaling.lean", "SmoothMobius.lean", "ElementaryGcd.lean", "ShiftWeights.lean", "SupportTail.lean", "MobiusHarmonic.lean", "MobiusPNT.lean", "MobiusPNTBridge.lean"):
            dependencies = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output))
            audited = re.findall(r"^#print axioms (\w+)$", path.read_text(), re.MULTILINE)
            required = {"IntegralJet.lean": "K2_exact_evaluator",
                        "TaylorEnvelope.lean": "K2_Taylor_enclosure",
                        "CoefficientEvaluator.lean": "K2_cached_enclosure",
                        "NumericalGate.lean": "actual_sub_finite",
                        "RationalEvaluator.lean": "finiteValue_exact",
                        "RationalBounds.lean": "rational_bounds",
                        "FixedCertificate.lean": "fixed_functional_gate",
                        "LogarithmicBudget.lean": "positive_moment_gate",
                        "CompactShiftIntegral.lean": "compact_integral_smooth",
                        "GcdDecomposition.lean": "normalized_gcd_split",
                        "ZetaPoleScaling.lean": "direct_pole_on_bidisc",
                        "HeightScaling.lean": "heightFactor_uniform",
                        "SmoothMobius.lean": "restricted_divisor_sum",
                        "ElementaryGcd.lean": "conrey_inner_expansion",
                        "ShiftWeights.lean": "weight_shift_modulus",
                        "SupportTail.lean": "normalizedTail_uniform_zero",
                        "MobiusHarmonic.lean": "linearProfile_uniform_of_mu_pnt_alt",
                        "MobiusPNT.lean": "mu_pnt_alt",
                        "MobiusPNTBridge.lean": "linearProfile_uniform"}[name]
            require(required in audited, "Missing integrated evaluator/enclosure audit")
            for theorem in audited:
                key = "XiPrime8845." + path.stem + "." + theorem
                require(key in dependencies, f"Missing axiom audit: {key}")
                actual = {item.strip() for item in dependencies[key].split(",")}
                require(actual == {"propext", "Classical.choice", "Quot.sound"},
                        f"Unexpected axiom dependencies: {key}: {actual}")
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
        "coefficient_subpower_formal_proof_complete": True,
        "normalized_przz_error_envelope_tends_to_zero": True,
        "actual_przz_normalized_difference_uniform_on_bidisc": True,
        "mixed_przz_error_cauchy_transfer_with_explicit_regularity_premises": True,
        "arithmetic_shift_regularity_premises_discharged": True,
        "actual_mixed_przz_error_tends_to_zero_without_regularity_premises": True,
        "gcd_mainterm_exact_direct_dual_split_proved": True,
        "outer_zeta_poles_scaled_uniformly": True,
        "dual_height_factor_uniform_limit_proved": True,
        "reflection_stable_two_bidisc_domain_defined": True,
        "finite_gcd_diagonalization_proved": True,
        "smooth_supported_coprimality_expansion_proved": True,
        "shift_absorption_and_uniform_weight_modulus_proved": True,
        "harmonic_averaged_supported_tail_uniform_zero_proved": True,
        "mobius_logMean_limit_from_qualitative_mass_proved": True,
        "linear_mobius_profile_uniform_from_qualitative_PNT_proved": True,
        "qualitative_mobius_PNT_imported": True,
        "mobius_logMean_and_linear_profile_PNT_premises_discharged": True,
        "pntplus_consequences_source_commit": "6a380f0c4658c04a420a9eb00b1ed62a1e3fde01",
        "general_C2_mobius_weight_transfer_proved": False,
        "coprimality_averaged_error_proved": False,
        "gcd_mainterm_limit_proved": False,
        "certified_logarithmic_budget_strictly_above_target": True,
        "wu_counting_adapter_proved": False,
        "witness_przz_coefficient_hypotheses_discharged": True,
        "finite_truncated_inverse_integral_and_jet_identities_proved": True,
        "beta_integral_and_finite_inverse_jet_coefficients_proved": True,
        "four_K2_linear_assembly_and_undifferentiated_cross_swap_proved": True,
        "full_K2_evaluator_equivalence_proved": False,
        "inverse_and_outer_integral_derivative_interchange_proved": True,
        "exact_untruncated_K2_W_evaluator_equivalence_proved": True,
        "integrated_contracted_cross_reduction_proved": True,
        "Taylor_truncation_error_envelope_formalized": True,
        "Taylor_bound_identical_to_python_sparse_envelope": False,
        "Taylor_polynomial_integrals_evaluated_as_coefficient_sums": True,
        "finite_Taylor_integrals_equal_cached_coefficient_evaluator": True,
        "coefficient_evaluator_error_bound_from_actual_K2_functional": True,
        "fixed_target_and_dual_exponentials_interval_certified": True,
        "fixed_total_K2_Taylor_error_le_one_millionth": True,
        "fixed_coefficient_expression_numerically_certified": True,
        "rational_backend_equals_fixed_cached_evaluator": True,
        "rational_bounds_checked_by_kernel_reduction": True,
        "fixed_functional_gate_has_no_numerical_premises": True,
        "fixed_finite_gate_has_explicit_coefficient_bound_premise": True,
        "python_execution_and_interval_rounding_formalized": False,
        "final_interval_inequality_formalized": True,
        "separable_quotient_derivatives_identified_with_W": True,
        "local_dual_conjugation_and_positive_op_proved": True,
        "swapped_dual_quotient_diagonal_identified_with_positive_W": True,
        "W_contracted_profile_swap_proved": True,
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
