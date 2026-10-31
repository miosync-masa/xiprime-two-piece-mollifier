#!/usr/bin/env python3
"""Compile the supplied probes in a separately installed, pinned AF environment.

No fetch, reset or source edit is performed. This is not a clean AF build.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
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
    "Zeta23/Defs.lean",
    "Zeta23/Assembly.lean",
    "Zeta23/Defs/Counting.lean",
    "Zeta23/Hypotheses.lean",
    "Zeta23/Chebyshev.lean",
    "Zeta23/FromPNTPlus/Mertens.lean",
    "Zeta23/XiPrime/Coeff/Basic.lean",
    "Zeta23/XiPrime/Coeff/Abel.lean",
    "Zeta23/XiPrime/Coeff/PowerSums.lean",
    "Zeta23/XiPrime/Coeff/NonSquarefree.lean",
    "Zeta23/XiPrime/Coeff/PrimeSums.lean",
    "Zeta23/Analytic/RectangleLogDeriv.lean",
    "Zeta23/XiPrime/Defs.lean",
    "Zeta23/XiPrime/Seam.lean",
    "Zeta23/GammaFacts/StirlingVert.lean",
    "Zeta23/Analytic/Stirling.lean",
    "Zeta23/XiPrime/ZeroCount/ArgBound.lean",
    "Zeta23/RvM/ZetaGrowth.lean",
    "Zeta23/WeilEF/Landau.lean",
    "Zeta23/XiPrime/ZeroCount/Basic.lean",
    "Zeta23/XiPrime/ZeroCount/Landau.lean",
    "Zeta23/XiPrime/ZeroCount/Y.lean",
    "Zeta23/XiPrime/ExplicitFormula/ZeroFree.lean",
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


def compile_sources(lake, af, source_dir, jobs=1):
    # Fresh local imports: no stale package oleans, and no writes into AF.
    with tempfile.TemporaryDirectory(prefix="xiprime-lean-") as build, ThreadPoolExecutor(max_workers=jobs) as pool:
        env = dict(os.environ)
        env["LEAN_PATH"] = build + (os.pathsep + env["LEAN_PATH"] if env.get("LEAN_PATH") else "")
        pending = {}
        ordered = []

        def enqueue(name, command):
            imports = re.findall(r"^import\s+([A-Za-z0-9_.]+)",
                                 (source_dir / name).read_text(), re.MULTILINE)
            local = [module for module in imports if (source_dir / (module + ".lean")).is_file()]
            require(all(module in pending for module in local), f"Non-topological module order: {name}")
            dependencies = [pending[module] for module in local]

            def compile_after_dependencies():
                for dependency in dependencies:
                    dependency.result()
                return run(command + [str(source_dir / name)], af, env)

            future = pool.submit(compile_after_dependencies)
            pending[Path(name).stem] = future
            ordered.append((name, future))
        for name in ("BetaKernel.lean", "FiniteJet.lean", "KernelAlgebra.lean",
                     "PRZZInterface.lean", "SmoothWeightWitness.lean", "AFProbe.lean", "IntegralJet.lean", "TaylorEnvelope.lean",
                     "CoefficientEvaluator.lean", "NumericalGate.lean", "RationalEvaluator.lean",
                     "RationalBounds.lean", "FixedCertificate.lean", "PRZZAsymptotic.lean",
                     "LogarithmicBudget.lean", "CompactShiftIntegral.lean", "ArithmeticRegularity.lean",
                     "GcdDecomposition.lean", "ZetaPoleScaling.lean", "HeightScaling.lean",
                     "SmoothMobius.lean", "ElementaryGcd.lean", "ShiftWeights.lean", "SupportTail.lean",
                     "MobiusHarmonic.lean", "MobiusPNT.lean", "MobiusPNTBridge.lean", "WeightedMobius.lean", "WeightDerivatives.lean", "ShiftedMobius.lean", "CoprimeShift.lean", "SupportProductTail.lean",
                     "ShiftedEndpoint.lean", "CoprimeHead.lean", "CoprimeApproximation.lean",
                     "TotientWeight.lean", "EndpointAverage.lean",
                     "MultiplicativeSummability.lean", "TotientConvolution.lean", "TotientSummability.lean",
                     "TotientHarmonic.lean", "TotientAbel.lean", "ShiftedTotient.lean",
                     "ShiftedEulerLocal.lean", "ShiftedEulerUniform.lean",
                     "LogProfileSum.lean", "OuterProfile.lean", "EulerHead.lean", "CoprimeEulerCompletion.lean",
                     "BareEuler.lean", "BareEulerUniform.lean", "CoprimeEndpoint.lean",
                     "CoprimeGluing.lean", "ConreyOuter.lean", "ConreyCoefficientBridge.lean", "ConreyMainTerm.lean",
                     "FengArithmetic.lean", "FengCoefficientBridge.lean", "FengShift.lean",
                     "FengAtG.lean", "FengLogBounds.lean", "FengLogEndpoint.lean", "FengPrimeCancellation.lean",
                     "FengOutside.lean", "FengPrimeMass.lean", "FengOutsideBounds.lean", "FengOutsideEndpoint.lean",
                     "FengShared.lean", "FengSharedBlock.lean", "FengResidual.lean", "FengSharedApproximation.lean",
                     "FengSharedBounds.lean", "FengSharedEndpoint.lean", "FengSharedTail.lean",
                     "FengSharedInterior.lean", "FengMarkedProfile.lean",
                     "FengMarkedAbel.lean", "FengMarkedLimit.lean",
                     "TotientCoprime.lean", "FengMarkedArithmetic.lean", "FengMarkedDecomposition.lean",
                     "FengMarkedTail.lean", "FengMertensModels.lean", "FengMarkedDiagonal.lean", "FengMarkedCross.lean", "FengMarkedCrossLimit.lean",
                     "FengMixedMoment.lean", "FengSharedLimit.lean",
                     "FengMixedAbel.lean", "FengMixedLimit.lean",
                     "FengMixedInterior.lean", "FengMixedProduct.lean", "FengMixedShift.lean",
                     "FengLogMainTerm.lean", "FengOutsideProfile.lean", "FengCrossAssembly.lean",
                     "FengPrimeProfile.lean", "FengPrimeExclusion.lean", "FengOutsidePrime.lean",
                     "CoprimeEulerError.lean", "FengPrimeWindow.lean", "FengOutsideAverage.lean", "FengOutsideReplacement.lean",
                     "FengInverseProfile.lean", "CoprimeSingleGluing.lean", "FengOutsideProxy.lean", "FengOutsideMainTerm.lean", "FengCrossCoefficient.lean", "FengMixedMainTerm.lean",
                     "FengLogProducts.lean", "FengSquareAssembly.lean",
                     "FengOutsidePartner.lean", "FengInverseProducts.lean", "FengOutsideSquare.lean", "FengOutsideShared.lean", "RawEuler.lean", "FengSharedShift.lean", "FengSquareCoefficient.lean", "FengSquareMainTerm.lean", "TwoPieceMainTerm.lean", "CauchyJetTransfer.lean", "TwoPieceMoment.lean", "ZetaMomentIntegral.lean", "ZetaMomentPolynomial.lean", "ZetaMomentMainTerm.lean", "WitnessMomentBound.lean", "WuAuxiliary.lean", "WuStirling.lean", "WuGammaJets.lean", "WuStirlingTransfer.lean", "WuStirlingMoment.lean", "WuMomentTransfer.lean"):
            command = [lake, "env", "lean", "--root=" + str(source_dir)]
            if name in ("BetaKernel.lean", "FiniteJet.lean", "KernelAlgebra.lean",
                        "IntegralJet.lean", "TaylorEnvelope.lean", "CoefficientEvaluator.lean",
                        "NumericalGate.lean", "RationalEvaluator.lean", "RationalBounds.lean",
                        "PRZZInterface.lean", "SmoothWeightWitness.lean", "FixedCertificate.lean", "PRZZAsymptotic.lean", "LogarithmicBudget.lean",
                        "CompactShiftIntegral.lean", "ArithmeticRegularity.lean", "GcdDecomposition.lean",
                        "SmoothMobius.lean", "ElementaryGcd.lean", "MobiusHarmonic.lean", "MobiusPNT.lean", "MobiusPNTBridge.lean",
                        "ShiftWeights.lean", "WeightedMobius.lean", "WeightDerivatives.lean",
                        "ShiftedMobius.lean", "SupportTail.lean", "CoprimeShift.lean", "SupportProductTail.lean",
                        "ShiftedEndpoint.lean", "CoprimeHead.lean", "CoprimeApproximation.lean",
                        "TotientWeight.lean", "MultiplicativeSummability.lean", "TotientConvolution.lean",
                        "TotientSummability.lean", "TotientHarmonic.lean", "ShiftedTotient.lean",
                        "ShiftedEulerLocal.lean", "ShiftedEulerUniform.lean", "TotientAbel.lean",
                        "LogProfileSum.lean", "OuterProfile.lean", "EulerHead.lean", "CoprimeEulerCompletion.lean",
                        "EndpointAverage.lean", "BareEuler.lean", "BareEulerUniform.lean",
                        "CoprimeEndpoint.lean", "CoprimeGluing.lean", "ConreyOuter.lean",
                        "ConreyCoefficientBridge.lean", "ZetaPoleScaling.lean", "HeightScaling.lean",
                        "FengArithmetic.lean", "FengShift.lean", "FengAtG.lean", "FengLogBounds.lean",
                        "ConreyMainTerm.lean", "FengCoefficientBridge.lean", "FengLogEndpoint.lean", "FengOutside.lean", "FengPrimeMass.lean", "FengOutsideBounds.lean",
                        "FengPrimeCancellation.lean", "FengShared.lean", "FengSharedBlock.lean",
                        "FengResidual.lean", "FengSharedBounds.lean", "FengSharedApproximation.lean",
                        "FengSharedTail.lean", "FengSharedInterior.lean",
                        "FengMarkedProfile.lean", "FengMarkedAbel.lean",
                        "TotientCoprime.lean", "FengMarkedArithmetic.lean", "FengMarkedDecomposition.lean",
                        "FengMarkedLimit.lean", "FengMarkedTail.lean", "FengMertensModels.lean",
                        "FengMarkedDiagonal.lean", "FengMarkedCross.lean", "FengMarkedCrossLimit.lean",
                        "FengMixedMoment.lean", "FengMixedAbel.lean", "FengMixedLimit.lean",
                        "FengSharedLimit.lean", "FengMixedInterior.lean", "FengMixedProduct.lean",
                        "FengMixedShift.lean", "FengLogMainTerm.lean", "FengOutsideProfile.lean", "FengCrossAssembly.lean",
                        "FengPrimeProfile.lean", "FengPrimeExclusion.lean", "FengOutsidePrime.lean",
                        "CoprimeEulerError.lean", "FengPrimeWindow.lean", "FengOutsideAverage.lean", "FengOutsideReplacement.lean",
                     "FengInverseProfile.lean", "CoprimeSingleGluing.lean", "FengOutsideProxy.lean", "FengOutsideMainTerm.lean", "FengCrossCoefficient.lean", "FengMixedMainTerm.lean",
                     "FengLogProducts.lean", "FengSquareAssembly.lean",
                     "FengOutsidePartner.lean", "FengInverseProducts.lean", "FengOutsideSquare.lean", "FengOutsideShared.lean", "RawEuler.lean", "FengSharedShift.lean", "FengSquareCoefficient.lean", "FengSquareMainTerm.lean", "TwoPieceMainTerm.lean", "CauchyJetTransfer.lean", "TwoPieceMoment.lean", "ZetaMomentIntegral.lean", "ZetaMomentPolynomial.lean", "ZetaMomentMainTerm.lean", "WitnessMomentBound.lean", "WuAuxiliary.lean", "WuStirling.lean", "WuGammaJets.lean", "WuStirlingTransfer.lean", "WuStirlingMoment.lean", "WuMomentTransfer.lean"):
                command += ["-o", str(Path(build) / (Path(name).stem + ".olean"))]
            enqueue(name, command)
        name = "SmoothWeightMoment.lean"
        enqueue(name, [lake, "env", "lean", "--root=" + str(source_dir)])
        for name in ("SmoothWindow.lean", "SmoothWindowLimit.lean", "WuUnsmoothing.lean",
                     "PRZZLocalization.lean", "PRZZLocalizedError.lean", "SmoothEndpoint.lean", "WuEndpointTransfer.lean",
                     "ExpandedGcd.lean", "ExpandedHeight.lean", "ExpandedRegularity.lean",
                     "ExpandedMainTerm.lean", "ExpandedZetaIntegral.lean", "ExpandedZetaPolynomial.lean",
                     "ExpandedMoment.lean", "WuLocalizedMoments.lean", "WuTrimmedLog.lean", "WuWindowTiling.lean",
                     "WuLittlewood.lean", "WuEdgeLog.lean", "WuSafeEndpoints.lean",
                     "WuIndependentWindows.lean", "WuSubintervalLog.lean",
                     "WuXiBands.lean", "WuAuxiliaryBoundary.lean",
                     "WuBoundaryZeros.lean", "WuAuxiliaryMultiplicity.lean", "WuLeftReturn.lean",
                     "WuRightMollifier.lean", "WuRightBoundary.lean", "WuRightLittlewood.lean",
                     "WuWideGamma.lean", "WuDiskGrowth.lean", "WuDiskCenter.lean",
                     "WuHorizontalIntegral.lean", "WuHorizontalBound.lean", "WuCriticalMultiplicity.lean",
                     "WuAuxiliaryHorizontal.lean", "WuFiniteDeflation.lean", "WuCriticalDeflation.lean",
                     "WuDeflatedDetection.lean", "WuPhaseCrossings.lean", "WuDeflatedContour.lean",
                     "WuBoundaryPhase.lean", "WuParallelReturn.lean", "WuContourCounting.lean",
                     "WuGammaPhase.lean", "WuGammaCancellation.lean", "WuVHorizontal.lean",
                     "WuEtaMainPhase.lean", "WuQuotientReturn.lean", "WuLocalCounting.lean",
                     "WuDyadicCounting.lean", "WuTotalAsymptotic.lean", "WuProportion.lean"):
            enqueue(name, [lake, "env", "lean", "--root=" + str(source_dir),
                           "-o", str(Path(build) / (Path(name).stem + ".olean"))])
        for name, future in ordered:
            yield name, future.result().replace(build, "<temporary-build>")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--af", type=Path, required=True, help="Pinned, already-built AF checkout")
    parser.add_argument("--lake", default=shutil.which("lake") or str(Path.home() / ".elan/bin/lake"))
    parser.add_argument("--output", type=Path, help="Optional generated JSON output; otherwise stdout")
    parser.add_argument("--jobs", type=int, default=1, help="Concurrent Lean processes (dependencies are awaited)")
    args = parser.parse_args()
    require(args.jobs >= 1, "--jobs must be positive")
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
    for name, output in compile_sources(args.lake, af, ROOT / "lean", args.jobs):
        path = ROOT / "lean" / name
        require("sorryAx" not in output and "error:" not in output, f"Proof check failed: {name}")
        explicit = sum(line.startswith("axiom ") for line in path.read_text().splitlines())
        require(explicit == (1 if name == "PRZZInterface.lean" else 0),
                f"Unexpected explicit axiom count: {name}")
        if name in {"WuXiBands.lean", "WuAuxiliaryBoundary.lean", "WuBoundaryZeros.lean",
                    "WuAuxiliaryMultiplicity.lean", "WuLeftReturn.lean", "WuRightMollifier.lean",
                    "WuRightBoundary.lean", "WuRightLittlewood.lean", "WuWideGamma.lean",
                    "WuDiskGrowth.lean", "WuDiskCenter.lean", "WuHorizontalIntegral.lean",
                    "WuHorizontalBound.lean", "WuCriticalMultiplicity.lean", "WuAuxiliaryHorizontal.lean",
                    "WuFiniteDeflation.lean", "WuCriticalDeflation.lean", "WuDeflatedDetection.lean",
                    "WuPhaseCrossings.lean", "WuDeflatedContour.lean", "WuBoundaryPhase.lean",
                    "WuParallelReturn.lean", "WuContourCounting.lean", "WuGammaPhase.lean",
                    "WuGammaCancellation.lean", "WuVHorizontal.lean", "WuEtaMainPhase.lean",
                    "WuQuotientReturn.lean", "WuLocalCounting.lean", "WuDyadicCounting.lean",
                    "WuTotalAsymptotic.lean", "WuProportion.lean"}:
            dependencies = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output))
            audited = set(re.findall(r"^#print axioms ([\w.]+)$", path.read_text(), re.MULTILINE))
            expected_audits = {
                "WuXiBands.lean": {"total_mono", "good_mono", "total_increment", "good_increment",
                    "unit_count", "unit_increment_uniform", "inward_counting_transfer", "global_bound"},
                "WuAuxiliaryBoundary.lean": {"auxiliary_entire", "eta_reflection_difference",
                    "eta_not_identically_zero", "auxiliary_factor", "log_auxiliary", "log_auxiliary_left",
                    "log_auxiliary_left_le", "H_left_eventually_nonzero", "left_log_integral_le",
                    "left_log_eventually_le"},
                "WuBoundaryZeros.lean": {"coefficient_one", "dirichletPolynomial_tendsto",
                    "psi_tendsto_right", "psi_not_identically_zero", "auxiliary_not_identically_zero",
                    "entire_zeros_countable", "auxiliary_zeros_countable", "safe_window_log_input",
                    "vertical_log_integrable", "auxiliary_left_ae_nonzero", "left_log_integral_le",
                    "left_log_eventually_le"},
                "WuAuxiliaryMultiplicity.lean": {"entire_order_ne_top", "auxiliary_order",
                    "eta_order_le_auxiliary", "oddPart_eq", "oddPart_order", "weighted_eta_le_auxiliary",
                    "exists_safe_sides", "littlewood_perturbed"},
                "WuLeftReturn.lean": {"integral_eventually_lt_of_upper_bound", "vertical_ae_nonzero",
                    "vertical_log_eventually_lt", "auxiliary_left_return", "exists_safe_left",
                    "littlewood_fixed_right", "weighted_sum_mono", "safe_left_budget_eventually"},
                "WuRightMollifier.lean": {"coefficient_tendsto", "shift_tendsto", "shiftedCoefficient_tendsto",
                    "shiftedCoefficient_bound", "error_term_bound", "errorMass_tendsto", "psi_eq_LSeries",
                    "inverse_error_bound", "zeta_psi_uniform", "LSeries_bound", "psi_bound"},
                "WuRightBoundary.lean": {"zeta_derivative_bound", "scaled_bound", "scaled_succ_bound",
                    "U_sub_zeta_bound", "V_sub_zeta_bound", "product_uniform", "right_nonzero",
                    "rightLog_uniform", "right_analytic", "right_real_pos", "rightLog_integrable",
                    "rightLog_integral_bound", "normalized_rightLog_tendsto", "right_phase_bound"},
                "WuRightLittlewood.lean": {"littlewood_eventually", "eta_count_le_weighted", "eta_count_le_boundary"},
                "WuWideGamma.lean": {"jetConstant_nonneg", "jet_bound"},
                "WuDiskGrowth.lean": {"zeta_halfPlane_bound", "center_derivative_bound", "disk_derivative_bound",
                    "V_disk_bound", "psi_polynomial_bound", "product_disk_bound"},
                "WuDiskCenter.lean": {"V_sub_zeta_bound", "product_uniform", "center_lower"},
                "WuHorizontalIntegral.lean": {"horizontal_of_partial_fraction"},
                "WuHorizontalBound.lean": {"product_analytic", "horizontal_bound", "phaseConstant_pos", "horizontal_safe"},
                "WuCriticalMultiplicity.lean": {"eta_conj", "realtype_order", "reflected_order",
                    "eta_order_le_xiDeriv", "critical_zero_budget"},
                "WuAuxiliaryHorizontal.lean": {"logDeriv_factor", "logDeriv_integrable", "auxiliary_horizontal_safe"},
                "WuFiniteDeflation.lean": {"divisor_order", "single_factor", "finite_factor", "order_restore"},
                "WuCriticalDeflation.lean": {"exists_data", "Data.divisor_critical", "Data.curve_nonzero",
                    "Data.xi_order_restore", "Data.count_restore", "Data.edgeLog"},
                "WuDeflatedDetection.lean": {"Data.realDivisor_ne_zero", "Data.curve_im", "Data.remaining_re",
                    "Data.curve_im_zero_iff", "Data.phase_zero_iff"},
                "WuPhaseCrossings.lean": {"phase_count", "positive_order_at_zero", "phase_count_restored",
                    "critical_phase_count"},
                "WuDeflatedContour.lean": {"divisor_logDeriv", "eta_logDeriv", "detour_integral",
                    "vertical_pole_bound", "vertical_comparison"},
                "WuBoundaryPhase.lean": {"edge_increment", "boundary_horizontal_error", "boundaryLog_le",
                    "auxiliary_boundaryLog_le"},
                "WuParallelReturn.lean": {"nonzero_strip", "vertical_continuousAt", "parallel_phase_count"},
                "WuContourCounting.lean": {"rectangle_phase", "argument_count", "phase_littlewood",
                    "original_eta_phase_supplier", "actual_window_merger", "eventual_window_merger"},
                "WuGammaPhase.lean": {"rectangle_regular", "otherPhase_eq", "boundary_zero",
                    "vertical_main_bound", "otherPhase_main_bound"},
                "WuGammaCancellation.lean": {"quotient_boundary", "auxiliary_cancellation",
                    "gamma_free_boundary_bound"},
                "WuVHorizontal.lean": {"V_analytic", "horizontal_bound", "phaseConstant_pos",
                    "right_real_pos", "right_phase_bound"},
                "WuEtaMainPhase.lean": {"eta_path_split", "otherPhase_split", "otherPhase_main",
                    "gamma_free_merger"},
                "WuQuotientReturn.lean": {"Hlog_continuous", "logDensity_integrable", "quotient_log_ae",
                    "quotient_integral_eq", "logIntegral_return", "exists_safe_left", "original_budget"},
                "WuLocalCounting.lean": {"divide_positive_budget", "closed_count_lower"},
                "WuDyadicCounting.lean": {"proportion_gt", "closed_sum_le_dyadic", "countLower_eq",
                    "budget_le", "budget_eventually_le", "budget_normalized_tendsto"},
                "WuTotalAsymptotic.lean": {"rvm", "total_growth", "dyadic_normalized", "N0_add", "cumulative"},
                "WuProportion.lean": {"dyadic_eventually", "cumulative_eventually", "strict_proportion",
                    "ratio_eventually_gt"},
            }
            require(audited == expected_audits[name], f"Actual counting bridge audit coverage changed: {name}")
            for theorem in audited:
                namespace = "WuCriticalDeflation" if name == "WuDeflatedDetection.lean" else path.stem
                key = "XiPrime8845." + namespace + "." + theorem
                require(key in dependencies, f"Missing actual counting bridge audit: {key}")
                expected = {"propext", "Classical.choice", "Quot.sound"}
                if theorem in {"left_log_eventually_le", "safe_window_log_input", "safe_left_budget_eventually",
                               "original_budget", "closed_count_lower", "budget_eventually_le",
                               "dyadic_eventually", "cumulative_eventually", "strict_proportion", "ratio_eventually_gt"}:
                    expected.add("PRZZ.przz41_case3_K2_profiles")
                actual = {item.strip() for item in dependencies[key].split(",")}
                require(actual == expected, f"Unexpected actual counting bridge dependencies: {key}: {actual}")
            require("LocalizedEstimate" not in path.read_text(), f"Localization leaked into counting bridge: {name}")
        if name in {"WuIndependentWindows.lean", "WuSubintervalLog.lean"}:
            dependencies = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output))
            audited = set(re.findall(r"^#print axioms (\w+)$", path.read_text(), re.MULTILINE))
            expected_audits = {
                "WuIndependentWindows.lean": {"exists_inward_heights", "exists_independent_heights",
                    "counting_transfer", "unit_band_transfer", "aggregate_independent", "number_cells_bound",
                    "band_budget_bound", "band_budget_normalized_tendsto", "global_independent_bound"},
                "WuSubintervalLog.lean": {"jensen_of_integral", "integral_density_subinterval",
                    "subLogMean_le", "subLogMean_eventually_le", "safe_window_log_input"},
            }
            require(audited == expected_audits[name], f"Independent-window audit coverage changed: {name}")
            for theorem in audited:
                key = "XiPrime8845." + path.stem + "." + theorem
                require(key in dependencies, f"Missing independent-window audit: {key}")
                actual = {item.strip() for item in dependencies[key].split(",")}
                expected = {"propext", "Classical.choice", "Quot.sound"}
                if theorem in {"subLogMean_eventually_le", "safe_window_log_input"}:
                    expected.add("PRZZ.przz41_case3_K2_profiles")
                require(actual == expected, f"Unexpected independent-window dependencies: {key}: {actual}")
            require("LocalizedEstimate" not in path.read_text(), f"Localization leaked into independent route: {name}")
        if name in {"WuLittlewood.lean", "WuEdgeLog.lean", "WuSafeEndpoints.lean"}:
            dependencies = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output))
            audited = set(re.findall(r"^#print axioms ([\w.]+)$", path.read_text(), re.MULTILINE))
            expected_audits = {
                "WuLittlewood.lean": {"EdgeLog.real_eq", "EdgeLog.parts", "contour_boundary", "littlewood"},
                "WuEdgeLog.lean": {"path_log_exists", "edgeLog_exists", "boundaryLogs_exists", "littlewood_of_boundary_nonzero"},
                "WuSafeEndpoints.lean": {"badTerminals_countable", "exists_safe_terminal", "badHeights_countable",
                    "horizontal_nonzero", "boundary_nonzero", "exists_safe_geometric_family",
                    "littlewood_of_safe_heights", "moving_endpoint_zero"},
            }
            require(audited == expected_audits[name], f"Littlewood audit coverage changed: {name}")
            namespace = "WuSafeEndpoints" if name == "WuSafeEndpoints.lean" else "WuLittlewood"
            for theorem in audited:
                key = "XiPrime8845." + namespace + "." + theorem
                require(key in dependencies, f"Missing Littlewood audit: {key}")
                actual = {item.strip() for item in dependencies[key].split(",")}
                require(actual == {"propext", "Classical.choice", "Quot.sound"},
                        f"Unexpected Littlewood dependencies: {key}: {actual}")
        if name in {"WuTrimmedLog.lean", "WuWindowTiling.lean"}:
            dependencies = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output))
            audited = set(re.findall(r"^#print axioms (\w+)$", path.read_text(), re.MULTILINE))
            expected_audits = {
                "WuTrimmedLog.lean": {"density_continuous", "integral_density", "log_tangent",
                    "logMean_le", "logMean_eventually_le"},
                "WuWindowTiling.lean": {"ratio_mem", "boundary_antitone", "height_le", "exists_cut",
                    "endpoints", "cell_eq", "cells_disjoint", "cells_union", "increments_telescope",
                    "lengths_telescope", "sum_error_bound", "sum_error_of_local", "all_window_log_inputs",
                    "aggregate_counting", "global_counting_bound"},
            }
            require(audited == expected_audits[name], f"Interior-window audit coverage changed: {name}")
            for theorem in audited:
                key = "XiPrime8845." + path.stem + "." + theorem
                require(key in dependencies, f"Missing interior-window audit: {key}")
                actual = {item.strip() for item in dependencies[key].split(",")}
                expected = {"propext", "Classical.choice", "Quot.sound"}
                if theorem in {"logMean_eventually_le", "all_window_log_inputs"}:
                    expected.add("PRZZ.przz41_case3_K2_profiles")
                require(actual == expected, f"Unexpected interior-window dependencies: {key}: {actual}")
            require("LocalizedEstimate" not in path.read_text(), f"Localization leaked into interior route: {name}")
        if name in {"PRZZLocalization.lean", "PRZZLocalizedError.lean", "SmoothEndpoint.lean", "WuEndpointTransfer.lean",
                    "ExpandedGcd.lean", "ExpandedHeight.lean", "ExpandedRegularity.lean", "ExpandedMainTerm.lean",
                    "ExpandedZetaIntegral.lean", "ExpandedZetaPolynomial.lean", "ExpandedMoment.lean", "WuLocalizedMoments.lean"}:
            dependencies = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output))
            audited = set(re.findall(r"^#print axioms (\w+)$", path.read_text(), re.MULTILINE))
            expected_audits = {
                "ExpandedGcd.lean": {"weighted_integral_restrict", "integrated_term", "gcdMainTerm_split", "normalized_gcd_split"},
                "ExpandedHeight.lean": {"log_height_bound", "phase_error_bound", "rescale_integral", "mass_full", "heightFactor_uniform"},
                "ExpandedRegularity.lean": {"twistedMoment_smooth"},
                "ExpandedMainTerm.lean": {"weightMass_full", "normalized_gcd_uniform_of_arithmetic", "normalized_gcd_uniform",
                    "normalized_witness_uniform", "normalizedMoment_uniform"},
                "ExpandedZetaIntegral.lean": {"integral_left_deriv", "integral_right_deriv", "integral_zero", "integral_eq_full", "twistedMoment_mixed_deriv"},
                "ExpandedZetaPolynomial.lean": {"moment_expansion", "normalized_jet₂", "contract₂_eq_moment"},
                "ExpandedMoment.lean": {"normalizedMoment_uniform", "normalizedMoment_tendsto", "normalizedMoment_regular",
                    "kernel_regular", "limit_regular", "normalizedMoment_jet₂_tendsto", "normalizedMoment_contract_tendsto",
                    "normalizedMoment_exactEvaluator_tendsto"},
                "WuLocalizedMoments.lean": {"normalizedMoment_contract_eq", "moment_exactEvaluator_tendsto", "squareMoment_exactEvaluator_tendsto",
                    "smoothedMoment_tendsto", "derivativeMoments_bounded", "localizedUMoments", "majorantDerivativeBounds",
                    "endpointTight", "fullMoment_tendsto", "fullMoment_eventually_lt"},
                "PRZZLocalization.lean": {"old_weight_iff", "compact_support", "integrable",
                    "fullMass_eq", "scaled_support", "weighted_integrable"},
                "PRZZLocalizedError.lean": {"normalized_difference_bound", "normalized_difference_uniform",
                    "normalized_difference_on_bidisc", "moment_uniform_limit_of_gcd_limit"},
                "SmoothEndpoint.lean": {"cap_mass", "weight_smooth", "weight_mass",
                    "endpoint_majorant", "fullCap_smooth", "fullCap_one"},
                "WuEndpointTransfer.lean": {"broad_u_integrable", "broad_derivative_integrable",
                    "full_error_integrable", "fullError_bound", "fullError_tendsto", "endpoint_bound",
                    "endpointTight_of_localizedMoments", "fullMoment_tendsto_of_localizedMoments"},
            }
            require(audited == expected_audits[name], f"Localization audit coverage changed: {name}")
            for theorem in audited:
                key = "XiPrime8845." + path.stem + "." + theorem
                require(key in dependencies, f"Missing localization audit: {key}")
                actual = {item.strip() for item in dependencies[key].split(",")}
                expected = {"propext", "Classical.choice", "Quot.sound"}
                if theorem == "fullMoment_tendsto_of_localizedMoments" or (name == "WuLocalizedMoments.lean" and theorem in {"fullMoment_tendsto", "fullMoment_eventually_lt"}):
                    expected.add("PRZZ.przz41_case3_K2_profiles")
                require(actual == expected, f"Unexpected localization dependencies: {key}: {actual}")
        if name in {"SmoothWindow.lean", "SmoothWindowLimit.lean", "WuUnsmoothing.lean"}:
            dependencies = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output))
            audited = set(re.findall(r"^#print axioms (\w+)$", path.read_text(), re.MULTILINE))
            expected_audits = {
                "SmoothWindow.lean": {"bump_smooth", "bump_one", "bump_zero", "bump_mass", "integral_sandwich"},
                "SmoothWindowLimit.lean": {"window_integrable", "windowMoment_tendsto"},
                "WuUnsmoothing.lean": {"trimmedMoment_eq", "fullMoment_eq", "weighted_integrable",
                    "trimmed_integrable", "trimmedMoment_tendsto", "trimmedMean_tendsto",
                    "trimmed_counting_bound", "width_budget", "trimmed_budget_bound", "iterated_width_limit", "sequential_unsmoothing",
                    "full_integrable", "full_split", "fullMoment_tendsto_of_endpointTight"},
            }
            require(audited == expected_audits[name], f"Unsmoothing audit coverage changed: {name}")
            analytic = {"trimmedMoment_tendsto", "trimmedMean_tendsto", "trimmed_counting_bound",
                        "trimmed_budget_bound", "iterated_width_limit", "sequential_unsmoothing", "fullMoment_tendsto_of_endpointTight"}
            for theorem in audited:
                key = "XiPrime8845." + path.stem + "." + theorem
                require(key in dependencies, f"Missing unsmoothing audit: {key}")
                actual = {item.strip() for item in dependencies[key].split(",")}
                expected = {"propext", "Classical.choice", "Quot.sound"}
                if name == "WuUnsmoothing.lean" and theorem in analytic:
                    expected.add("PRZZ.przz41_case3_K2_profiles")
                require(actual == expected, f"Unexpected unsmoothing dependencies: {key}: {actual}")
        if name == "SmoothWeightMoment.lean":
            dependencies = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output))
            audited = set(re.findall(r"^#print axioms (\w+)$", path.read_text(), re.MULTILINE))
            require(audited == {"plateau_mass_pos", "plateau_u_moment_bound", "plateau_v_moment_bound"},
                    "Concrete moment audit coverage changed")
            for theorem in audited:
                key = "XiPrime8845.SmoothWeightMoment." + theorem
                require(key in dependencies, f"Missing axiom audit: {key}")
                actual = {item.strip() for item in dependencies[key].split(",")}
                expected = {"propext", "Classical.choice", "Quot.sound"}
                if theorem != "plateau_mass_pos":
                    expected.add("PRZZ.przz41_case3_K2_profiles")
                require(actual == expected, f"Unexpected concrete moment dependencies: {key}: {actual}")
        if name == "SmoothWeightWitness.lean":
            dependencies = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output))
            audited = set(re.findall(r"^#print axioms (\w+)$", path.read_text(), re.MULTILINE))
            require({"plateau_smooth", "plateau_mass_bounds", "positive_mass_witness"} <= audited,
                    "Missing nonvacuity audit")
            for theorem in audited:
                key = "XiPrime8845.SmoothWeightWitness." + theorem
                require(key in dependencies, f"Missing axiom audit: {key}")
                actual = {item.strip() for item in dependencies[key].split(",")}
                require(actual == {"propext", "Classical.choice", "Quot.sound"},
                        f"Nonvacuity must not depend on PRZZ: {key}: {actual}")
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


        if name == "WuMomentTransfer.lean":
            dependencies = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output))
            audited = set(re.findall(r"^#print axioms (\w+)$", path.read_text(), re.MULTILINE))
            elementary = {"square_difference", "weighted_square_difference", "u_integrable",
                          "v_integrable", "vMoment_nonneg", "moment_difference_bound"}
            analytic = {"moment_difference_rate", "moment_difference_tendsto", "vMoment_tendsto",
                        "normalizedVMoment_tendsto", "normalizedVMoment_eventually_lt",
                        "v_moment_bound", "unit_mass_vMoment_bound"}
            require(audited == elementary | analytic, "Wu moment transfer audit coverage changed")
            for theorem in audited:
                key = "XiPrime8845.WuMomentTransfer." + theorem
                require(key in dependencies, f"Missing axiom audit: {key}")
                actual = {item.strip() for item in dependencies[key].split(",")}
                expected = {"propext", "Classical.choice", "Quot.sound"}
                if theorem in analytic:
                    expected.add("PRZZ.przz41_case3_K2_profiles")
                require(actual == expected, f"Unexpected axiom dependencies: {key}: {actual}")
        if name in ("WuStirling.lean", "WuGammaJets.lean", "WuStirlingTransfer.lean", "WuStirlingMoment.lean"):
            coverage = {
                "WuStirling.lean": {"H_ne_zero", "H_analytic", "H_deriv", "H_logDeriv", "xi_eq",
                    "xi_leibniz", "V_expansion", "digamma_sub_log", "log_half_bound",
                    "firstConstant_pos", "Lfn_stirling_bound", "jet_one_bound"},
                "WuGammaJets.lean": {"H_iterated_analytic", "jet_analytic", "jet_recurrence",
                    "disc_strip", "jetConstant_nonneg", "jet_bound"},
                "WuStirlingTransfer.lean": {"U_expansion", "difference_expansion", "transferConstant_nonneg",
                    "difference_bound", "leftPoint_strip", "difference_left_bound"},
                "WuStirlingMoment.lean": {"weight_support", "weighted_integrable", "derivative_integrable",
                    "error_integrable", "square_error_bound", "errorMoment_bound",
                    "errorMoment_rate", "errorMoment_tendsto"},
            }
            dependencies = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output))
            audited = set(re.findall(r"^#print axioms (\w+)$", path.read_text(), re.MULTILINE))
            require(audited == coverage[name], "Wu Stirling audit coverage changed")
            for theorem in audited:
                key = "XiPrime8845." + Path(name).stem + "." + theorem
                require(key in dependencies, f"Missing axiom audit: {key}")
                actual = {item.strip() for item in dependencies[key].split(",")}
                expected = {"propext", "Classical.choice", "Quot.sound"}
                if name == "WuStirlingMoment.lean" and theorem in {"errorMoment_rate", "errorMoment_tendsto"}:
                    expected.add("PRZZ.przz41_case3_K2_profiles")
                require(actual == expected, f"Unexpected axiom dependencies: {key}: {actual}")
        if name == "WuAuxiliary.lean":
            dependencies = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output))
            audited = set(re.findall(r"^#print axioms (\w+)$", path.read_text(), re.MULTILINE))
            elementary = {"translated_polynomial", "operator_polynomial", "r_at_half",
                          "linear_coefficient_pos", "xi_derivative_conj", "xi_derivative_one_sub",
                          "xi_derivative_critical", "xi_even_im", "xi_odd_re", "eta_entire",
                          "eta_im", "eta_im_zero_iff", "psi_entire", "psi_left",
                          "smoothedMoment_eq", "single_operator", "derivativeMoment_eq"}
            analytic = {"smoothedMoment_tendsto", "smoothedMoment_bound", "derivativeMoments_bounded"}
            require(audited == elementary | analytic, "Wu auxiliary audit coverage changed")
            for theorem in audited:
                key = "XiPrime8845.WuAuxiliary." + theorem
                require(key in dependencies, f"Missing axiom audit: {key}")
                actual = {item.strip() for item in dependencies[key].split(",")}
                expected = {"propext", "Classical.choice", "Quot.sound"}
                if theorem in analytic:
                    expected.add("PRZZ.przz41_case3_K2_profiles")
                require(actual == expected, f"Unexpected axiom dependencies: {key}: {actual}")
        if name == "WitnessMomentBound.lean":
            dependencies = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output))
            audited = set(re.findall(r"^#print axioms (\w+)$", path.read_text(), re.MULTILINE))
            elementary = {"qReal_cast", "profiles_match", "radius_match", "evaluator_eq_actual",
                          "weightMass_eq", "mass_nonneg", "witnessMoment_nonneg",
                          "countingCap_lt_target", "countingCap_budget"}
            analytic = {"witnessMoment_tendsto", "witnessMoment_eventually_lt",
                        "normalizedMoment_tendsto", "normalizedMoment_eventually_lt",
                        "witness_moment_bound", "unit_mass_moment_bound"}
            require(audited == elementary | analytic, "Witness moment audit coverage changed")
            for theorem in audited:
                key = "XiPrime8845.WitnessMomentBound." + theorem
                require(key in dependencies, f"Missing axiom audit: {key}")
                actual = {item.strip() for item in dependencies[key].split(",")}
                expected = {"propext", "Classical.choice", "Quot.sound"}
                if theorem in analytic:
                    expected.add("PRZZ.przz41_case3_K2_profiles")
                require(actual == expected, f"Unexpected axiom dependencies: {key}: {actual}")
        if name == "ZetaMomentMainTerm.lean":
            dependencies = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output))
            audited = set(re.findall(r"^#print axioms (\w+)$", path.read_text(), re.MULTILINE))
            analytic = {"moment_exactEvaluator_tendsto", "squareMoment_exactEvaluator_tendsto"}
            require(audited == analytic | {"normalizedMoment_contract_eq"},
                    "Zeta derivative moment audit coverage changed")
            for theorem in audited:
                key = "XiPrime8845.ZetaMomentMainTerm." + theorem
                require(key in dependencies, f"Missing axiom audit: {key}")
                actual = {item.strip() for item in dependencies[key].split(",")}
                expected = {"propext", "Classical.choice", "Quot.sound"}
                if theorem in analytic:
                    expected.add("PRZZ.przz41_case3_K2_profiles")
                require(actual == expected, f"Unexpected axiom dependencies: {key}: {actual}")
        if name == "TwoPieceMoment.lean":
            dependencies = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output))
            audited = set(re.findall(r"^#print axioms (\w+)$", path.read_text(), re.MULTILINE))
            elementary = {"normalizedMoment_regular", "kernel_regular", "limit_regular"}
            analytic = {"normalizedMoment_uniform", "normalizedMoment_tendsto",
                        "normalizedMoment_jet₂_tendsto", "normalizedMoment_contract_tendsto",
                        "normalizedMoment_exactEvaluator_tendsto"}
            require(audited == elementary | analytic, "Two-piece moment audit coverage changed")
            for theorem in audited:
                key = "XiPrime8845.TwoPieceMoment." + theorem
                require(key in dependencies, f"Missing axiom audit: {key}")
                actual = {item.strip() for item in dependencies[key].split(",")}
                expected = {"propext", "Classical.choice", "Quot.sound"}
                if theorem in analytic:
                    expected.add("PRZZ.przz41_case3_K2_profiles")
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
                    "ZetaPoleScaling.lean", "HeightScaling.lean", "SmoothMobius.lean", "ElementaryGcd.lean", "ShiftWeights.lean", "SupportTail.lean", "MobiusHarmonic.lean", "MobiusPNT.lean", "MobiusPNTBridge.lean", "WeightedMobius.lean", "WeightDerivatives.lean", "ShiftedMobius.lean", "CoprimeShift.lean", "SupportProductTail.lean",
                     "ShiftedEndpoint.lean", "CoprimeHead.lean", "CoprimeApproximation.lean",
                     "TotientWeight.lean", "EndpointAverage.lean",
                     "MultiplicativeSummability.lean", "TotientConvolution.lean", "TotientSummability.lean",
                     "TotientHarmonic.lean", "TotientAbel.lean", "ShiftedTotient.lean",
                     "ShiftedEulerLocal.lean", "ShiftedEulerUniform.lean",
                     "LogProfileSum.lean", "OuterProfile.lean", "EulerHead.lean", "CoprimeEulerCompletion.lean",
                     "BareEuler.lean", "BareEulerUniform.lean", "CoprimeEndpoint.lean",
                     "CoprimeGluing.lean", "ConreyOuter.lean", "ConreyCoefficientBridge.lean", "ConreyMainTerm.lean",
                     "FengArithmetic.lean", "FengCoefficientBridge.lean", "FengShift.lean",
                     "FengAtG.lean", "FengLogBounds.lean", "FengLogEndpoint.lean", "FengPrimeCancellation.lean",
                     "FengOutside.lean", "FengPrimeMass.lean", "FengOutsideBounds.lean", "FengOutsideEndpoint.lean",
                     "FengShared.lean", "FengSharedBlock.lean", "FengResidual.lean", "FengSharedApproximation.lean",
                     "FengSharedBounds.lean", "FengSharedEndpoint.lean", "FengSharedTail.lean",
                     "FengSharedInterior.lean", "FengMarkedProfile.lean",
                     "FengMarkedAbel.lean", "FengMarkedLimit.lean",
                     "TotientCoprime.lean", "FengMarkedArithmetic.lean", "FengMarkedDecomposition.lean",
                     "FengMarkedTail.lean", "FengMertensModels.lean", "FengMarkedDiagonal.lean", "FengMarkedCross.lean", "FengMarkedCrossLimit.lean",
                     "FengMixedMoment.lean", "FengSharedLimit.lean",
                     "FengMixedAbel.lean", "FengMixedLimit.lean",
                     "FengMixedInterior.lean", "FengMixedProduct.lean", "FengMixedShift.lean",
                     "FengLogMainTerm.lean", "FengOutsideProfile.lean", "FengCrossAssembly.lean",
                     "FengPrimeProfile.lean", "FengPrimeExclusion.lean", "FengOutsidePrime.lean",
                     "CoprimeEulerError.lean", "FengPrimeWindow.lean", "FengOutsideAverage.lean", "FengOutsideReplacement.lean",
                     "FengInverseProfile.lean", "CoprimeSingleGluing.lean", "FengOutsideProxy.lean", "FengOutsideMainTerm.lean", "FengCrossCoefficient.lean", "FengMixedMainTerm.lean",
                     "FengLogProducts.lean", "FengSquareAssembly.lean",
                     "FengOutsidePartner.lean", "FengInverseProducts.lean", "FengOutsideSquare.lean", "FengOutsideShared.lean", "RawEuler.lean", "FengSharedShift.lean", "FengSquareCoefficient.lean", "FengSquareMainTerm.lean", "TwoPieceMainTerm.lean", "CauchyJetTransfer.lean", "ZetaMomentIntegral.lean", "ZetaMomentPolynomial.lean"):
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
                        "MobiusPNTBridge.lean": "linearProfile_uniform",
                        "WeightedMobius.lean": "weighted_family_uniform",
                        "WeightDerivatives.lean": "second_bound",
                        "ShiftedMobius.lean": "shifted_jet_reflected",
                        "CoprimeShift.lean": "scaled_coprime_expansion",
                        "SupportProductTail.lean": "product_error_average",
                        "ShiftedEndpoint.lean": "coprime_second_moment",
                        "CoprimeHead.lean": "finite_head_eventually",
                        "CoprimeApproximation.lean": "coprime_product_error_eventually",
                        "TotientWeight.lean": "zero_shift_weight",
                        "EndpointAverage.lean": "actual_log_endpoint_bound",
                        "MultiplicativeSummability.lean": "summable_of_local_mass",
                        "TotientConvolution.lean": "harmonic_representation",
                        "TotientSummability.lean": "correction_mass_one",
                        "TotientHarmonic.lean": "summatory_log_bound",
                        "TotientAbel.lean": "weighted_error_bound",
                        "ShiftedTotient.lean": "outerWeight_product",
                        "ShiftedEulerLocal.lean": "prime_defect_bound",
                        "ShiftedEulerUniform.lean": "averageError_twoBidiscs_uniform",
                        "LogProfileSum.lean": "shifted_family_uniform",
                        "OuterProfile.lean": "modelSum_twoBidiscs",
                        "EulerHead.lean": "full_tail_product",
                        "CoprimeEulerCompletion.lean": "actual_product_average_uniform",
                        "BareEuler.lean": "ratio_bound",
                        "BareEulerUniform.lean": "weighted_Euler_error_uniform",
                        "CoprimeEndpoint.lean": "endpoint_small",
                        "CoprimeGluing.lean": "averageError_uniform",
                        "ConreyOuter.lean": "actualSum_twoBidiscs",
                        "ConreyCoefficientBridge.lean": "scaledArithmetic_eq_actualSum",
                        "ConreyMainTerm.lean": "normalized_gcdMainTerm_uniform",
                        "FengArithmetic.lean": "weighted_feng_expansion",
                        "FengCoefficientBridge.lean": "gcdMainTerm_four",
                        "FengShift.lean": "shifted_feng_derivative",
                        "FengAtG.lean": "fengBlock_decomposition",
                        "FengLogBounds.lean": "logBlock_twoBidiscs",
                        "FengLogEndpoint.lean": "logBlock_product_endpoint_twoBidiscs",
                        "FengPrimeCancellation.lean": "shared_local_at_gn",
                        "FengOutside.lean": "outside_error_average",
                        "FengPrimeMass.lean": "scaled_mass_bound",
                        "FengOutsideBounds.lean": "outsideBlock_twoBidiscs",
                        "FengOutsideEndpoint.lean": "outside_product_endpoint_twoBidiscs",
                        "FengShared.lean": "shared_eq_prime_residues",
                        "FengSharedBlock.lean": "sharedBlock_residual",
                        "FengResidual.lean": "sharedBlock_coprimeScaled",
                        "FengSharedApproximation.lean": "sharedBlock_main_error",
                        "FengSharedBounds.lean": "sharedBlock_twoBidiscs",
                        "FengSharedEndpoint.lean": "product_endpoint_twoBidiscs",
                        "FengSharedTail.lean": "shared_head_uniform",
                        "FengSharedInterior.lean": "averageRemainder_twoBidiscs",
                        "FengMarkedProfile.lean": "main_sum_profile",
                        "FengMarkedAbel.lean": "weighted_error_bound",
                        "FengMarkedLimit.lean": "marked_profile_twoBidiscs",
                        "TotientCoprime.lean": "two_prime_exclusion_log",
                        "FengMarkedArithmetic.lean": "crossAt_reindex",
                        "FengMarkedDecomposition.lean": "summatory_decomposition",
                        "FengMarkedTail.lean": "higherPowers_normalized",
                        "FengMertensModels.lean": "model_total_limit",
                        "FengMarkedDiagonal.lean": "diagonal_limit",
                        "FengMarkedCross.lean": "cross_point_error",
                        "FengMarkedCrossLimit.lean": "marked_scalar_asymptotic",
                        "FengMixedMoment.lean": "mixed_scalar_limit",
                        "FengSharedLimit.lean": "actualSum_twoBidiscs",
                        "FengMixedAbel.lean": "weighted_error_bound",
                        "FengMixedLimit.lean": "mixed_profile_twoBidiscs",
                        "FengMixedInterior.lean": "averageRemainder_twoBidiscs",
                        "FengMixedProduct.lean": "actualSum_twoBidiscs",
                        "FengMixedShift.lean": "actualSum_twoBidiscs",
                        "FengLogMainTerm.lean": "actualSum_twoBidiscs",
                        "FengOutsideProfile.lean": "convolution_inverse",
                        "FengCrossAssembly.lean": "fullSum_twoBidiscs_of_outside",
                        "FengPrimeProfile.lean": "profileTransform_uniform",
                        "FengPrimeExclusion.lean": "excluded_mass_scaled",
                        "FengOutsidePrime.lean": "mainProxy_twoBidiscs",
                        "CoprimeEulerError.lean": "innerError_average",
                        "FengPrimeWindow.lean": "endpoint_mass",
                        "FengOutsideAverage.lean": "averageError_twoBidiscs",
                        "FengOutsideReplacement.lean": "outside_sub_proxy_twoBidiscs",
                        "FengInverseProfile.lean": "zero_profile_uniform",
                        "CoprimeSingleGluing.lean": "average_uniform",
                        "FengOutsideProxy.lean": "zeroModel_sub_profile_uniform",
                        "FengOutsideMainTerm.lean": "outsideAsymptotic",
                        "FengCrossCoefficient.lean": "scaledArithmetic20_twoBidiscs",
                        "FengMixedMainTerm.lean": "normalized_cross_uniform",
                        "FengLogProducts.lean": "logarithmicSum_twoBidiscs",
                        "FengSquareAssembly.lean": "fullSum_twoBidiscs_of_remaining",
                        "FengOutsidePartner.lean": "outside_outside_sub_proxy",
                        "FengInverseProducts.lean": "inverse_mixed_twoBidiscs",
                        "FengOutsideSquare.lean": "outside_outside_twoBidiscs",
                        "FengOutsideShared.lean": "outside_shared_twoBidiscs",
                        "RawEuler.lean": "rawWeight_factor",
                        "FengSharedShift.lean": "fullSum_twoBidiscs",
                        "FengSquareCoefficient.lean": "scaledArithmetic22_twoBidiscs",
                        "FengSquareMainTerm.lean": "normalized_gcd22_uniform",
                        "TwoPieceMainTerm.lean": "normalized_witness_uniform",
                        "CauchyJetTransfer.lean": "jet₂_tendsto",
                        "ZetaMomentIntegral.lean": "twistedMoment_mixed_deriv",
                        "ZetaMomentPolynomial.lean": "contract₂_eq_moment"}[name]
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
        "parallel_jobs": args.jobs,
        "smoothWeight_explicit_C_infinity_not_analytic": True,
        "positive_mass_smooth_plateau_without_PRZZ": True,
        "concrete_positive_mass_U_and_V_moment_bounds_from_PRZZ": True,
        "fixed_inner_window_unweighted_V_moment_limit": True,
        "iterated_limit_height_before_endpoint_width": True,
        "full_dyadic_V_moment_limit_requires_endpoint_tightness": True,
        "endpoint_tightness_discharged": False,
        "expanded_support_gcd_and_height_limits_proved": True,
        "expanded_support_exact_zeta_derivative_jet_identity": True,
        "localized_estimate_to_U_and_derivative_moment_suppliers": True,
        "endpoint_tightness_from_explicit_LocalizedEstimate": True,
        "full_dyadic_V_moment_limit_and_cap_from_LocalizedEstimate": True,
        "localized_PRZZ_estimate_proved": False,
        "localized_PRZZ_is_added_axiom": False,
        "abstract_rectangle_Littlewood_proved": True,
        "compatible_edge_logarithms_constructed": True,
        "fixed_countable_family_geometric_endpoint_avoidance": True,
        "independent_inward_safe_endpoints_proved": True,
        "unit_band_counting_transfer_proved": True,
        "conditional_total_band_budget_normalized_tends_to_zero": True,
        "unit_trimmed_subinterval_log_cap_uniform": True,
        "actual_xi_prime_unit_band_count_bound_proved": True,
        "actual_xi_prime_cumulative_multiplicity_count_adapters": True,
        "actual_xi_prime_global_transfer_requires_local_counting_gate": True,
        "actual_eta_psi_left_log_bound_given_nonvanishing": True,
        "actual_eta_not_identically_zero_proved": True,
        "actual_Wu_horizontal_argument_bound_proved": True,
        "actual_eta_psi_horizontal_bound_uniform_on_safe_subsegments": True,
        "critical_eta_analytic_order_bounded_by_xi_prime": True,
        "actual_eta_critical_divisor_removed_with_analytic_extension": True,
        "deflated_curve_continuous_log_constructed": True,
        "deflated_phase_to_full_xi_prime_multiplicity_count_proved": True,
        "original_eta_phase_indentation_comparison_proved": False,
        "phase_to_xi_prime_multiplicity_count_proved": True,
        "moving_Wu_family_bad_terminal_countability_proved": False,
        "actual_Wu_vertical_boundary_nonvanishing_proved": False,
        "coefficient_subpower_formal_proof_complete": True,
        "normalized_przz_error_envelope_tends_to_zero": True,
        "actual_przz_normalized_difference_uniform_on_bidisc": True,
        "mixed_przz_error_cauchy_transfer_with_explicit_regularity_premises": True,
        "arithmetic_shift_regularity_premises_discharged": True,
        "actual_mixed_przz_error_tends_to_zero_without_regularity_premises": True,
        "fixed_witness_normalized_moment_uniform_from_PRZZ": True,
        "all_finite_mixed_moment_jets_at_negative_R": True,
        "moment_jet_regularity_premises_discharged": True,
        "moment_contract_limit_is_exact_K2_evaluator": True,
        "explicit_mixed_zeta_derivative_integral_identity": True,
        "finite_operator_moment_integral_identity": True,
        "real_operator_absolute_square_moment_limit": True,
        "fixed_degree_six_witness_matches_numerical_functional": True,
        "actual_mass_normalized_square_moment_eventually_lt_1_128202": True,
        "eventual_moment_cap_has_strict_logarithmic_margin": True,
        "moment_bound_requires_fixed_nonnegative_weight_of_positive_mass": True,
        "moment_limit_uses_existing_PRZZ_external_axiom": True,
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
        "general_C2_mobius_weight_transfer_proved": True,
        "absolute_logMean_error_Cesaro_limit_proved": True,
        "shifted_profile_uniform_derivative_bounds_supplied": True,
        "shifted_profile_jet_limit_proved": True,
        "unrestricted_shifted_profile_uniform_on_both_bidiscs": True,
        "restricted_shifted_sum_exact_convolution_proved": True,
        "harmonic_product_supported_tail_uniform_zero_proved": True,
        "product_error_harmonic_transfer_with_explicit_envelopes_proved": True,
        "actual_coprime_endpoint_uniform_bound_proved": True,
        "actual_coprime_harmonic_second_moment_proved": True,
        "finite_coprime_head_mainterm_uniformly_identified": True,
        "actual_interior_coprime_product_error_envelopes_supplied": True,
        "actual_log_endpoint_quantitative_bound_proved": True,
        "zero_shift_totient_weight_identified": True,
        "totient_weight_harmonic_asymptotic_proved": True,
        "totient_normalized_summatory_uniform_proved": True,
        "totient_complex_weighted_Abel_error_proved": True,
        "shifted_outer_weight_finite_Euler_product_proved": True,
        "shifted_outer_Euler_ratio_uniform_limit_proved": True,
        "shifted_outer_Euler_ratio_uniform_for_growing_g_on_both_bidiscs": True,
        "shifted_outer_weight_averaged_replacement_proved": True,
        "bounded_test_array_outer_weight_error_proved": True,
        "logarithmic_profile_sum_explicit_error_proved": True,
        "shifted_Euler_model_outer_profile_limit_on_both_bidiscs_proved": True,
        "outer_profile_integral_identified_with_H00": True,
        "supported_full_Euler_mass_product_tail_proved": True,
        "actual_interior_coprime_products_zero_shift_Euler_average_proved": True,
        "zero_shift_to_shifted_inner_Euler_replacement_proved": True,
        "literal_bare_prefactor_uniform_bound_proved": True,
        "coprime_product_endpoint_gluing_proved": True,
        "actual_diagonal_Conrey_sum_H00_limit_on_both_bidiscs_proved": True,
        "literal_PRZZ_Conrey_coefficient_adapter_proved": True,
        "original_PRZZ_Conrey_scaled_arithmetic_H00_limit_proved": True,
        "original_PRZZ_Conrey_normalized_gcd_exact_adapter_proved": True,
        "original_PRZZ_Conrey_normalized_gcd_uniform_limit_proved": True,
        "Feng_logarithmic_convolution_decomposition_proved": True,
        "Feng_prime_square_nonzero_regression_proved": True,
        "original_PRZZ_ordered_four_component_split_proved": True,
        "Feng_shift_derivative_and_prime_power_convolution_identity_proved": True,
        "Feng_at_gn_shared_prime_power_split_proved": True,
        "Feng_log_block_endpoint_safe_growing_g_bound_proved": True,
        "Feng_log_block_product_endpoint_small_on_both_bidiscs": True,
        "Feng_outside_finite_proxy_weighted_error_proved": True,
        "Feng_shared_prime_local_telescope_proved": True,
        "Feng_prime_power_scaled_mass_uniform_bound_proved": True,
        "Feng_outside_endpoint_safe_Euler_bound_on_both_bidiscs": True,
        "Feng_outside_product_endpoint_small_on_both_bidiscs": True,
        "Feng_global_shared_divisor_cancellation_proved": True,
        "Feng_sharedBlock_exact_residual_formula_proved": True,
        "Feng_residual_exact_prime_power_reindexing_to_coprimeScaled_proved": True,
        "Feng_shared_finite_main_proxy_and_weighted_error_proved": True,
        "Feng_shared_growing_g_endpoint_safe_Euler_bound_proved": True,
        "Feng_complete_block_product_endpoint_small_on_both_bidiscs": True,
        "Feng_shared_positive_power_tail_uniform_O_one_over_L_proved": True,
        "Feng_shared_product_remainder_o_one_on_both_bidiscs_proved": True,
        "Feng_shared_marked_profile_finite_identity_proved": True,
        "Feng_marked_actual_Abel_error_bound_proved": True,
        "Feng_marked_profile_uniform_transfer_from_explicit_scalar_premise_proved": True,
        "Feng_marked_scalar_asymptotic_discharged": True,
        "Feng_signed_mixed_scalar_minus_one_sixth_proved": True,
        "Feng_signed_mixed_Abel_profile_limit_on_both_bidiscs_proved": True,
        "Feng_actual_Conrey_shared_zero_shift_outer_weight_limit_proved": True,
        "Feng_actual_Conrey_shared_endpoint_safe_averaged_error_proved": True,
        "Feng_actual_Conrey_shared_raw_shifted_outer_weight_limit_proved": True,
        "Feng_mixed_raw_weight_shift_replacement_proved": True,
        "Feng_K20_K02_remaining_kernel_targets_checked": True,
        "Feng_actual_Conrey_logBlock_raw_shifted_limit_proved": True,
        "Feng_outside_candidate_convolution_equals_inverse_profile": True,
        "Feng_Conrey_Feng_assembly_conditional_on_actual_outside_limit": True,
        "Feng_actual_Conrey_outsideBlock_limit_proved": True,
        "Feng_outside_outerProxy_profile_integral_uniform": True,
        "Feng_Conrey_Feng_fullSum_poleSum02_before_theta_normalization": True,
        "mixed_PRZZ_scaledArithmetic_H02_H20_uniform_both_bidiscs": True,
        "mixed_theta_minus_two_finite_coefficient_bridge": True,
        "mixed_original_normalized_gcd_H02_H20_uniform": True,
        "K22_five_actual_logarithmic_products_uniform": True,
        "K22_exact_nine_product_shifted_decomposition": True,
        "K22_remaining_four_shifted_products_discharged": True,
        "K22_actual_shifted_outside_outside_limit_proved": True,
        "K22_proxy_shared_signed_marked_profile_bridge_proved": True,
        "K22_actual_ordered_outside_shared_limits_proved": True,
        "K22_shared_shared_shifted_weight_limit_proved": True,
        "K22_theta_minus_four_original_coefficient_bridge": True,
        "K22_H22_arithmetic_limit_both_bidiscs": True,
        "K22_original_normalized_gcd_uniform_on_witness_bidisc": True,
        "two_piece_ordered_four_component_gcd_assembly": True,
        "two_piece_original_arithmetic_uniform_both_bidiscs": True,
        "two_piece_same_profile_limit_is_shiftedFunctional": True,
        "fixed_witness_full_normalized_gcd_uniform": True,
        "Feng_outside_finite_mainProxy_inverse_profile_uniform_growing_g": True,
        "Feng_outside_mainProxy_includes_zero_endpoint_and_both_bidiscs": True,
        "Feng_outside_actual_inner_replacement_average_discharge": True,
        "Feng_outside_moving_endpoint_prime_power_window_proved": True,
        "Feng_outside_raw_shifted_outer_proxy_difference_uniform_zero": True,
        "Feng_actual_shared_product_zero_shift_outer_weight_limit_proved": True,
        "Feng_marked_higher_prime_power_tail_normalized_zero": True,
        "Feng_marked_diagonal_one_twentieth_and_ordered_cross_one_120_proved": True,
        "Feng_marked_exact_prime_power_and_ordered_pair_decomposition_proved": True,
        "Totient_coprime_exclusion_uniform_log_bounds_proved": True,
        "Feng_shared_marked_totient_profile_integral_limit_proved": True,
        "Feng_shared_and_outside_prime_power_asymptotics_proved": False,
        "Feng_K20_K02_K22_uniform_asymptotics_proved": False,
        "coprimality_averaged_error_proved": False,
        "gcd_mainterm_limit_proved": True,
        "certified_logarithmic_budget_strictly_above_target": True,
        "wu_trimmed_regularized_log_integral_bound": True,
        "wu_terminal_anchored_window_tiling": True,
        "wu_all_height_transfer_from_explicit_local_counting_input": True,
        "wu_interior_route_requires_localized_estimate": False,
        "wu_actual_local_counting_inequality_proved": True,
        "wu_counting_adapter_proved": True,
        "wu_all_terminal_heights_fixed_strict_margin": True,
        "wu_final_proportion_requires_localized_estimate": False,
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
        "przz_external_axiom_count": 1, "final_proportion_formalized": True,
        "final_proportion_scope": "Actual xi-prime counts with multiplicity, conditional only on the existing PRZZ input beyond standard axioms",
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
