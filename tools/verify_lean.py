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
                output = run(command + [str(source_dir / name)], af, env)
                # Preserve successful fresh compiler diagnostics even if a later
                # registry audit fails. This is not an input/build cache.
                diagnostics = env.get("XIPRIME_DIAGNOSTICS_DIR")
                if diagnostics:
                    destination = Path(diagnostics)
                    destination.mkdir(parents=True, exist_ok=True)
                    (destination / (name + ".json")).write_text(json.dumps({
                        "name": name, "sha256": sha(source_dir / name),
                        "exit_code": 0, "output": output,
                    }, indent=2) + "\n")
                return output

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
                     "WuDyadicCounting.lean", "WuTotalAsymptotic.lean", "WuProportion.lean",
                     "PRZZKloostermanInputs.lean", "PRZZLambda.lean", "PRZZHeathBrown.lean",
                     "PRZZWeightedHeathBrown.lean", "PRZZTypeI.lean", "PRZZTypeII.lean",
                     "PRZZDyadic.lean", "PRZZMobiusHeathBrown.lean", "PRZZMellinSeparation.lean",
                     "PRZZTypeIWeights.lean", "PRZZMellinTypeII.lean", "PRZZSmoothMellin.lean",
                     "PRZZSmoothWeights.lean", "PRZZGcdAverage.lean",
                     "PRZZDyadicArithmetic.lean", "PRZZTypeIFrequency.lean", "PRZZDISeven.lean",
                     "PRZZSourceTypeII.lean", "PRZZDIExpansion.lean", "PRZZGCoefficient.lean", "PRZZEulerSubpower.lean",
                     "PRZZGAbsorption.lean", "PRZZCoprimeAllocation.lean", "PRZZConvolutionSplit.lean",
                     "PRZZCoefficientSeparation.lean", "PRZZAStar.lean", "PRZZAStarIntegrability.lean",
                     "PRZZAStarMellin.lean", "PRZZAStarFubini.lean", "PRZZAStarFrequency.lean",
                     "PRZZWindowWeight.lean", "PRZZAStarWindow.lean", "PRZZWindowDominance.lean",
                     "PRZZNuCoefficient.lean", "PRZZActualMellin.lean", "PRZZAStarTransform.lean",
                     "PRZZNuBounds.lean", "PRZZAStarNu.lean", "PRZZSignedTypeII.lean",
                     "PRZZAStarRectangles.lean", "PRZZAStarIntegralBound.lean",
                     "PRZZFullHeathBrown.lean", "PRZZOuterMass.lean",
                     "PRZZGroupedConvolution.lean", "PRZZGroupedDI.lean",
                     "PRZZGroupBounds.lean", "PRZZSharpCutoff.lean", "PRZZSharpCost.lean", "PRZZSharpDI.lean",
                     "PRZZHBBranches.lean", "PRZZSharpAggregation.lean", "PRZZHBRectangles.lean",
                     "PRZZTypedClassification.lean", "PRZZHBAtomSupply.lean", "PRZZSharpGrouped.lean",
                     "PRZZDyadicSupport.lean", "PRZZTypeIVariation.lean",
                     "PRZZBranchGrouping.lean", "PRZZSourceEnvelope.lean", "PRZZGroupedSeven.lean",
                     "PRZZSourceAbsorption.lean", "PRZZBranchDegrees.lean", "PRZZBranchEnvelope.lean",
                     "PRZZBranchSeven.lean", "PRZZSourceCoefficients.lean", "PRZZBranchMass.lean",
                     "PRZZDyadicBudget.lean", "PRZZLiteralBranches.lean",
                     "PRZZSupportedSplit.lean", "PRZZSupportedBranches.lean",
                     "PRZZSupportedAllocation.lean", "PRZZSupportedSource.lean",
                     "PRZZResidualCoprime.lean", "PRZZWeightedDI.lean",
                     "PRZZResidualWeighted.lean", "PRZZResidualRow.lean",
                     "PRZZResidualBoxes.lean", "PRZZMaskedVariation.lean", "PRZZMaskedSource.lean",
                     "PRZZRowWindow.lean", "PRZZMellinMoment.lean", "PRZZLinearOuter.lean",
                     "PRZZActualBranchCells.lean", "PRZZActualBranchDI.lean",
                     "PRZZSourceScales.lean", "PRZZInflatedSeven.lean",
                     "PRZZMaskedAbsorption.lean", "PRZZInflatedOuter.lean",
                     "PRZZLocalReexpansion.lean", "PRZZSmallRowVariation.lean",
                     "PRZZActualRowSmooth.lean", "PRZZSplitScaleSum.lean", "PRZZSplitScaleOuter.lean",
                     "PRZZRowPlacement.lean", "PRZZAllBranchCells.lean",
                     "PRZZActualSupportBoxes.lean", "PRZZSourceGroupDI.lean",
                     "PRZZZeroExtension.lean", "PRZZActualRowRectangle.lean", "PRZZWholeRowsSum.lean",
                     "PRZZPositiveRow.lean", "PRZZCellAggregation.lean", "PRZZSignedSourceCell.lean", "PRZZTypeICoprime.lean",
                     "PRZZInversePhase.lean", "PRZZEffectiveBalance.lean", "PRZZEffectiveAverage.lean",
                     "PRZZTypeICost.lean", "PRZZAllocatedCells.lean",
                     "PRZZRowCellLayout.lean", "PRZZCommonCellBound.lean",
                     "PRZZHiAllocatedCells.lean", "PRZZCellMass.lean", "PRZZFreeLogRow.lean", "PRZZFreeLogCoprime.lean", "PRZZFreeSource.lean", "PRZZFreeDyadic.lean",
                     "PRZZBareFactors.lean", "PRZZFreeCoefficient.lean", "PRZZFreeCell.lean", "PRZZAllocationMass.lean", "PRZZModulusBudget.lean",
                     "PRZZFreeLength.lean", "PRZZFreeLengthCoefficient.lean", "PRZZFreeLengthCell.lean", "PRZZLengthBudget.lean",
                     "PRZZModulusScale.lean", "PRZZCombinedBudget.lean", "PRZZTypeIScaleSupplier.lean",
                     "PRZZDyadicModulus.lean", "PRZZDyadicCellBound.lean", "PRZZMixedOuter.lean",
                     "PRZZActualSignedBranches.lean", "PRZZAllSignedSources.lean", "PRZZRetainedScale.lean",
                     "PRZZAllCellsBound.lean", "PRZZSignedCellsAggregate.lean", "PRZZDyadicWindow.lean",
                     "PRZZDyadicEnvelope.lean", "PRZZGaussianLine.lean", "PRZZWindowComposition.lean",
                     "PRZZGaussianTail.lean", "PRZZGaussianCorrection.lean", "PRZZSourceW.lean",
                     "PRZZSourceWOuter.lean", "PRZZPositiveMellin.lean",
                     "PRZZBalancedCellEnvelope.lean", "PRZZActualBudgetLayout.lean", "PRZZActualTypeI.lean",
                     "PRZZActualSmall.lean", "PRZZActualCases.lean", "PRZZActualCaseSum.lean",
                     "PRZZActualAggregate.lean", "PRZZPositiveOuter.lean", "PRZZActualAStar.lean",
                     "PRZZOptimalPowers.lean", "PRZZL1Finite.lean", "PRZZOptimalOuter.lean",
                     "PRZZL1Truncation.lean", "PRZZL1Poisson.lean", "PRZZActualCasePowers.lean",
                     "PRZZActualRowOuter.lean", "PRZZOriginalRowWindow.lean",
                     "PRZZActualLoss.lean", "PRZZRowMellinBranches.lean",
                     "PRZZLiteralRows.lean", "PRZZThreeCaseLoss.lean", "PRZZNonemptyRowBudget.lean",
                     "PRZZRowIntegralBudget.lean", "PRZZActiveRows.lean",
                     "PRZZSourceFrequency.lean", "PRZZL1Residue.lean", "PRZZSourceCutoffs.lean",
                     "PRZZSourceDecay.lean", "PRZZGaussianDerivatives.lean", "PRZZLogDerivatives.lean", "PRZZSourceWDerivatives.lean", "PRZZSourceWSums.lean", "PRZZAFEGamma.lean", "PRZZGammaPath.lean",
                     "PRZZGammaFar.lean", "PRZZMellinTail.lean", "PRZZKernelDifference.lean", "PRZZGammaCentral.lean",
                     "PRZZGammaMain.lean", "PRZZGammaUniform.lean", "PRZZCentralIntegral.lean", "PRZZKernelUniform.lean",
                     "PRZZActualDirectSum.lean", "PRZZAFEDual.lean",
                     "PRZZContourKernel.lean", "PRZZKernelTime.lean", "PRZZNoncentralResidues.lean", "PRZZArithmeticTime.lean", "PRZZMollifiedTime.lean", "PRZZCompletedStrip.lean", "PRZZResidueEnvelope.lean", "PRZZHorizontalDecay.lean", "PRZZFiniteContour.lean", "PRZZInfiniteContour.lean", "PRZZContourAFE.lean", "PRZZSeriesAFE.lean", "PRZZIntegratedAFE.lean", "PRZZPoissonTimeChange.lean", "PRZZReplacementIntegral.lean", "PRZZPhaseError.lean", "PRZZPoissonSpatial.lean", "PRZZCutoffPhase.lean", "PRZZPoissonWDerivative.lean", "PRZZArithmeticMass.lean", "PRZZFullWeightSmooth.lean", "PRZZDyadicArithmeticMass.lean", "PRZZCutoffJets.lean", "PRZZQuadraticJets.lean", "PRZZReciprocalJets.lean", "PRZZPowerJets.lean", "PRZZFullWeightJets.lean", "PRZZWeightFourier.lean", "PRZZWeightTail.lean", "PRZZSourceTailBudget.lean", "PRZZEnvelopeMass.lean", "PRZZJetUniform.lean", "PRZZNormalizedTail.lean", "PRZZPhaseDegree.lean", "PRZZZeroPhaseBudget.lean", "PRZZTailSourceFamily.lean", "PRZZExtendedTailDomain.lean", "PRZZPrunedTailRows.lean", "PRZZAbsorbedFourierTail.lean", "PRZZTailTimeSum.lean", "PRZZArithmeticFourierTail.lean", "PRZZFourierTime.lean", "PRZZSourceRows.lean", "PRZZInfiniteTail.lean", "PRZZAFEIndices.lean", "PRZZAFEProgression.lean", "PRZZGroupedTime.lean", "PRZZQuotientMass.lean", "PRZZHeightMass.lean", "PRZZExplicitDomain.lean", "PRZZExplicitTail.lean", "PRZZPoissonActualWeight.lean", "PRZZCongruencePoisson.lean", "PRZZReplacementMass.lean", "PRZZTruncatedProgression.lean", "PRZZReplacementHeight.lean", "PRZZLocalReplacement.lean", "PRZZActualLocalReplacement.lean", "PRZZDifferenceRegular.lean", "PRZZDifferenceDecay.lean", "PRZZDifferenceContour.lean", "PRZZLeftCentral.lean", "PRZZLeftFar.lean", "PRZZLeftUniform.lean", "PRZZActualSmallReplacement.lean", "PRZZProductMass.lean", "PRZZProductSummation.lean", "PRZZProductTime.lean", "PRZZMeanSquare.lean", "PRZZScaledReplacement.lean", "PRZZResidueTime.lean", "PRZZResidueAbsorption.lean", "PRZZDualError.lean", "PRZZIntegratedDefect.lean", "PRZZFrozenTail.lean", "PRZZCentralTail.lean", "PRZZSharpPoisson.lean", "PRZZInverseProfile.lean", "PRZZExpandedCutoff.lean", "PRZZFrozenProfileBound.lean", "PRZZProfileTimeBudget.lean", "PRZZTransformedSourceBudget.lean", "PRZZSourceTailMass.lean", "PRZZAFEOuterAssembly.lean", "PRZZFrozenFamilyCutoff.lean", "PRZZSourceLattice.lean", "PRZZUnitModulusBudget.lean", "PRZZUnitTailMass.lean", "PRZZSourceWindowCutoff.lean", "PRZZWArithmeticCutoff.lean", "PRZZSourceBoundaryDecay.lean", "PRZZPartitionMass.lean", "PRZZDeltaDecay.lean", "PRZZTimeJets.lean", "PRZZTimeAmplitude.lean", "PRZZTimeDiscarded.lean", "PRZZDiscardedSuppliers.lean", "PRZZDiscardedPartition.lean", "PRZZDiscardedOuter.lean", "PRZZValuedCutoffs.lean", "PRZZWeightedSourcePoisson.lean", "PRZZAmplitudeFreeze.lean", "PRZZFreezeMass.lean", "PRZZFreezeScales.lean", "PRZZPrefactorMass.lean", "PRZZActiveFreezeBudget.lean", "PRZZFiniteFreezeBudget.lean", "PRZZFreezeErrorBudget.lean", "PRZZUnfrozenPoisson.lean", "PRZZPoissonAnalyticMass.lean", "PRZZSpatialFreezeBudget.lean", "PRZZEmptyFrequencyDecay.lean", "PRZZEmptyArithmeticMass.lean", "PRZZEmptyScaleAbsorption.lean", "PRZZEmptyMomentScalar.lean", "PRZZEmptyMomentMass.lean", "PRZZActualPoissonError.lean", "PRZZWRowLimit.lean", "PRZZWRowReindex.lean", "PRZZFilteredResidual.lean", "PRZZLiteralComplement.lean", "PRZZCentralFubini.lean", "PRZZDiagonalMellin.lean", "PRZZDiagonalContour.lean", "PRZZDiagonalAssembly.lean", "PRZZOriginalDiagonal.lean", "PRZZDiagonalMass.lean", "PRZZCoupledAFE.lean", "PRZZZeroReflection.lean", "PRZZSignedCentral.lean", "PRZZZeroGap.lean", "PRZZZeroGapExchange.lean", "PRZZZeroSpatialLimit.lean", "PRZZZeroCutoffLimit.lean", "PRZZZeroCosine.lean", "PRZZGammaLaplace.lean", "PRZZCosineAbel.lean", "PRZZZeroSourceHeight.lean", "PRZZCosineImproper.lean", "PRZZCosineDominated.lean", "PRZZCosineMellinCore.lean", "PRZZCosineMellin.lean", "PRZZSourceWLine.lean", "PRZZZeroMellinSpace.lean", "PRZZZeroMellinLimit.lean", "PRZZCosineGapMellin.lean", "PRZZReflectedEnvelope.lean", "PRZZReflectedContour.lean", "PRZZCosineGapCorrection.lean", "PRZZCosineSpatialJets.lean", "PRZZCosineSpatialBoundary.lean", "PRZZCosineSpatialImproper.lean", "PRZZCosineFiniteFubini.lean", "PRZZCosineDerivativeMellin.lean", "PRZZCosineTimeDomination.lean", "PRZZCosineTimeMellin.lean", "PRZZCosineMovingWindow.lean", "PRZZZeroReciprocal.lean", "PRZZZeroReciprocalRows.lean", "PRZZZeroRowMellin.lean", "PRZZZeroOuterMellin.lean", "PRZZZeroNormalization.lean", "PRZZZeroGapTime.lean", "PRZZActualZeroReflection.lean", "PRZZZeroCross.lean", "PRZZZeroCoupled.lean", "PRZZZeroGammaBound.lean", "PRZZZeroFourierReduction.lean", "PRZZAllOffDiagonalRows.lean", "PRZZAllPoissonRows.lean", "PRZZAllPoissonAFE.lean", "PRZZResolvedComplement.lean", "PRZZZeroExhaustionCross.lean", "PRZZResolvedBoundary.lean", "PRZZDualSmooth.lean", "PRZZZeroDualExhaustion.lean", "PRZZResolvedTail.lean", "PRZZPartitionDiscrepancy.lean", "PRZZOriginalSpatialLimit.lean", "PRZZArithmeticBoundaryFamily.lean", "PRZZNativeFamily.lean", "PRZZNativeComponents.lean", "PRZZNativeGcdGrid.lean", "PRZZResolvedTailMass.lean", "PRZZLargeSpatialKernel.lean", "PRZZLargeSpatialFamily.lean", "PRZZLargeSpatialHeight.lean", "PRZZLargeResolvedPruning.lean", "PRZZWindowGrids.lean", "PRZZWindowTailMass.lean", "PRZZWindowTailTime.lean", "PRZZWindowNativeTail.lean", "PRZZWindowBoundary.lean", "PRZZValuedSourceDiscarded.lean", "PRZZWindowErrorJoin.lean", "PRZZDualTimeIBP.lean", "PRZZDualDiscardedIBP.lean", "PRZZExhaustiveAFEError.lean", "PRZZSourceMaskFamily.lean", "PRZZDualFirstJet.lean", "PRZZDiscardedAFEBridge.lean", "PRZZPolygammaSeries.lean", "PRZZDualHigherJets.lean", "PRZZDualJetTransfer.lean", "PRZZDualJetMass.lean", "PRZZDualDiscardedBudget.lean", "PRZZDualWindowErrorJoin.lean", "PRZZDiscardedTimePair.lean", "PRZZPrunedAFEError.lean", "PRZZRetainedNative.lean", "PRZZNativeCentralLiteral.lean", "PRZZKeptLiteral.lean", "PRZZRejectedExhaustion.lean", "PRZZArithmeticCutoffPartition.lean", "PRZZSelectedLocalFourier.lean", "PRZZLocalTailBudget.lean", "PRZZFullFreezeBudget.lean", "PRZZSpatialErrorJoin.lean", "PRZZNativeFreezeEnvelope.lean", "PRZZDualNativeFreeze.lean", "PRZZNativeFreezeTime.lean", "PRZZIntegratedFreezeAFE.lean", "PRZZFreezeRemovedLiteral.lean", "PRZZLiteralAFEJoin.lean", "PRZZCompatibleTail.lean", "PRZZResidualPartition.lean", "PRZZBandOuterMass.lean", "PRZZSpatialReconstruction.lean", "PRZZSameMaskResidual.lean", "PRZZSameMaskFreezeBudget.lean", "PRZZReconstructedAFE.lean", "PRZZStrictSmallTail.lean", "PRZZSmallCentralLiteral.lean", "PRZZSelectedDiscarded.lean", "PRZZSelectedDiscardedFamily.lean", "PRZZRemainderBudget.lean", "PRZZRemainderAbsorption.lean", "PRZZLiteralExhaustion.lean", "PRZZLiteralTotalBound.lean", "PRZZFourierExhaustion.lean", "PRZZLiteralFourierLimit.lean", "PRZZFullLiteralBound.lean", "PRZZCentralArithmeticJoin.lean", "PRZZCentralMainAssembly.lean", "PRZZCentralGridWeilDI.lean", "PRZZWeilDIMainBound.lean", "PRZZDualProfileUniform.lean", "PRZZMellinSeminorm.lean", "PRZZDualMellinUniform.lean", "PRZZArithmeticTailLimit.lean", "PRZZNegativeArithmetic.lean", "PRZZNegativeMellin.lean", "PRZZNegativeOuter.lean", "PRZZNegativeGrid.lean", "PRZZZeroMismatchLimit.lean", "PRZZIndexedCaps.lean", "PRZZUniformTypeI.lean", "PRZZUniformCases.lean", "PRZZUniformAggregate.lean", "PRZZUniformOuter.lean", "PRZZUniformGrid.lean", "PRZZZeroUniformHeight.lean", "PRZZZeroSpatialHeight.lean", "PRZZZeroOmittedGaps.lean", "PRZZZeroOuterHeight.lean", "PRZZZeroNativeTail.lean", "PRZZZeroIntegerReindex.lean", "PRZZZeroCompleteCell.lean", "PRZZZeroDualHeight.lean", "PRZZZeroBoundaryHeight.lean", "PRZZZeroNativeCompletion.lean", "PRZZZeroSpatialPrefix.lean", "PRZZZeroArithmeticPartition.lean", "PRZZZeroBoundarySum.lean", "PRZZZeroBoundaryIdentity.lean", "PRZZZeroDualBoundary.lean", "PRZZZeroDualGaps.lean", "PRZZZeroDualOuter.lean", "PRZZZeroDualNativeTail.lean", "PRZZZeroMismatchHeight.lean", "PRZZWeilDIZeroJoin.lean", "PRZZGammaBudgetAbsorption.lean", "PRZZWeilDIErrorJoin.lean", "PRZZSignedUniformGrid.lean", "PRZZSignedMomentBudget.lean", "PRZZLocalFrequencyLoss.lean", "PRZZLocalCentralTransfer.lean", "PRZZDisjointSpatialJoin.lean", "PRZZArithmeticWindowCutoff.lean", "PRZZWindowBandMass.lean", "PRZZSubunitFourier.lean", "PRZZSubunitWindowMass.lean", "PRZZWideRowBudget.lean", "PRZZWindowCentralAssembly.lean", "PRZZWindowMoment.lean", "PRZZWideActiveRows.lean", "PRZZWindowScaleSupply.lean", "PRZZWindowSpatialJoin.lean", "PRZZWindowOptimalCell.lean", "PRZZOuterLogBudget.lean", "PRZZNegativeLocalRows.lean", "PRZZPositiveOuterGrid.lean", "PRZZNegativeRowWindow.lean", "PRZZNegativeRowIntegral.lean", "PRZZNegativeLiteralRows.lean", "PRZZNegativeActiveRows.lean", "PRZZNegativeWindowCell.lean", "PRZZNegativeOuterGrid.lean", "PRZZCommonSignedWindow.lean", "PRZZCommonWindowCollector.lean", "PRZZCommonCutMoment.lean", "PRZZCommonResidualJoin.lean", "PRZZActualTailNative.lean", "PRZZActualTailCollector.lean", "PRZZBodyTailMass.lean", "PRZZBodyTailTime.lean", "PRZZTailRowIntegrable.lean", "PRZZNativeTailRectangle.lean", "PRZZBodyTailCollector.lean", "PRZZBodyTailOptimal.lean", "PRZZMomentOptimal.lean"):
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
        if name in {"PRZZKloostermanInputs.lean", "PRZZLambda.lean", "PRZZHeathBrown.lean",
                    "PRZZWeightedHeathBrown.lean", "PRZZTypeI.lean", "PRZZTypeII.lean",
                    "PRZZDyadic.lean", "PRZZMobiusHeathBrown.lean", "PRZZMellinSeparation.lean",
                    "PRZZTypeIWeights.lean", "PRZZMellinTypeII.lean", "PRZZSmoothMellin.lean",
                    "PRZZSmoothWeights.lean", "PRZZGcdAverage.lean",
                    "PRZZDyadicArithmetic.lean", "PRZZTypeIFrequency.lean", "PRZZDISeven.lean",
                    "PRZZSourceTypeII.lean", "PRZZDIExpansion.lean", "PRZZGCoefficient.lean", "PRZZEulerSubpower.lean",
                    "PRZZGAbsorption.lean", "PRZZCoprimeAllocation.lean", "PRZZConvolutionSplit.lean",
                    "PRZZCoefficientSeparation.lean", "PRZZAStar.lean", "PRZZAStarIntegrability.lean",
                    "PRZZAStarMellin.lean", "PRZZAStarFubini.lean", "PRZZAStarFrequency.lean",
                    "PRZZWindowWeight.lean", "PRZZAStarWindow.lean", "PRZZWindowDominance.lean",
                    "PRZZNuCoefficient.lean", "PRZZActualMellin.lean", "PRZZAStarTransform.lean",
                    "PRZZNuBounds.lean", "PRZZAStarNu.lean", "PRZZSignedTypeII.lean",
                    "PRZZAStarRectangles.lean", "PRZZAStarIntegralBound.lean",
                    "PRZZFullHeathBrown.lean", "PRZZOuterMass.lean",
                    "PRZZGroupedConvolution.lean", "PRZZGroupedDI.lean",
                    "PRZZGroupBounds.lean", "PRZZSharpCutoff.lean", "PRZZSharpCost.lean", "PRZZSharpDI.lean",
                    "PRZZHBBranches.lean", "PRZZSharpAggregation.lean", "PRZZHBRectangles.lean",
                    "PRZZTypedClassification.lean", "PRZZHBAtomSupply.lean", "PRZZSharpGrouped.lean",
                    "PRZZDyadicSupport.lean", "PRZZTypeIVariation.lean",
                    "PRZZBranchGrouping.lean", "PRZZSourceEnvelope.lean", "PRZZGroupedSeven.lean",
                    "PRZZSourceAbsorption.lean", "PRZZBranchDegrees.lean", "PRZZBranchEnvelope.lean",
                    "PRZZBranchSeven.lean", "PRZZSourceCoefficients.lean", "PRZZBranchMass.lean",
                    "PRZZDyadicBudget.lean", "PRZZLiteralBranches.lean",
                    "PRZZSupportedSplit.lean", "PRZZSupportedBranches.lean",
                    "PRZZSupportedAllocation.lean", "PRZZSupportedSource.lean",
                    "PRZZResidualCoprime.lean", "PRZZWeightedDI.lean",
                    "PRZZResidualWeighted.lean", "PRZZResidualRow.lean",
                    "PRZZResidualBoxes.lean", "PRZZMaskedVariation.lean", "PRZZMaskedSource.lean",
                    "PRZZRowWindow.lean", "PRZZMellinMoment.lean", "PRZZLinearOuter.lean",
                    "PRZZActualBranchCells.lean", "PRZZActualBranchDI.lean",
                    "PRZZSourceScales.lean", "PRZZInflatedSeven.lean",
                    "PRZZMaskedAbsorption.lean", "PRZZInflatedOuter.lean",
                    "PRZZLocalReexpansion.lean", "PRZZSmallRowVariation.lean",
                    "PRZZActualRowSmooth.lean", "PRZZSplitScaleSum.lean", "PRZZSplitScaleOuter.lean",
                    "PRZZRowPlacement.lean", "PRZZAllBranchCells.lean",
                    "PRZZActualSupportBoxes.lean", "PRZZSourceGroupDI.lean",
                    "PRZZZeroExtension.lean", "PRZZActualRowRectangle.lean", "PRZZWholeRowsSum.lean",
                    "PRZZPositiveRow.lean", "PRZZCellAggregation.lean", "PRZZSignedSourceCell.lean", "PRZZTypeICoprime.lean",
                    "PRZZInversePhase.lean", "PRZZEffectiveBalance.lean", "PRZZEffectiveAverage.lean",
                    "PRZZTypeICost.lean", "PRZZAllocatedCells.lean",
                    "PRZZRowCellLayout.lean", "PRZZCommonCellBound.lean",
                    "PRZZHiAllocatedCells.lean", "PRZZCellMass.lean", "PRZZFreeLogRow.lean", "PRZZFreeLogCoprime.lean", "PRZZFreeSource.lean", "PRZZFreeDyadic.lean",
                    "PRZZBareFactors.lean", "PRZZFreeCoefficient.lean", "PRZZFreeCell.lean", "PRZZAllocationMass.lean", "PRZZModulusBudget.lean",
                    "PRZZFreeLength.lean", "PRZZFreeLengthCoefficient.lean", "PRZZFreeLengthCell.lean", "PRZZLengthBudget.lean",
                    "PRZZModulusScale.lean", "PRZZCombinedBudget.lean", "PRZZTypeIScaleSupplier.lean",
                    "PRZZDyadicModulus.lean", "PRZZDyadicCellBound.lean", "PRZZMixedOuter.lean",
                    "PRZZActualSignedBranches.lean", "PRZZAllSignedSources.lean", "PRZZRetainedScale.lean",
                    "PRZZAllCellsBound.lean", "PRZZSignedCellsAggregate.lean", "PRZZDyadicWindow.lean",
                    "PRZZDyadicEnvelope.lean", "PRZZGaussianLine.lean", "PRZZWindowComposition.lean",
                    "PRZZGaussianTail.lean", "PRZZGaussianCorrection.lean", "PRZZSourceW.lean",
                    "PRZZSourceWOuter.lean", "PRZZPositiveMellin.lean",
                    "PRZZBalancedCellEnvelope.lean", "PRZZActualBudgetLayout.lean", "PRZZActualTypeI.lean",
                    "PRZZActualSmall.lean", "PRZZActualCases.lean", "PRZZActualCaseSum.lean",
                    "PRZZActualAggregate.lean", "PRZZPositiveOuter.lean", "PRZZActualAStar.lean",
                    "PRZZOptimalPowers.lean", "PRZZL1Finite.lean", "PRZZOptimalOuter.lean",
                    "PRZZL1Truncation.lean", "PRZZL1Poisson.lean", "PRZZActualCasePowers.lean",
                    "PRZZActualRowOuter.lean", "PRZZOriginalRowWindow.lean",
                    "PRZZActualLoss.lean", "PRZZRowMellinBranches.lean",
                    "PRZZLiteralRows.lean", "PRZZThreeCaseLoss.lean", "PRZZNonemptyRowBudget.lean",
                    "PRZZRowIntegralBudget.lean", "PRZZActiveRows.lean",
                    "PRZZSourceFrequency.lean", "PRZZL1Residue.lean", "PRZZSourceCutoffs.lean",
                    "PRZZSourceDecay.lean", "PRZZGaussianDerivatives.lean", "PRZZLogDerivatives.lean", "PRZZSourceWDerivatives.lean", "PRZZSourceWSums.lean", "PRZZAFEGamma.lean", "PRZZGammaPath.lean",
                    "PRZZGammaFar.lean", "PRZZMellinTail.lean", "PRZZKernelDifference.lean", "PRZZGammaCentral.lean",
                    "PRZZGammaMain.lean", "PRZZGammaUniform.lean", "PRZZCentralIntegral.lean", "PRZZKernelUniform.lean",
                    "PRZZActualDirectSum.lean", "PRZZAFEDual.lean",
                    "PRZZContourKernel.lean", "PRZZKernelTime.lean", "PRZZNoncentralResidues.lean", "PRZZArithmeticTime.lean", "PRZZMollifiedTime.lean", "PRZZCompletedStrip.lean", "PRZZResidueEnvelope.lean", "PRZZHorizontalDecay.lean", "PRZZFiniteContour.lean", "PRZZInfiniteContour.lean", "PRZZContourAFE.lean", "PRZZSeriesAFE.lean", "PRZZIntegratedAFE.lean", "PRZZPoissonTimeChange.lean", "PRZZReplacementIntegral.lean", "PRZZPhaseError.lean", "PRZZPoissonSpatial.lean", "PRZZCutoffPhase.lean", "PRZZPoissonWDerivative.lean", "PRZZArithmeticMass.lean", "PRZZFullWeightSmooth.lean", "PRZZDyadicArithmeticMass.lean", "PRZZCutoffJets.lean", "PRZZQuadraticJets.lean", "PRZZReciprocalJets.lean", "PRZZPowerJets.lean", "PRZZFullWeightJets.lean", "PRZZWeightFourier.lean", "PRZZWeightTail.lean", "PRZZSourceTailBudget.lean", "PRZZEnvelopeMass.lean", "PRZZJetUniform.lean", "PRZZNormalizedTail.lean", "PRZZPhaseDegree.lean", "PRZZZeroPhaseBudget.lean", "PRZZTailSourceFamily.lean", "PRZZExtendedTailDomain.lean", "PRZZPrunedTailRows.lean", "PRZZAbsorbedFourierTail.lean", "PRZZTailTimeSum.lean", "PRZZArithmeticFourierTail.lean", "PRZZFourierTime.lean", "PRZZSourceRows.lean", "PRZZInfiniteTail.lean", "PRZZAFEIndices.lean", "PRZZAFEProgression.lean", "PRZZGroupedTime.lean", "PRZZQuotientMass.lean", "PRZZHeightMass.lean", "PRZZExplicitDomain.lean", "PRZZExplicitTail.lean", "PRZZPoissonActualWeight.lean", "PRZZCongruencePoisson.lean", "PRZZReplacementMass.lean", "PRZZTruncatedProgression.lean", "PRZZReplacementHeight.lean", "PRZZLocalReplacement.lean", "PRZZActualLocalReplacement.lean", "PRZZDifferenceRegular.lean", "PRZZDifferenceDecay.lean", "PRZZDifferenceContour.lean", "PRZZLeftCentral.lean", "PRZZLeftFar.lean", "PRZZLeftUniform.lean", "PRZZActualSmallReplacement.lean", "PRZZProductMass.lean", "PRZZProductSummation.lean", "PRZZProductTime.lean", "PRZZMeanSquare.lean", "PRZZScaledReplacement.lean", "PRZZResidueTime.lean", "PRZZResidueAbsorption.lean", "PRZZDualError.lean", "PRZZIntegratedDefect.lean", "PRZZFrozenTail.lean", "PRZZCentralTail.lean", "PRZZSharpPoisson.lean", "PRZZInverseProfile.lean", "PRZZExpandedCutoff.lean", "PRZZFrozenProfileBound.lean", "PRZZProfileTimeBudget.lean", "PRZZTransformedSourceBudget.lean", "PRZZSourceTailMass.lean", "PRZZAFEOuterAssembly.lean", "PRZZFrozenFamilyCutoff.lean", "PRZZSourceLattice.lean", "PRZZUnitModulusBudget.lean", "PRZZUnitTailMass.lean", "PRZZSourceWindowCutoff.lean", "PRZZWArithmeticCutoff.lean", "PRZZSourceBoundaryDecay.lean", "PRZZPartitionMass.lean", "PRZZDeltaDecay.lean", "PRZZTimeJets.lean", "PRZZTimeAmplitude.lean", "PRZZTimeDiscarded.lean", "PRZZDiscardedSuppliers.lean", "PRZZDiscardedPartition.lean", "PRZZDiscardedOuter.lean", "PRZZValuedCutoffs.lean", "PRZZWeightedSourcePoisson.lean", "PRZZAmplitudeFreeze.lean", "PRZZFreezeMass.lean", "PRZZFreezeScales.lean", "PRZZPrefactorMass.lean", "PRZZActiveFreezeBudget.lean", "PRZZFiniteFreezeBudget.lean", "PRZZFreezeErrorBudget.lean", "PRZZUnfrozenPoisson.lean", "PRZZPoissonAnalyticMass.lean", "PRZZSpatialFreezeBudget.lean", "PRZZEmptyFrequencyDecay.lean", "PRZZEmptyArithmeticMass.lean", "PRZZEmptyScaleAbsorption.lean", "PRZZEmptyMomentScalar.lean", "PRZZEmptyMomentMass.lean", "PRZZActualPoissonError.lean", "PRZZWRowLimit.lean", "PRZZWRowReindex.lean", "PRZZFilteredResidual.lean", "PRZZLiteralComplement.lean", "PRZZCentralFubini.lean", "PRZZDiagonalMellin.lean", "PRZZDiagonalContour.lean", "PRZZDiagonalAssembly.lean", "PRZZOriginalDiagonal.lean", "PRZZDiagonalMass.lean", "PRZZCoupledAFE.lean", "PRZZZeroReflection.lean", "PRZZSignedCentral.lean", "PRZZZeroGap.lean", "PRZZZeroGapExchange.lean", "PRZZZeroSpatialLimit.lean", "PRZZZeroCutoffLimit.lean", "PRZZZeroCosine.lean", "PRZZGammaLaplace.lean", "PRZZCosineAbel.lean", "PRZZZeroSourceHeight.lean", "PRZZCosineImproper.lean", "PRZZCosineDominated.lean", "PRZZCosineMellinCore.lean", "PRZZCosineMellin.lean", "PRZZSourceWLine.lean", "PRZZZeroMellinSpace.lean", "PRZZZeroMellinLimit.lean", "PRZZCosineGapMellin.lean", "PRZZReflectedEnvelope.lean", "PRZZReflectedContour.lean", "PRZZCosineGapCorrection.lean", "PRZZCosineSpatialJets.lean", "PRZZCosineSpatialBoundary.lean", "PRZZCosineSpatialImproper.lean", "PRZZCosineFiniteFubini.lean", "PRZZCosineDerivativeMellin.lean", "PRZZCosineTimeDomination.lean", "PRZZCosineTimeMellin.lean", "PRZZCosineMovingWindow.lean", "PRZZZeroReciprocal.lean", "PRZZZeroReciprocalRows.lean", "PRZZZeroRowMellin.lean", "PRZZZeroOuterMellin.lean", "PRZZZeroNormalization.lean", "PRZZZeroGapTime.lean", "PRZZActualZeroReflection.lean", "PRZZZeroCross.lean", "PRZZZeroCoupled.lean", "PRZZZeroGammaBound.lean", "PRZZZeroFourierReduction.lean", "PRZZAllOffDiagonalRows.lean", "PRZZAllPoissonRows.lean", "PRZZAllPoissonAFE.lean", "PRZZResolvedComplement.lean", "PRZZZeroExhaustionCross.lean", "PRZZResolvedBoundary.lean", "PRZZDualSmooth.lean", "PRZZZeroDualExhaustion.lean", "PRZZResolvedTail.lean", "PRZZPartitionDiscrepancy.lean", "PRZZOriginalSpatialLimit.lean", "PRZZArithmeticBoundaryFamily.lean", "PRZZNativeFamily.lean", "PRZZNativeComponents.lean", "PRZZNativeGcdGrid.lean", "PRZZResolvedTailMass.lean", "PRZZLargeSpatialKernel.lean", "PRZZLargeSpatialFamily.lean", "PRZZLargeSpatialHeight.lean", "PRZZLargeResolvedPruning.lean", "PRZZWindowGrids.lean", "PRZZWindowTailMass.lean", "PRZZWindowTailTime.lean", "PRZZWindowNativeTail.lean", "PRZZWindowBoundary.lean", "PRZZValuedSourceDiscarded.lean", "PRZZWindowErrorJoin.lean", "PRZZDualTimeIBP.lean", "PRZZDualDiscardedIBP.lean", "PRZZExhaustiveAFEError.lean", "PRZZSourceMaskFamily.lean", "PRZZDualFirstJet.lean", "PRZZDiscardedAFEBridge.lean", "PRZZPolygammaSeries.lean", "PRZZDualHigherJets.lean", "PRZZDualJetTransfer.lean", "PRZZDualJetMass.lean", "PRZZDualDiscardedBudget.lean", "PRZZDualWindowErrorJoin.lean", "PRZZDiscardedTimePair.lean", "PRZZPrunedAFEError.lean", "PRZZRetainedNative.lean", "PRZZNativeCentralLiteral.lean", "PRZZKeptLiteral.lean", "PRZZRejectedExhaustion.lean", "PRZZArithmeticCutoffPartition.lean", "PRZZSelectedLocalFourier.lean", "PRZZLocalTailBudget.lean", "PRZZFullFreezeBudget.lean", "PRZZSpatialErrorJoin.lean", "PRZZNativeFreezeEnvelope.lean", "PRZZDualNativeFreeze.lean", "PRZZNativeFreezeTime.lean", "PRZZIntegratedFreezeAFE.lean", "PRZZFreezeRemovedLiteral.lean", "PRZZLiteralAFEJoin.lean", "PRZZCompatibleTail.lean", "PRZZResidualPartition.lean", "PRZZBandOuterMass.lean", "PRZZSpatialReconstruction.lean", "PRZZSameMaskResidual.lean", "PRZZReconstructedAFE.lean", "PRZZSameMaskFreezeBudget.lean", "PRZZStrictSmallTail.lean", "PRZZSmallCentralLiteral.lean", "PRZZSelectedDiscarded.lean", "PRZZSelectedDiscardedFamily.lean", "PRZZRemainderBudget.lean", "PRZZRemainderAbsorption.lean", "PRZZLiteralExhaustion.lean", "PRZZLiteralTotalBound.lean", "PRZZFourierExhaustion.lean", "PRZZLiteralFourierLimit.lean", "PRZZFullLiteralBound.lean", "PRZZCentralArithmeticJoin.lean", "PRZZCentralMainAssembly.lean", "PRZZCentralGridWeilDI.lean", "PRZZWeilDIMainBound.lean", "PRZZDualProfileUniform.lean", "PRZZMellinSeminorm.lean", "PRZZDualMellinUniform.lean", "PRZZArithmeticTailLimit.lean", "PRZZNegativeArithmetic.lean", "PRZZNegativeMellin.lean", "PRZZNegativeOuter.lean", "PRZZNegativeGrid.lean", "PRZZZeroMismatchLimit.lean", "PRZZIndexedCaps.lean", "PRZZUniformTypeI.lean", "PRZZUniformCases.lean", "PRZZUniformAggregate.lean", "PRZZUniformOuter.lean", "PRZZUniformGrid.lean", "PRZZZeroUniformHeight.lean", "PRZZZeroSpatialHeight.lean", "PRZZZeroOmittedGaps.lean", "PRZZZeroOuterHeight.lean", "PRZZZeroNativeTail.lean", "PRZZZeroIntegerReindex.lean", "PRZZZeroCompleteCell.lean", "PRZZZeroDualHeight.lean", "PRZZZeroBoundaryHeight.lean", "PRZZZeroNativeCompletion.lean", "PRZZZeroSpatialPrefix.lean", "PRZZZeroArithmeticPartition.lean", "PRZZZeroBoundarySum.lean", "PRZZZeroBoundaryIdentity.lean", "PRZZZeroDualBoundary.lean", "PRZZZeroDualGaps.lean", "PRZZZeroDualOuter.lean", "PRZZZeroDualNativeTail.lean", "PRZZZeroMismatchHeight.lean", "PRZZWeilDIZeroJoin.lean", "PRZZGammaBudgetAbsorption.lean", "PRZZWeilDIErrorJoin.lean", "PRZZSignedUniformGrid.lean", "PRZZSignedMomentBudget.lean", "PRZZLocalFrequencyLoss.lean", "PRZZLocalCentralTransfer.lean", "PRZZDisjointSpatialJoin.lean", "PRZZArithmeticWindowCutoff.lean", "PRZZWindowBandMass.lean", "PRZZSubunitFourier.lean", "PRZZSubunitWindowMass.lean", "PRZZWideRowBudget.lean", "PRZZWindowCentralAssembly.lean", "PRZZWindowMoment.lean", "PRZZWideActiveRows.lean", "PRZZWindowScaleSupply.lean", "PRZZWindowSpatialJoin.lean", "PRZZWindowOptimalCell.lean", "PRZZOuterLogBudget.lean", "PRZZNegativeLocalRows.lean", "PRZZPositiveOuterGrid.lean", "PRZZNegativeRowWindow.lean", "PRZZNegativeRowIntegral.lean", "PRZZNegativeLiteralRows.lean", "PRZZNegativeActiveRows.lean", "PRZZNegativeWindowCell.lean", "PRZZNegativeOuterGrid.lean", "PRZZCommonSignedWindow.lean", "PRZZCommonWindowCollector.lean", "PRZZCommonCutMoment.lean", "PRZZCommonResidualJoin.lean", "PRZZActualTailNative.lean", "PRZZActualTailCollector.lean", "PRZZBodyTailMass.lean", "PRZZBodyTailTime.lean", "PRZZTailRowIntegrable.lean", "PRZZNativeTailRectangle.lean", "PRZZBodyTailCollector.lean", "PRZZBodyTailOptimal.lean", "PRZZMomentOptimal.lean"}:
            dependencies = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output))
            dependencies.update({key: "" for key in re.findall(
                r"'([^']+)' does not depend on any axioms", output)})
            audited = set(re.findall(r"^#print axioms ([\w.]+)$", path.read_text(), re.MULTILINE))
            expected_audits = {
                "PRZZTimeDiscarded.lean": {"row_controlled", "summed_controlled", "row", "summed", "actual_coefficient_cap", "order", "actual_block", "negligible"},
                "PRZZDiscardedSuppliers.lean": {"all_gap_geometry", "cutoff_geometry", "log_shift_cap", "outer_mass", "scaled_summed", "loss_absorbed", "scaled_negligible"},
        "PRZZDiscardedPartition.lean": 7,
        "PRZZDiscardedOuter.lean": 8,
        "PRZZValuedCutoffs.lean": 4,
        "PRZZWeightedSourcePoisson.lean": 7,
        "PRZZAmplitudeFreeze.lean": 13,
        "PRZZFreezeMass.lean": 2,
        "PRZZFreezeScales.lean": 6,
        "PRZZPrefactorMass.lean": 8,
        "PRZZActiveFreezeBudget.lean": 14,
        "PRZZFiniteFreezeBudget.lean": 9,
        "PRZZFreezeErrorBudget.lean": 4,
        "PRZZUnfrozenPoisson.lean": 18,
        "PRZZPoissonAnalyticMass.lean": 8,
        "PRZZSpatialFreezeBudget.lean": 4,
        "PRZZEmptyFrequencyDecay.lean": 11,
        "PRZZEmptyArithmeticMass.lean": 9,
        "PRZZEmptyScaleAbsorption.lean": 5,
        "PRZZEmptyMomentScalar.lean": 4,
        "PRZZEmptyMomentMass.lean": 9,
        "PRZZActualPoissonError.lean": 11,
        "PRZZWRowLimit.lean": 8,
        "PRZZWRowReindex.lean": 13,
        "PRZZFilteredResidual.lean": 11, "PRZZLiteralComplement.lean": 8, "PRZZCentralFubini.lean": 9, "PRZZDiagonalMellin.lean": 12, "PRZZDiagonalContour.lean": 14, "PRZZDiagonalAssembly.lean": 18, "PRZZOriginalDiagonal.lean": 8, "PRZZDiagonalMass.lean": 10, "PRZZCoupledAFE.lean": 5, "PRZZZeroReflection.lean": 8, "PRZZSignedCentral.lean": 9, "PRZZZeroGap.lean": 6, "PRZZZeroGapExchange.lean": 6, "PRZZZeroSpatialLimit.lean": 7, "PRZZZeroCutoffLimit.lean": 4, "PRZZZeroCosine.lean": 4, "PRZZGammaLaplace.lean": 8, "PRZZCosineAbel.lean": 5, "PRZZZeroSourceHeight.lean": 4, "PRZZCosineImproper.lean": 15, "PRZZCosineDominated.lean": 8, "PRZZCosineMellinCore.lean": 4, "PRZZCosineMellin.lean": 10, "PRZZSourceWLine.lean": 14, "PRZZZeroMellinSpace.lean": 6, "PRZZZeroMellinLimit.lean": 3, "PRZZCosineGapMellin.lean": 9, "PRZZReflectedEnvelope.lean": 5, "PRZZReflectedContour.lean": 8, "PRZZCosineGapCorrection.lean": 3, "PRZZCosineSpatialJets.lean": 5, "PRZZCosineSpatialBoundary.lean": 7, "PRZZCosineSpatialImproper.lean": 7, "PRZZCosineFiniteFubini.lean": 6, "PRZZCosineDerivativeMellin.lean": 15, "PRZZCosineTimeDomination.lean": 5, "PRZZCosineTimeMellin.lean": 7, "PRZZCosineMovingWindow.lean": 5, "PRZZZeroReciprocal.lean": 4, "PRZZZeroReciprocalRows.lean": 8, "PRZZZeroRowMellin.lean": 4, "PRZZZeroOuterMellin.lean": 7, "PRZZZeroNormalization.lean": 4, "PRZZZeroGapTime.lean": 5, "PRZZActualZeroReflection.lean": 4, "PRZZZeroCross.lean": 5, "PRZZZeroCoupled.lean": 4, "PRZZZeroGammaBound.lean": 6, "PRZZZeroFourierReduction.lean": 3, "PRZZAllOffDiagonalRows.lean": 6, "PRZZAllPoissonRows.lean": 4, "PRZZAllPoissonAFE.lean": 2, "PRZZResolvedComplement.lean": 4, "PRZZZeroExhaustionCross.lean": 4, "PRZZResolvedBoundary.lean": 3, "PRZZDualSmooth.lean": 3, "PRZZZeroDualExhaustion.lean": 4, "PRZZResolvedTail.lean": 2, "PRZZPartitionDiscrepancy.lean": 10, "PRZZOriginalSpatialLimit.lean": 3, "PRZZArithmeticBoundaryFamily.lean": 5, "PRZZNativeFamily.lean": 5, "PRZZNativeComponents.lean": 3, "PRZZNativeGcdGrid.lean": 6, "PRZZResolvedTailMass.lean": 3, "PRZZLargeSpatialKernel.lean": 6, "PRZZLargeSpatialFamily.lean": 3, "PRZZLargeSpatialHeight.lean": 3, "PRZZLargeResolvedPruning.lean": 4, "PRZZWindowGrids.lean": 4, "PRZZWindowTailMass.lean": 2, "PRZZWindowTailTime.lean": 5, "PRZZWindowNativeTail.lean": 7, "PRZZWindowBoundary.lean": 6, "PRZZValuedSourceDiscarded.lean": 1, "PRZZWindowErrorJoin.lean": 3, "PRZZDualTimeIBP.lean": 5, "PRZZDualDiscardedIBP.lean": 5, "PRZZExhaustiveAFEError.lean": 4, "PRZZSourceMaskFamily.lean": 7, "PRZZDualFirstJet.lean": 10, "PRZZDiscardedAFEBridge.lean": 6, "PRZZPolygammaSeries.lean": 11, "PRZZDualHigherJets.lean": 9, "PRZZDualJetTransfer.lean": 9, "PRZZDualJetMass.lean": 1, "PRZZDualDiscardedBudget.lean": 4, "PRZZDualWindowErrorJoin.lean": 2, "PRZZDiscardedTimePair.lean": 3, "PRZZPrunedAFEError.lean": 7, "PRZZRetainedNative.lean": 3, "PRZZNativeCentralLiteral.lean": 7, "PRZZKeptLiteral.lean": 4, "PRZZRejectedExhaustion.lean": 12, "PRZZArithmeticCutoffPartition.lean": 9, "PRZZSelectedLocalFourier.lean": 6, "PRZZLocalTailBudget.lean": 6, "PRZZFullFreezeBudget.lean": 4, "PRZZSpatialErrorJoin.lean": 4, "PRZZNativeFreezeEnvelope.lean": 5, "PRZZDualNativeFreeze.lean": 2, "PRZZNativeFreezeTime.lean": 4, "PRZZIntegratedFreezeAFE.lean": 6, "PRZZFreezeRemovedLiteral.lean": 5, "PRZZLiteralAFEJoin.lean": 4, "PRZZCompatibleTail.lean": 4, "PRZZResidualPartition.lean": 6, "PRZZBandOuterMass.lean": 10, "PRZZSpatialReconstruction.lean": 9, "PRZZSameMaskResidual.lean": 8, "PRZZReconstructedAFE.lean": 9, "PRZZSameMaskFreezeBudget.lean": 2, "PRZZStrictSmallTail.lean": 8, "PRZZSmallCentralLiteral.lean": 9, "PRZZSelectedDiscarded.lean": 9, "PRZZSelectedDiscardedFamily.lean": 11, "PRZZRemainderBudget.lean": 4, "PRZZRemainderAbsorption.lean": 4, "PRZZLiteralExhaustion.lean": 5, "PRZZLiteralTotalBound.lean": 2, "PRZZFourierExhaustion.lean": 6, "PRZZLiteralFourierLimit.lean": 5, "PRZZFullLiteralBound.lean": 1, "PRZZCentralArithmeticJoin.lean": 4, "PRZZCentralMainAssembly.lean": 9, "PRZZCentralGridWeilDI.lean": 5, "PRZZWeilDIMainBound.lean": 1, "PRZZDualProfileUniform.lean": 4, "PRZZMellinSeminorm.lean": 13, "PRZZDualMellinUniform.lean": 6, "PRZZArithmeticTailLimit.lean": 3, "PRZZNegativeArithmetic.lean": 6, "PRZZNegativeMellin.lean": 10, "PRZZNegativeOuter.lean": 2, "PRZZNegativeGrid.lean": 3, "PRZZZeroMismatchLimit.lean": 3, "PRZZIndexedCaps.lean": 4, "PRZZUniformTypeI.lean": 8, "PRZZUniformCases.lean": 6, "PRZZUniformAggregate.lean": 4, "PRZZUniformOuter.lean": 5, "PRZZUniformGrid.lean": 4, "PRZZZeroUniformHeight.lean": 4, "PRZZZeroSpatialHeight.lean": 4, "PRZZZeroOmittedGaps.lean": 6, "PRZZZeroOuterHeight.lean": 4, "PRZZZeroNativeTail.lean": 5, "PRZZZeroIntegerReindex.lean": 4, "PRZZZeroCompleteCell.lean": 4, "PRZZZeroDualHeight.lean": 5, "PRZZZeroBoundaryHeight.lean": 7, "PRZZZeroNativeCompletion.lean": 5, "PRZZZeroSpatialPrefix.lean": 8, "PRZZZeroArithmeticPartition.lean": 5, "PRZZZeroBoundarySum.lean": 3, "PRZZZeroBoundaryIdentity.lean": 9, "PRZZZeroDualBoundary.lean": 6, "PRZZZeroDualGaps.lean": 3, "PRZZZeroDualOuter.lean": 3, "PRZZZeroDualNativeTail.lean": 3, "PRZZZeroMismatchHeight.lean": 2, "PRZZWeilDIZeroJoin.lean": 3, "PRZZGammaBudgetAbsorption.lean": 3, "PRZZWeilDIErrorJoin.lean": 3, "PRZZSignedUniformGrid.lean": 2, "PRZZSignedMomentBudget.lean": 1, "PRZZLocalFrequencyLoss.lean": 9, "PRZZLocalCentralTransfer.lean": 7, "PRZZDisjointSpatialJoin.lean": 9, "PRZZArithmeticWindowCutoff.lean": 4, "PRZZWindowBandMass.lean": 11, "PRZZSubunitFourier.lean": 2, "PRZZSubunitWindowMass.lean": 11, "PRZZWideRowBudget.lean": 3, "PRZZWindowCentralAssembly.lean": 7, "PRZZWindowMoment.lean": 8, "PRZZWideActiveRows.lean": 4, "PRZZWindowScaleSupply.lean": 5, "PRZZWindowSpatialJoin.lean": 6, "PRZZWindowOptimalCell.lean": 3, "PRZZOuterLogBudget.lean": 5, "PRZZNegativeLocalRows.lean": 4, "PRZZPositiveOuterGrid.lean": 3, "PRZZNegativeRowWindow.lean": 3, "PRZZNegativeRowIntegral.lean": 4, "PRZZNegativeLiteralRows.lean": 3, "PRZZNegativeActiveRows.lean": 1, "PRZZNegativeWindowCell.lean": 2, "PRZZNegativeOuterGrid.lean": 1, "PRZZCommonSignedWindow.lean": 2, "PRZZCommonWindowCollector.lean": 3, "PRZZCommonCutMoment.lean": 2, "PRZZCommonResidualJoin.lean": 1, "PRZZActualTailNative.lean": 6, "PRZZActualTailCollector.lean": 6, "PRZZBodyTailMass.lean": 5, "PRZZBodyTailTime.lean": 3, "PRZZTailRowIntegrable.lean": 2, "PRZZNativeTailRectangle.lean": 2, "PRZZBodyTailCollector.lean": 3, "PRZZBodyTailOptimal.lean": 2, "PRZZMomentOptimal.lean": 1,
                "PRZZTimeJets.lean": {"scaled_bound", "term_deriv", "first_deriv", "jet_deriv", "iterated", "term_bound", "decay", "all_decay"},
                "PRZZTimeAmplitude.lean": {"uniform", "window_bound", "mass", "jet_support", "smooth", "compact", "jet_integrable", "mass_window", "coefficient_mass", "arithmetic_mass"},
                "PRZZDeltaDecay.lean": {"gap_le_log", "oscillatory_bound", "discarded_bound", "finite_discarded", "height_gain", "source_scale"},
                "PRZZPartitionMass.lean": {"piece_nonneg", "piece_norm", "piece_mass", "grouped_piece_mass", "integrated_boundary", "integrated_boundary_zero", "profile_scaled", "configuration_mass", "assembled_bound", "assembled_integral_zero", "timeCoefficient_norm", "gcd_time_cutoff", "cutoff_small_gap", "retained_configuration", "retained_mass", "gcd_cutoff_small_gap", "gap_split"},
                "PRZZSourceBoundaryDecay.lean": {"cutoff_cap", "source_bound", "source_pointwise", "majorant_summable", "tail_nonneg", "tail_zero", "boundary_bound", "row_bound", "family_boundary", "boundary_tendsto", "positive_square", "boundary_integer", "poisson_boundary"},
                "PRZZWArithmeticCutoff.lean": {"kernel_bound", "arithmetic_bound", "term_measurable", "weighted_cutoff_removed", "mollified_cutoff_removed", "source_term_bound"},
                "PRZZUnitModulusBudget.lean": {"scales", "sum_shift_envelopes", "source_tail_absorbed", "actual_tail_absorbed", "retained_conditions", "integrated"},
                "PRZZUnitTailMass.lean": {"retained_support", "summed", "integrated"},
                "PRZZSourceWindowCutoff.lean": {"endpoints", "boundary_zero"},
                "PRZZSourceLattice.lean": {"lattice", "source_delta", "source_support", "sharp_source", "boundary_split", "source_boundary", "boundary_scale"},
                "PRZZFrozenFamilyCutoff.lean": {"family_stable", "remainder_stable", "time_stable", "source_cutoff_not_sufficient"},
                "PRZZAFEOuterAssembly.lean": {"partition_explicit", "literal_partition", "label_count", "outer_sum", "outer_absorbed", "outer_time_absorbed"},
                "PRZZSourceTailMass.lean": {"retained_support", "retained_domain", "summed", "integrated"},
                "PRZZTransformedSourceBudget.lean": {"scales", "sum_shift_envelopes", "source_tail_absorbed", "actual_tail_absorbed", "retained_conditions", "integrated"},
                "PRZZProfileTimeBudget.lean": {"time_scales", "time_mass", "local_absorbed", "full_tail_absorbed"},
                "PRZZFrozenProfileBound.lean": {"actual_tail", "local_weighted_mass", "dual_weighted_mass"},
                "PRZZExpandedCutoff.lean": {"central_extend", "poisson_expand", "rows_extend", "rows_remainder", "mass_time", "original_remainder_bound"},
                "PRZZInverseProfile.lean": {"support", "smooth", "compact", "jets", "weight_absorb_pos", "weight_absorb", "fourier_absorb", "frozen_profile_fourier", "uniform_transformed_tail", "rounded_cutoff_gain", "rounded_tail_budget"},
                "PRZZSharpPoisson.lean": {"support_retained", "sharp_eq_progression", "active_small", "sharp_frozen", "sharp_frozen_stable", "active_phase", "active_phase_sum"},
                "PRZZCentralTail.lean": {"integer_split", "mode_summable", "poisson_split", "signed_mode", "all_rows", "all_rows_time", "signed_phase_integral"},
                "PRZZIntegratedDefect.lean": {"replacement_integrable", "zeta_continuous", "residue_integrable", "integral_eq", "scaled_target"},
                "PRZZFrozenTail.lean": {"phase_norm", "pair_eq", "time_swap", "frozen_dilation", "jacobian_dilation", "frozen_fourier"},
                "PRZZResidueAbsorption.lean": {"gaussian_budget", "scalar_absorbed", "combined_target"},
                "PRZZDualError.lean": {"multiplier_ratio", "multiplier_bound", "multiplier_scaled_cap", "dual_scaled_target", "two_sided_defect", "replacement_residue_target", "dilation_cap", "multiplier_dilation_cap", "dual_power_pair_mass", "dual_dilated_pair_mass"},
                "PRZZResidueTime.lean": {"noncentral_bound", "weighted_bound", "window_envelope", "envelope_integral", "direct_afe_defect", "scaled_combined", "scaled_combined_explicit"},
                "PRZZScaledReplacement.lean": {"shifts_eventually", "singular_absorbed", "scaled_target", "cutoff_target"},
                "PRZZMeanSquare.lean": {"phase_norm", "phase_integral", "summand", "mean_nonneg", "replacement_mean", "phase_pair", "exponential_gram", "exponential_mean_bound", "polynomial_expansion", "log_gap", "polynomial_mean", "normalized_norm", "bounded_mean", "source_mean", "replacement_source", "mean_scale_target", "replacement_target"},
                "PRZZProductTime.lean": {"term_measurable", "rectangles_integral", "weighted_cutoff_removed", "mollified_cutoff_removed", "source_bound", "source_absorbed", "difference_integral"},
                "PRZZProductMass.lean": {"hyperbola_card", "cutoff_product", "cutoff_stable", "direct_coefficient", "localized_mass", "actual_mass"},
                "PRZZProductSummation.lean": {"monomial", "global_bound", "coefficient_time", "arithmetic_bound", "summed_bound", "cutoff_removed", "integrated_bound"},
                "PRZZActualSmallReplacement.lean": {"cutoff_finite", "all_rows", "all_rows_time", "mass_factorized", "factorized_time"},
                "PRZZDifferenceDecay.lean": {"power_bound", "gamma_cap", "ratio_strip_bound", "tail_bound"},
                "PRZZDifferenceContour.lean": {"vertical_continuous", "vertical_integrable", "horizontal_tendsto", "integral_shift", "difference_shifted"},
                "PRZZDifferenceRegular.lean": {"finite_rectangle", "regular_analytic", "pole_free_strip", "denominator_nonzero", "numerator_zero", "numerator_analytic", "regular_analytic_zero", "regular_eq", "on_original_line"},
                "PRZZActualLocalReplacement.lean": {"term_difference", "all_rows", "grouped_mass", "coefficient_norm", "mass_time_independent", "all_rows_time"},
                "PRZZLocalReplacement.lean": {"local_bound", "finite_bound", "height_scale_bound", "cutoff_scale", "cutoff_finite_bound", "cutoff_time_bound"},
                "PRZZTruncatedProgression.lean": {"reconstruct", "progression_bounds", "weighted_sum", "actual_weight"},
                "PRZZReplacementHeight.lean": {"cost_lower", "cost_upper", "weighted_cost", "integrated_source_height"},
                "PRZZCongruencePoisson.lean": {"congruence_iff", "progression_iff", "truncated_progression", "astar_residue_phase", "poisson_signed", "fibre_progression", "signed_phase_error"},
                "PRZZReplacementMass.lean": {"reciprocal_sqrt_sum", "polynomial_bound", "source_weight_bound", "integrated_source"},
                "PRZZPoissonActualWeight.lean": {"frozen_identity", "literal_frozen", "prefactor_norm", "literal_arithmetic_bound", "frozen_poisson"},
                "PRZZKloostermanInputs.lean": {"WeilPrime", "WeilIncomplete", "DeshouillersIwaniecLemma1"},
                "PRZZLambda.lean": {"generalizedLambda_succ", "generalizedLambda_decomposition", "generalizedLambda_two"},
                "PRZZHeathBrown.lean": {"remainder_small", "pow_vanish_below", "heathBrown_remainder",
                    "heathBrown", "heathBrown_binomial"},
                "PRZZWeightedHeathBrown.lean": {"weight_mul", "expand_eq_weight", "allocationCoeff_sum",
                    "log_product_multinomial", "heathBrown_weighted", "root_cutoff_range", "heathBrown_weighted_real"},
                "PRZZTypeI.lean": {"incomplete_eq_range", "abel_bound", "weighted_bound"},
                "PRZZTypeII.lean": {"diSum_const_mul", "di_bound_scaled", "block_le_diSum",
                    "block_bound", "negativeBlock_eq", "two_sided_bound"},
                "PRZZDyadic.lean": {"mem_cell", "sum_partition", "crossing", "classify", "box_sum_bound"},
                "PRZZMobiusHeathBrown.lean": {"moebius_binomial", "truncated_factor_small"},
                "PRZZMellinSeparation.lean": {"twist_mul", "inversion", "separate", "sum_separate",
                    "integral_budget", "scaled_mellin", "scaled_verticalIntegrable", "scaled_mellin_mass"},
                "PRZZTypeIWeights.lean": {"source_hasDerivAt", "source_derivative_bound", "variation_le", "sampled_step"},
                "PRZZMellinTypeII.lean": {"sum_indices", "separated_sum", "twisted_continuous",
                    "coupled_eq_integral", "coupled_bound"},
                "PRZZSmoothMellin.lean": {"logPull_support", "logPull_compact", "vertical_integrable",
                    "mellin_convergent", "rapid_decay", "scaled_rapid_decay", "scaled_suppliers", "coupled_bound_smooth"},
                "PRZZSmoothWeights.lean": {"scaled_hasDerivAt", "scaled_deriv", "cutoff_bounds", "source_bound_uniform"},
                "PRZZGcdAverage.lean": {"sum_multiples", "common_divisors", "gcd_sum", "gcd_sum_le",
                    "coprime_indicator", "coprime_sum"},
                "PRZZDyadicArithmetic.lean": {"sum_restrict", "convolution_dyadic", "weighted_coprime_convolution"},
                "PRZZTypeIFrequency.lean": {"gcd_sum_real", "positive_frequency_bound"},
                "PRZZSourceTypeII.lean": {"coprimeCoeff_norm", "sourceSum_eq", "sourceSum_bound"},
                "PRZZDIExpansion.lean": {"radical_bound", "seven_identity", "diBound_seven", "sourceSum_seven"},
                "PRZZGCoefficient.lean": {"coefficient_eq", "coefficient_bound", "sourceG_bound", "sourceG_average", "sourceG_seven_average"},
                "PRZZEulerSubpower.lean": {"local_eventually", "eulerMass_subpower", "sourceG_average_subpower", "sourceG_seven_subpower"},
                "PRZZGAbsorption.lean": {"log_pow_bound", "sourceG_average_power", "sourceG_seven_power"},
                "PRZZCoprimeAllocation.lean": {"primePower_coprime_split", "weightedLambda_mul_coprime", "mu_mul_coprime", "weighted_product_allocation"},
                "PRZZConvolutionSplit.lean": {"sum_coprime", "convolution_coprime", "coefficient_cons_coprime", "coefficient_cons_split"},
                "PRZZAStar.lean": {"literal_eq_sum_integrals", "literal_eq_integral_sum", "innerKernel_zero_of_nonpos", "delta_cutoff_iff", "h_cutoff_iff"},
                "PRZZCoefficientSeparation.lean": {"coefficient_separation", "source_coefficient_separation", "allocations_length"},
                "PRZZAStarIntegrability.lean": {"inner_integrable", "kernel_integrable_y", "literal_eq_integral_sum_of_cutoff"},
                "PRZZAStarMellin.lean": {"kernel_amplitude", "finite_integrand_mellin"},
                "PRZZAStarFubini.lean": {"kernel_integrable", "outer_integrable", "kernel_integral_swap", "literal_eq_integral_sum"},
                "PRZZAStarFrequency.lean": {"kernel_phase", "regroup", "literal_regroup", "residual_separated"},
                "PRZZWindowWeight.lean": {"window_bound", "twisted_window_bound"},
                "PRZZAStarWindow.lean": {"support_window", "indicator_kernel", "literal_window"},
                "PRZZWindowDominance.lean": {"joint_integrable", "mellin_swap"},
                "PRZZNuCoefficient.lean": {"separate", "oscillation_norm", "nu_norm_le_card",
                    "fiber_card_le_divisors", "nu_norm_le_divisors"},
                "PRZZActualMellin.lean": {"amplitude_continuous", "localized_integrable", "localized_swap", "finite_swap", "localized_bound"},
                "PRZZAStarTransform.lean": {"kernel_inversion", "literal_mellin"},
                "PRZZNuBounds.lean": {"divisors_subpower", "nu_subpower", "positive_rectangle_bound"},
                "PRZZAStarNu.lean": {"amplitude_nu", "localized_nu", "literal_mellin_nu",
                    "frequency_positive_h", "frequency_ne_zero", "source_nu_bound", "source_positive_rectangle_bound"},
                "PRZZSignedTypeII.lean": {"sourcePlus_conj", "sourcePlus_eq", "signedSource_bound"},
                "PRZZAStarRectangles.lean": {"pair_partition", "rectangle_separated", "signedSum_rectangles"},
                "PRZZAStarIntegralBound.lean": {"common_integrable", "literal_bound", "literal_bound_of_rectangles"},
                "PRZZFullHeathBrown.lean": {"fullExpansion_product", "convolution_congr_below",
                    "coefficient_eq_fullExpansion", "rectangle_congr_coeff", "rectangle_heathBrown", "rectangle_heathBrown_root"},
                "PRZZOuterMass.lean": {"ratio_mem", "log_bound", "inv_power_bound",
                    "window_volume_bound", "common_mass_uniform", "literal_uniform"},
                "PRZZGroupedConvolution.lean": {"weighted_convolution", "regroup_factors", "factor_sum", "boxed_weighted"},
                "PRZZGroupedDI.lean": {"grouped_eq", "grouped_bound"},
                "PRZZGroupBounds.lean": {"atom_weight_bound", "atom_subpower", "convolution_bound",
                    "group_subpower", "masked_twisted_group", "rectangle_envelope"},
                "PRZZSharpCutoff.lean": {"phase_norm", "phase_integral", "comparison", "product_comparison",
                    "sharp_eq", "cost_nonneg", "kernel_geometric", "kernel_decay", "kernel_norm_le", "cost_le", "sharp_bound"},
                "PRZZSharpCost.lean": {"density_even", "denominator_lower", "density_inv_bound",
                    "cost_interval", "cost_half", "cost_log"},
                "PRZZTypedClassification.lean": {"large_free", "classify_typed", "orient_groups"},
                "PRZZHBAtomSupply.lean": {"weighted_supply", "mu_supply", "lambda_supply",
                    "branches_supply", "branch_large_free", "branch_classify"},
                "PRZZSharpGrouped.lean": {"grouped_eq", "factor_grouped_eq"},
                "PRZZDyadicSupport.lean": {"mul_support", "restrict_support", "group_support",
                    "upper_box_factor", "sharp_shrink", "dyadic_grouped_eq"},
                "PRZZTypeIVariation.lean": {"sampled_variation", "source_variation"},
                "PRZZBranchGrouping.lean": {"factor_prod", "subset_product", "branch_grouped", "classify_branch"},
                "PRZZSourceEnvelope.lean": {"exponent_re", "power_log", "source_variation_uniform", "source_weil"},
                "PRZZGroupedSeven.lean": {"grouped_seven"},
                "PRZZSourceAbsorption.lean": {"finite_log_powers", "exponent_norm", "budget_absorbed", "source_weil_absorbed"},
                "PRZZBranchDegrees.lean": {"weighted_degrees", "branches_degrees", "branch_large_free_degrees", "branches_length"},
                "PRZZBranchEnvelope.lean": {"bounded_atom", "bounded_product", "all_branch_subgroups", "masked_branch_subgroups", "branch_rectangle"},
                "PRZZBranchSeven.lean": {"signed_branch_seven"},
                "PRZZSourceCoefficients.lean": {"signed_nu", "inverse_shift", "second_coefficient", "second_coefficient_scaled", "source_branch_seven"},
                "PRZZBranchMass.lean": {"weighted_weights", "branches_weights", "mass_eq", "sum_bound", "mixed_unscaled", "pair_sum_bound"},
                "PRZZDyadicBudget.lean": {"cell_count", "grids_absorbed", "grid_card", "support_inflation", "branch_pair_grids"},
                "PRZZLiteralBranches.lean": {"literal_branches"},
                "PRZZSupportedSplit.lean": {"supported_coprime", "exists_split", "split_unique", "sum_split", "source_allocation", "mem_hSupport", "sum_cutoff"},
                "PRZZSupportedBranches.lean": {"mixed_row", "mixed_supported", "rectangle_supported", "literal_supported"},
                "PRZZSupportedAllocation.lean": {"weighted_source", "residual_average"},
                "PRZZSupportedSource.lean": {"row_factor", "rectangle_allocated", "signedSum_allocated", "rectangle_average", "literal_uniform_allocated"},
                "PRZZResidualCoprime.lean": {"restrict_mul", "restrict_norm", "weighted_residual", "grouped_restricted"},
                "PRZZWeightedDI.lean": {"weighted_eq", "sharp_zero", "weighted_bound", "weighted_seven", "negative_eq", "signed_seven"},
                "PRZZResidualWeighted.lean": {"grouped_eq", "weighted_shrink", "grouped_seven"},
                "PRZZResidualRow.lean": {"row_eq", "row_seven"},
                "PRZZResidualBoxes.lean": {"support", "balanced_box", "dyadic_eq", "dyadic_seven"},
                "PRZZMaskedVariation.lean": {"mask_step", "mask_variation", "mask_of_variation"},
                "PRZZMaskedSource.lean": {"source_uniform"},
                "PRZZRowWindow.lean": {"test", "weight_eq", "weight_bound"},
                "PRZZMellinMoment.lean": {"polynomial_integrable", "linear_mass"},
                "PRZZLinearOuter.lean": {"literal_linear_bound", "literal_linear_uniform", "literal_linear_h_blocks"},
                "PRZZActualBranchCells.lean": {"group_split", "witnesses", "classify", "common_envelope", "common_rectangle", "group_support", "balanced_support", "weighted_group_split"},
                "PRZZActualBranchDI.lean": {"signed_group_seven"},
                "PRZZSourceScales.lean": {"smaller_balanced", "upper_product", "oriented_boxes", "quarter_conditions", "local_root_short", "local_root_quarter", "local_layout"},
                "PRZZInflatedSeven.lean": {"power_bound", "seven_balanced", "seven_h_bound"},
                "PRZZMaskedAbsorption.lean": {"source_absorbed"},
                "PRZZInflatedOuter.lean": {"source_h_sum", "literal_variation_blocks"},
                "PRZZLocalReexpansion.lean": {"local_coefficient", "change_cutoff", "masked_sum", "row_sum"},
                "PRZZSmallRowVariation.lean": {"supported_variation", "actual_row", "small_scale", "actual_small_row"},
                "PRZZActualRowSmooth.lean": {"analytic_factor", "variation_const", "sampled_eq", "sampled_variation", "small_scaled", "selected_variation"},
                "PRZZSplitScaleSum.lean": {"absolute_mass", "mixed_sum"},
                "PRZZSplitScaleOuter.lean": {"literal_mixed", "rows_sum"},
                "PRZZRowPlacement.lean": {"upper_le", "narrow", "placement", "empty_row", "retained_variation"},
                "PRZZAllBranchCells.lean": {"factor_partition", "product_local", "branch_cells", "weighted_branch", "all_weighted", "local_all"},
                "PRZZActualSupportBoxes.lean": {"bounds", "vanishes", "rectangle"},
                "PRZZSourceGroupDI.lean": {"source_seven"},
                "PRZZZeroExtension.lean": {"prepend", "zero_tail", "zero_prefix", "supported", "head_le", "actual", "full_variation", "weil_row"},
                "PRZZActualRowRectangle.lean": {"split", "coefficient_eq", "shrink_local", "row_eq"},
                "PRZZWholeRowsSum.lean": {"rows_sum", "literal_rows"},
                "PRZZPositiveRow.lean": {"grouped_eq", "source_row_eq", "negative_shrink_local", "actual_row_eq"},
                "PRZZCellAggregation.lean": {"scalar", "grid_bound", "local_bound"},
                "PRZZSignedSourceCell.lean": {"source_eq", "source_seven"},
                "PRZZTypeICoprime.lean": {"divisor_rows", "coprime_divisor_rows"},
                "PRZZInversePhase.lean": {"e_add_int", "phase_mod", "inverse_product", "phase_product", "restricted_eq", "restricted_bound"},
                "PRZZEffectiveBalance.lean": {"scale_le", "clipped", "local_layout", "seven_decay"},
                "PRZZEffectiveAverage.lean": {"source_h_sum", "literal_actual_boxes"},
                "PRZZTypeICost.lean": {"inverse_coprime", "frequency_gcd", "prefix_bound", "weighted_bound", "actual_bound", "frequency_bound", "divisor_pair_absorbed", "actual_frequency_bound"},
                "PRZZAllocatedCells.lean": {"residual_eq", "signedSum_eq", "literal_bound"},
                "PRZZRowCellLayout.lean": {"cutoff_le", "actual_layout", "row_expansion", "retained_sample"},
                "PRZZCommonCellBound.lean": {"source_bound"},
                "PRZZHiAllocatedCells.lean": {"row_vanish", "residual_eq", "signedSum_eq", "literal_bound"},
                "PRZZCellMass.lean": {"upper_support", "small_support", "typeI_support", "weighted_mass", "supported_sum"},
                "PRZZFreeLogRow.lean": {"sample_eq", "variation_bound", "weil_bound", "multiplier_le", "retained_variation"},
                "PRZZFreeLogCoprime.lean": {"shift_eq", "full_variation", "frequency_bound", "small_variation"},
                "PRZZFreeSource.lean": {"slice_eq", "slice_frequency_gcd"},
                "PRZZFreeDyadic.lean": {"point_le", "dyadic_mask", "variation_bound", "transformed_bound", "slice_bound"},
                "PRZZBareFactors.lean": {"branches_bare", "large_log_power", "large_piece", "classify"},
                "PRZZFreeCoefficient.lean": {"modulusBudget_nonneg", "slice_bound", "nu_slice_bound", "signed_slice_bound"},
                "PRZZFreeCell.lean": {"real_convolution", "cell_eq", "signed_cell_bound"},
                "PRZZAllocationMass.lean": {"grid_mass", "allocation_mass", "weighted_allocation_mass"},
                "PRZZModulusBudget.lean": {"weighted_gcd", "positive_budget", "signed_budget", "source_range", "source_budget", "averaged_absorbed", "signed_cell_averaged"},
                "PRZZFreeLength.lean": {"vanishes", "restrict_eq", "supported_bound", "transformed_bound"},
                "PRZZFreeLengthCoefficient.lean": {"budget_nonneg", "budget_mono", "endpoint_le", "slice_bound", "nu_slice_bound", "signed_slice_bound"},
                "PRZZLeftCentral.lean": {"exponent_budget", "line_ne_zero", "inverse_bound", "annihilator_line", "gaussian_line", "central_bound"},
                "PRZZLeftFar.lean": {"shifted_quotient_uniform", "actual_ratio_uniform", "far_core_uniform", "far_bound"},
                "PRZZLeftUniform.lean": {"integrand_uniform", "difference_uniform", "scale_cost", "small_product_bound", "scaled_small_product"},
                "PRZZFreeLengthCell.lean": {"signed_cell_bound"},
                "PRZZLengthBudget.lean": {"positive_budget", "signed_budget", "source_range", "source_budget", "signed_cell_averaged"},
                "PRZZModulusScale.lean": {"cell_card", "averaged_scale", "typeI_scale", "actual_product", "actual_averaged_typeI"},
                "PRZZTypeIScaleSupplier.lean": {"signed_cell", "retained_root_short"},
                "PRZZDyadicModulus.lean": {"bound_pos", "second_zero", "weighted_restrict", "negative_restrict", "source_eq_dyadic", "source_seven_dyadic"},
                "PRZZDyadicCellBound.lean": {"source_bound"},
                "PRZZMixedOuter.lean": {"mixed_sum", "literal_mixed"},
                "PRZZActualSignedBranches.lean": {"nu_zero", "frequency_pair", "sum_list", "cells_eq_sources"},
                "PRZZAllSignedSources.lean": {"signedCells_eq", "signedSum_eq", "blocks_bound"},
                "PRZZRetainedScale.lean": {"retained_scale", "balanced_boxes"},
                "PRZZAllCellsBound.lean": {"outer_sum_bound", "allocation_bound"},
                "PRZZSignedCellsAggregate.lean": {"signedCells_bound", "signedSum_bound", "literal_bound"},
                "PRZZDyadicWindow.lean": {"support_box", "indicator_kernel", "support_box_of_cutoffs",
                    "literal_box", "volume_bound", "mass_bound", "dyadic_swap"},
                "PRZZGaussianLine.lean": {"gaussian_integrable", "gaussian_integral", "power_exp",
                    "mellin_gaussian_integral"},
                "PRZZWindowComposition.lean": {"literal_windowed", "literal_windowed_nu"},
                "PRZZGaussianTail.lean": {"laplace_integral", "joint_integrable", "pole_integral", "pole_integrable"},
                "PRZZGaussianCorrection.lean": {"moment_integrable", "moment_integral"},
                "PRZZSourceW.lean": {"source_integrable", "sourceW_eq", "tail_bounds", "correction_bound",
                    "sourceW_bound", "sourceW_scaled_bound"},
                "PRZZSourceWOuter.lean": {"tail_continuous", "sourceW_continuous", "actual_mass",
                    "envelope_absorbed", "actual_mass_absorbed", "restricted_mass"},
                "PRZZPositiveMellin.lean": {"kernel_integrable_positive", "amplitude_continuous_positive",
                    "localized_integrable_positive", "finite_swap_positive", "literal_mellin_positive",
                    "literal_windowed_positive", "literal_windowed_nu_positive", "sourceW_literal_windowed_nu"},
                "PRZZBalancedCellEnvelope.lean": {"balanced_source_bound"},
                "PRZZActualBudgetLayout.lean": {"typeI_inflate", "actual_budget_layout", "actual_source_bound",
                    "retained_typeI_decay", "small_retained_threshold"},
                "PRZZActualTypeI.lean": {"source_eq_signed", "source_bound", "retained_source_bound"},
                "PRZZActualSmall.lean": {"row_bound", "small_cell", "small_source"},
                "PRZZActualCases.lean": {"complementary_support", "retained_source_bound",
                    "source_zero", "bound_of_retained", "source_bound"},
                "PRZZActualCaseSum.lean": {"largeBudget_linear", "budget_linear_le", "supported_source_bound"},
                "PRZZActualAggregate.lean": {"row_nonneg", "actual_blocks", "totalBudget_nonneg", "signedSum_bound"},
                "PRZZPositiveOuter.lean": {"common_integrable_positive", "literal_linear_positive"},
                "PRZZActualAStar.lean": {"literal_sourceW_bound"},
                "PRZZOptimalPowers.lean": {"scale_identity", "mixed_power", "seven_term_bound", "seven_bound",
                    "typeI_bound", "combined_bound", "frequency_bound", "source_frequency_bound",
                    "small_frequency_bound", "clipped_frequency_bound"},
                "PRZZActualCasePowers.lean": {"row_normalized", "cutoff_row_scale", "cutoff_frequency",
                    "row_nonzero_cutoffs", "nonzero_row_frequency"},
                "PRZZActualRowOuter.lean": {"mass_row_bound"},
                "PRZZL1Finite.lean": {"direct_expansion", "diagonal_split"},
                "PRZZOptimalOuter.lean": {"source_mass_budget", "finite_source_mass_budget", "power_log_absorbed"},
                "PRZZOriginalRowWindow.lean": {"row_indicator", "row_integral_window", "row_mellin_window", "row_iterated_eq"},
                "PRZZActualLoss.lean": {"common_power", "common_absorbed", "common_aggregation_absorbed"},
                "PRZZRowMellinBranches.lean": {"signedRow_blocks", "row_amplitude", "row_localized", "row_mellin_blocks"},
                "PRZZLiteralRows.lean": {"index_partition", "literal_rows", "literal_windowed_blocks"},
                "PRZZThreeCaseLoss.lean": {"typeI_absorbed", "small_absorbed", "three_case_absorbed", "normalized_row_absorbed"},
                "PRZZNonemptyRowBudget.lean": {"original_mass", "nonempty_row_absorbed", "allocation_dyadic_absorbed"},
                "PRZZRowIntegralBudget.lean": {"row_integral_bound", "rowBudget_nonneg", "signedRow_bound", "literal_row_budgets", "literal_sourceW_rows"},
                "PRZZActiveRows.lean": {"active_witness", "inactive_integral", "active_budget_absorbed", "literal_absorbed"},
                "PRZZSourceFrequency.lean": {"indices_empty", "literal_zero", "frequency_rounding", "frequency_source_bound", "empty_or_source_frequency", "log_scale_of_power_bounds", "row_log_scale"},
                "PRZZL1Residue.lean": {"residue_iff", "progression_residue", "poisson_inverse_progression"},
                "PRZZSourceCutoffs.lean": {"cutoff_product", "empty_or_frequency", "tail_ratio", "exists_tail_order"},
                "PRZZSourceDecay.lean": {"gaussian_linear_bound", "tail_exp_bound", "correction_exp_bound", "sourceW_decay", "tail_hasDerivAt"},
                "PRZZGaussianDerivatives.lean": {"weighted_hasDerivAt", "weighted_iterated", "tail_iterated", "correction_iterated", "weighted_integrable", "tail_derivatives_integrable", "correction_derivatives_integrable", "weighted_cutoff_removed", "weighted_integral"},
                "PRZZLogDerivatives.lean": {"scaled_hasDerivAt", "ordinary_iterated", "monomial_decay", "weighted_decay", "ordinary_decay", "tail_ordinary", "tail_ordinary_decay"},
                "PRZZSourceWDerivatives.lean": {"source_hasDerivAt", "jet_hasDerivAt", "source_iterated", "source_derivative_decay", "source_all_decay", "source_scaled_decay"},
                "PRZZSourceWSums.lean": {"sampled_bound", "sampled_summable", "sampled_cutoff_removed", "sampled_tail_tendsto", "sampled_absolute_tail"},
                "PRZZAFEGamma.lean": {"digamma_error", "gamma_argument_error"},
                "PRZZGammaPath.lean": {"gamma_analytic", "ratio_eq_exp_integral", "integrated_error", "ratio_with_error"},
                "PRZZGammaCentral.lean": {"log_segment_bound", "ratio_reference_error", "log_scaled_shift_bound", "log_scaled_shifts_eventually", "log_vertical_reference", "actual_log_comparison"},
                "PRZZGammaMain.lean": {"single_factor_strip", "ratio_main_error_strip", "ratio_relative_bound_strip", "single_factor", "reference_phases", "main_phase", "ratio_main_error", "ratio_relative_bound"},
                "PRZZGammaUniform.lean": {"real_gamma_cap", "shifted_quotient_uniform", "actual_ratio_uniform", "far_core_uniform"},
                "PRZZCentralIntegral.lean": {"exponent_budget", "central_integrand_bound", "majorant_integrable", "central_integral_bound"},
                "PRZZKernelUniform.lean": {"far_integral_uniform", "difference_uniform", "scaled_difference"},
                "PRZZActualDirectSum.lean": {"main_envelope", "actual_envelope", "denominator_one", "direct_summable_of_envelope", "actual_summable", "actual_cutoff_removed", "directTerm_sub", "finite_replacement", "actual_finite_replacement", "main_summable", "infinite_replacement", "actual_absolute_tail", "dual_summable"},
                "PRZZAFEDual.lean": {"reflected_arguments", "gammaPair_formula", "dualMultiplier_formula", "completed_reflection", "gammaPair_ne_zero", "zeta_product_reflection", "annihilator_reflection", "contourNumerator_zero", "central_residue", "contour_reflection", "contour_integrand_reflection", "offDiagonal_residue", "offDiagonal_inverse", "offDiagonal_poisson"},
                "PRZZContourKernel.lean": {"gammaRatio_pair", "completed_factor", "numerator_eq_actual", "contour_differentiable", "completedPair_pole_expansion"},
                "PRZZKernelTime.lean": {"joint_continuous", "uniform_space_majorant", "bounded_time_majorant", "time_mellin_integrable", "time_mellin_swap", "kernel_time_integral"},
                "PRZZArithmeticTime.lean": {"kernel_measurable", "kernel_window_bound", "weighted_time_swap", "actual_time_swap"},
                "PRZZMollifiedTime.lean": {"polynomial_continuous", "mollifierWeight_continuous", "gammaPair_continuous", "dualMultiplier_continuous", "direct_mollified_swap", "dual_mollified_swap", "cutoff_integral", "direct_full_time_swap"},
                "PRZZCompletedStrip.lean": {"gammaR_bound", "right_bound", "strip_bound", "residue_factors", "actual_residue_factors"},
                "PRZZResidueEnvelope.lean": {"inverse_gammaR_uniform", "inverse_pair_uniform", "residue_envelope", "actual_left_residues", "actual_right_residues"},
                "PRZZHorizontalDecay.lean": {"horizontal_bound", "majorant_tendsto", "horizontal_integral_tendsto"},
                "PRZZFiniteContour.lean": {"principal_part_of_limit", "pole_limit_exists", "principal_parts", "poles_interior", "finite_rectangle"},
                "PRZZNoncentralResidues.lean": {"shifted_residue_zero", "shifted_residue_one", "weight_continuous", "product_residue_zero", "product_residue_one", "contour_eq_product", "actual_residues", "arguments_separated", "small_shift_residues"},
                "PRZZInfiniteContour.lean": {"vertical_continuous", "vertical_integrable", "vertical_limit", "infinite_rectangle"},
                "PRZZContourAFE.lean": {"left_integral", "central_value", "contour_afe"},
                "PRZZSeriesAFE.lean": {"shifted_summable", "contour_series", "term_eq", "term_integral", "term_bound", "summable_integral_norm", "positiveIntegral_series", "series_afe"},
                "PRZZIntegratedAFE.lean": {"weighted_integrable", "mollified_afe"},
                "PRZZReplacementIntegral.lean": {"series_bound", "actual_series_bound", "weighted_bound"},
                "PRZZPhaseError.lean": {"exp_phase_lipschitz", "log_remainder", "phase_error", "offDiagonal_error", "finite_error", "weighted_finite_error"},
                "PRZZPoissonSpatial.lean": {"kernel_scaled", "spatial_integral"},
                "PRZZCutoffPhase.lean": {"height_eventually", "ratio_bound", "support_ratio", "support_small", "mass_bound", "source_finite_error"},
                "PRZZPoissonWDerivative.lean": {"quadratic_hasDerivAt", "quadratic_scaled_decay", "cutoff_scaled_decay"},
                "PRZZArithmeticMass.lean": {"pair_bound", "mass_bound", "weighted_mass_bound", "phase_mass_bound"},
                "PRZZFullWeightSmooth.lean": {"source_smooth", "weight_eq", "weight_smooth", "weight_iterated_smooth", "weight_derivative_bound"},
                "PRZZDyadicArithmeticMass.lean": {"cell_card", "reciprocal_mass", "pair_mass", "weighted_pair_mass", "scaled_cutoff_pair_mass", "dilated_weighted_pair_mass"},
                "PRZZCutoffJets.lean": {"jet_support", "scaled_jet", "ordinary_uniform", "scaled_uniform", "scaled_leibniz"},
                "PRZZQuadraticJets.lean": {"term_deriv", "first_deriv", "jet_deriv", "iterated", "term_bound", "decay", "all_decay", "scaled_shifts", "scaled_bound"},
                "PRZZReciprocalJets.lean": {"term_deriv", "iterated", "phase_norm", "bound", "scaled_bound", "envelope_nonneg"},
                "PRZZPowerJets.lean": {"jet_deriv", "iterated", "scaled_norm"},
                "PRZZFullWeightJets.lean": {"product_bound", "uniform", "ordinary_uniform"},
                "PRZZWeightFourier.lean": {"support_subset", "compact", "smooth", "jet_support", "jet_zero", "jet_integrable", "fourier_jet", "norm_fourier_le", "mass_on_support", "fourier_bound", "mass_uniform"},
                "PRZZWeightTail.lean": {"square_summable", "tail_majorant", "tail_of_bound", "actual_tail", "uniform_tail"},
                "PRZZSourceTailBudget.lean": {"phase_radius", "source_mass", "finite_norm_bound", "weighted_time_bound", "arithmetic_time", "arithmetic_time_compact"},
                "PRZZEnvelopeMass.lean": {"convolution_nonneg", "convolution_mono", "cap_nonneg", "envelope_le_cap", "integral_cap", "support_log", "mass_bound", "tail_bound", "source_tail"},
                "PRZZJetUniform.lean": {"power_coeff", "phase_polynomial", "shift_cost", "cap_uniform"},
                "PRZZNormalizedTail.lean": {"normalized_budget", "normalized_tail", "arithmetic_time", "uniform_tail", "tail_arithmetic_time"},
                "PRZZPhaseDegree.lean": {"degree_bound", "phase_order", "phase_height", "cutoff_gain", "cutoff_absorbed", "convolution_growth", "cap_phase_growth", "source_modulus", "normalized_shape"},
                "PRZZZeroPhaseBudget.lean": {"base_nonneg", "zero_cap", "zero_cap_power", "absorbed"},
                "PRZZTailSourceFamily.lean": {"quadratic_scale", "modulus_scale", "window_log", "shift_envelopes", "source_absorbed"},
                "PRZZExtendedTailDomain.lean": {"nonempty_scale", "scales", "window_log", "shift_envelopes", "source_absorbed", "index_time"},
                "PRZZPrunedTailRows.lean": {"prune", "afe_prune", "active_scale", "all_rows"},
                "PRZZAbsorbedFourierTail.lean": {"normalized_cap", "source_tail"},
                "PRZZTailTimeSum.lean": {"finite_le", "domain_of_active", "integrated"},
                "PRZZArithmeticFourierTail.lean": {"pair_integrated", "time_swap"},
                "PRZZFourierTime.lean": {"source_measurable", "joint_measurable", "fourier_measurable", "uniform_fourier", "term_domination", "actual_swap", "residue_norm", "source_swap"},
                "PRZZSourceRows.lean": {"pair_prune", "domain", "integrated", "time_swap"},
                "PRZZInfiniteTail.lean": {"infinite_le", "source_bound", "outer_sum", "integrated"},
                "PRZZAFEIndices.lean": {"grouped", "direct_grouped", "mass_exact", "reduced_rows", "reciprocal_total", "grouped_mass", "gap_eq"},
                "PRZZAFEProgression.lean": {"quotient_iff", "truncated_iff", "k_sum", "grouped_cutoff_removed", "grouped_analytic_mass", "piece_smooth", "piece_support", "piece_telescope", "piece_sum_one"},
                "PRZZGroupedTime.lean": {"partition_grouped", "weighted_integrable_series", "weighted_cutoff_removed", "grouped_time_cutoff_removed", "partitioned_time_cutoff_removed", "fibre_quotient"},
                "PRZZQuotientMass.lean": {"restore_project", "fibre_sum", "grouped_sum", "kernel_height"},
                "PRZZHeightMass.lean": {"direct_mass_height", "mollifier_mass_le", "grouped_mass_height", "scaled_grouped_mass", "coefficient_mass", "source_mass_height"},
                "PRZZExplicitDomain.lean": {"image_eq_domain", "fibre_explicit", "grouped_explicit"},
                "PRZZExplicitTail.lean": {"retained_rows", "source_domain", "infinite_tail"},
                "PRZZPoissonTimeChange.lean": {"timeKernel_scaled", "time_integral", "literal_time_form"},
                "PRZZGammaFar.lean": {"gamma_norm_le", "sin_norm_le", "gamma_inv_bound", "quotient_bound", "shifted_quotient_bound", "actual_ratio_bound", "gaussian_norm", "far_core_bound"},
                "PRZZMellinTail.lean": {"kernel_eq", "factor_bound", "far_integrand_bound", "majorant_integrable", "far_integral_bound", "integrand_continuous", "integrand_integrable"},
                "PRZZKernelDifference.lean": {"main_eq_rescaled", "main_integrable", "sourceW_rescaled", "error_eq", "error_integrable", "difference_eq", "difference_norm_le", "far_main_bound", "far_error_integral_bound", "difference_split_bound"},
                "PRZZL1Truncation.lean": {"positive_sum", "rectangles_tendsto", "directSum_tendsto"},
                "PRZZL1Poisson.lean": {"progression", "scaled_fourier", "progression_normalized"},
                "PRZZDyadicEnvelope.lean": {"inverse_power", "dyadic_log_bound", "scaled_cutoffs",
                    "annihilator_bound", "annihilator_scaled", "common_integrable", "common_mass",
                    "arithmetic_integral_bound"},
                "PRZZCombinedBudget.lean": {"typeI_decay", "combined_decay", "source_h_sum", "literal_variation_blocks"},
                "PRZZHBBranches.lean": {"value_join", "total_multiply", "weighted_total", "mu_total",
                    "lambda_total", "branches_total", "coefficient_branches", "rectangle_branches"},
                "PRZZSharpAggregation.lean": {"sharp_signed_seven", "branch_sum_bound", "source_h_sum", "literal_of_h_blocks"},
                "PRZZHBRectangles.lean": {"mixed_diagonal", "mixed_add_left", "mixed_add_right",
                    "mixed_branch_pairs", "original_branch_pairs", "original_branch_bound", "signedSum_branches"},
                "PRZZSharpDI.lean": {"rightTwist_norm", "leftTwist_norm", "sharpBlock_eq", "sharpBlock_bound",
                    "sharpBlock_log_bound", "sharp_groups_bound", "sharpNegativeBlock_eq", "sharp_two_sided_bound"},
                "PRZZDISeven.lean": {"seven_expand", "balanced_exponents", "balance_power", "seven_balanced",
                    "h_power_transfer", "decay_positive", "decay_lower", "balanced_h_sum", "seven_h_bound", "finite_h_bound"},
            }
            expected_coverage = expected_audits[name]
            require(len(audited) == expected_coverage if isinstance(expected_coverage, int)
                    else audited == expected_coverage,
                    f"PRZZ debt-layer audit coverage changed: {name}")
            for theorem in audited:
                key = "XiPrime8845." + path.stem + "." + theorem
                require(key in dependencies, f"Missing PRZZ debt-layer audit: {key}")
                actual = {item.strip() for item in dependencies[key].split(",") if item.strip()}
                expected = (set()
                            if name == "PRZZNativeFamily.lean" and theorem == "matching_label"
                            else {"propext", "Quot.sound"}
                            if name == "PRZZNativeGcdGrid.lean" and theorem in {"restore_reduce", "reduce_restore"}
                            else {"propext", "Quot.sound"}
                            if name == "PRZZCoefficientSeparation.lean" and theorem == "allocations_length"
                            else {"propext", "Quot.sound"}
                            if name == "PRZZFreeLengthCoefficient.lean" and theorem == "endpoint_le"
                            else {"propext", "Quot.sound"}
                            if name == "PRZZL1Residue.lean" and theorem in {"residue_iff", "progression_residue"}
                            else {"propext", "Quot.sound"}
                            if name == "PRZZAFEDual.lean" and theorem in {"offDiagonal_residue", "offDiagonal_inverse"}
                            else {"propext", "Quot.sound"}
                            if name == "PRZZAFEIndices.lean" and theorem == "gap_eq"
                            else {"propext", "Quot.sound"}
                            if name == "PRZZWRowReindex.lean" and theorem == "reducePair_injective"
                            else {"propext"}
                            if name == "PRZZRowPlacement.lean" and theorem == "upper_le"
                            else {"propext"}
                            if name == "PRZZWRowReindex.lean" and theorem == "label_iff"
                            else {"propext", "Classical.choice", "Quot.sound"})
                require(actual == expected,
                        f"Unexpected PRZZ debt-layer dependencies: {key}: {actual}")
            # L0 defines input propositions; it must not install any proof of them.
            if name == "PRZZKloostermanInputs.lean":
                for proposition in expected_audits[name]:
                    require(re.search(r"^def " + proposition + r" : Prop :=$", path.read_text(), re.MULTILINE),
                            f"L0 input is no longer an explicit Prop definition: {proposition}")
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
