#!/usr/bin/env python3
"""Fail-closed regression tests for the polarization axiom-output audit."""
import ast
import re
import unittest

from verify_lean import (ROOT, audit_diagonal_kernel, audit_finite_family_rows,
                        audit_polarization, audit_witness_proportion, audit_witness_basis,
                        audit_profile_uniform, audit_moment_bridge, audit_proved_input, lean_code_only,
                        audit_standard_module)


class PolarizationAuditTests(unittest.TestCase):
    def setUp(self):
        source = (ROOT / "lean/PRZZCoefficientPolarization.lean").read_text()
        names = re.findall(r"^#print axioms (\w+)$", source, re.MULTILINE)
        self.good = "\n".join(
            f"'XiPrime8845.PRZZCoefficientPolarization.{name}' depends on axioms: "
            "[propext, Classical.choice, Quot.sound]" for name in names)

    def test_exact_coverage(self):
        audit_polarization(self.good)

    def test_missing_or_duplicate_audit(self):
        rows = self.good.splitlines()
        for bad in ("\n".join(rows[1:]), self.good + "\n" + rows[0],
                    "\n".join([rows[0]] + rows[:-1])):
            with self.subTest(output=bad), self.assertRaises(ValueError):
                audit_polarization(bad)

    def test_extra_analytic_axiom(self):
        with self.assertRaises(ValueError):
            audit_polarization(self.good.replace("Quot.sound]",
                "Quot.sound, PRZZ.przz41_case3_K2_profiles]", 1))

    def test_errors_cannot_hide_behind_successful_audits(self):
        for trailer in ("\nerror: failed", "\nsorryAx"):
            with self.subTest(trailer=trailer), self.assertRaises(ValueError):
                audit_polarization(self.good + trailer)


class FiniteFamilyRowAuditTests(unittest.TestCase):
    def test_coverage_and_no_analytic_axiom(self):
        source = (ROOT / "lean/PRZZFiniteFamilyRows.lean").read_text()
        names = re.findall(r"^#print axioms (\w+)$", source, re.MULTILINE)
        good = "\n".join(
            f"'XiPrime8845.PRZZFiniteFamilyRows.{name}' depends on axioms: "
            "[propext, Classical.choice, Quot.sound]" for name in names)
        audit_finite_family_rows(good)
        for bad in ("\n".join(good.splitlines()[1:]), good + "\nerror: failed",
                    good + "\n" + good.splitlines()[0],
                    good.replace("Quot.sound]", "Quot.sound, sorryAx]", 1)):
            with self.subTest(output=bad), self.assertRaises(ValueError):
                audit_finite_family_rows(bad)


class DiagonalKernelAuditTests(unittest.TestCase):
    def test_kernel_coverage_and_analytic_axiom_rejection(self):
        source = (ROOT / "lean/PRZZDiagonalKernel.lean").read_text()
        names = re.findall(r"^#print axioms (\w+)$", source, re.MULTILINE)
        good = "\n".join(
            f"'XiPrime8845.PRZZDiagonalKernel.{name}' depends on axioms: "
            "[propext, Classical.choice, Quot.sound]" for name in names)
        audit_diagonal_kernel(good)
        for bad in ("\n".join(good.splitlines()[1:]), good + "\nerror: failed",
                    good.replace("Quot.sound]", "Quot.sound, PRZZ.przz41_case3_K2_profiles]", 1)):
            with self.subTest(output=bad), self.assertRaises(ValueError):
                audit_diagonal_kernel(bad)


class WitnessInputAuditTests(unittest.TestCase):
    def test_general_input_is_rejected(self):
        good = "\n".join(
            f"'XiPrime8845.WuProportion.{name}' depends on axioms: "
            "[propext, Classical.choice, Quot.sound]"
            for name in ("dyadic_eventually", "cumulative_eventually", "strict_proportion", "ratio_eventually_gt"))
        audit_witness_proportion(good)
        for old in ("przz41_case3_K2_witness", "przz41_case3_K2_profiles"):
            with self.subTest(axiom=old), self.assertRaises(ValueError):
                audit_witness_proportion(good.replace("Quot.sound]", "Quot.sound, PRZZ." + old + "]", 1))


class WitnessBasisAuditTests(unittest.TestCase):
    def test_basis_and_mass_fail_closed(self):
        for module in ("PRZZWitnessBasis", "PRZZWitnessMass"):
            source = (ROOT / "lean" / (module + ".lean")).read_text()
            names = re.findall(r"^#print axioms (\w+)$", source, re.MULTILINE)
            good = "\n".join(f"'XiPrime8845.{module}.{name}' depends on axioms: "
                "[propext, Classical.choice, Quot.sound]" for name in names)
            audit_witness_basis(good, module)
            for bad in ("\n".join(good.splitlines()[1:]), good+"\nerror: failed",
                        good.replace("Quot.sound]", "Quot.sound, PRZZ.przz41_case3_K2_witness]", 1)):
                with self.subTest(module=module), self.assertRaises(ValueError):
                    audit_witness_basis(bad, module)


class UniformProfileAuditTests(unittest.TestCase):
    def test_profiles_have_exact_standard_only_audits(self):
        for module in ("PRZZProfileSmooth", "PRZZProfileScale"):
            source = (ROOT / "lean" / (module + ".lean")).read_text()
            names = re.findall(r"^#print axioms (\w+)$", source, re.MULTILINE)
            good = "\n".join(f"'XiPrime8845.{module}.{name}' depends on axioms: "
                "[propext, Classical.choice, Quot.sound]" for name in names)
            audit_profile_uniform(good, module)
            for bad in ("\n".join(good.splitlines()[1:]), good+"\nsorryAx",
                        good+"\n"+good.splitlines()[0],
                        good.replace("Quot.sound]", "Quot.sound, PRZZ.przz41_case3_K2_witness]", 1)):
                with self.subTest(module=module), self.assertRaises(ValueError):
                    audit_profile_uniform(bad, module)


class MomentBridgeAuditTests(unittest.TestCase):
    def test_exact_standard_only_coverage(self):
        for module in ("PRZZPrimitiveKernel", "PRZZGammaMultiplier", "PRZZKernelComparison", "PRZZFamilyMoment",
                       "PRZZMellinInterval", "PRZZProfileMellin",
                       "PRZZClassSources", "PRZZClassVariation", "PRZZClassDI",
                       "PRZZClassFreeLength", "PRZZClassTypeI", "PRZZClassCases", "PRZZClassRows",
                       "PRZZMixedLiteral", "PRZZClassLiteral", "PRZZMixedReplacement", "PRZZMixedDefect", "PRZZMixedPoisson", "PRZZMixedMoment", "PRZZClassPoisson",
                 "PRZZClassWideLiteral", "PRZZClassWidePoisson", "PRZZClassPositiveGrid",
                 "PRZZClassDualProfile", "PRZZClassPairedGrid",
                 "PRZZClassSpatialSources", "PRZZClassSpatialDI", "PRZZClassSpatialTypeI", "PRZZClassSpatialCases", "PRZZClassSpatialRows", "PRZZClassNegativeLiteral", "PRZZClassNegativePoisson", "PRZZClassNegativeGrid", "PRZZClassSignedGrid", "PRZZClassPairedSignedGrid", "PRZZClassZeroBoundary", "PRZZClassZeroTail", "PRZZClassZeroPrimalGap", "PRZZClassZeroCorrection", "PRZZCappedPrefactor", "PRZZCappedTailMass", "PRZZCappedWindowMass", "PRZZCappedWindowTime", "PRZZCappedWindowField", "PRZZCappedFreezeMoment", "PRZZCappedFreezeBudget", "PRZZCappedNativeTail", "PRZZCappedStrictTail", "PRZZCappedBandOuter", "PRZZCappedSameMask", "PRZZCappedTailBand", "PRZZCappedStrictFreeze", "PRZZCappedLarge", "PRZZCappedDiscardedIBP", "PRZZCappedDiscarded", "PRZZCappedFreezeCollector", "PRZZCappedDiscardedFamily", "PRZZCappedRemainder", "PRZZCappedMomentBridge", "PRZZCappedMainTerm", "PRZZCentralGridIdentity", "PRZZBasisGridCutoff", "PRZZBasisGridBound", "PRZZCappedWindowBand", "PRZZCappedSubunitMass", "PRZZCappedBodyMass", "PRZZCappedBodyTail", "PRZZCappedGammaDefect", "PRZZBasisPairedBody", "PRZZFamilyMomentOptimal", "PRZZWitnessBridge"):
            source = (ROOT / "lean" / (module + ".lean")).read_text()
            names = re.findall(r"^#print axioms (\w+)$", source, re.MULTILINE)
            namespace = "PRZZZeroGammaBound" if module == "PRZZGammaMultiplier" else module
            good = "\n".join(f"'XiPrime8845.{namespace}.{name}' depends on axioms: "
                "[propext, Classical.choice, Quot.sound]" for name in names)
            audit_moment_bridge(good, module)
            for bad in ("\n".join(good.splitlines()[1:]), good+"\nerror: failed",
                        good+"\n"+good.splitlines()[0],
                        good.replace("Quot.sound]", "Quot.sound, PRZZ.przz41_case3_K2_witness]", 1)):
                with self.subTest(module=module), self.assertRaises(ValueError):
                    audit_moment_bridge(bad, module)


class ProvedInputAuditTests(unittest.TestCase):
    def test_proved_interface_and_core_fail_closed(self):
        for module, namespaces in (
                ("PRZZProvedInput", ["PRZZ", "PRZZ"]),
                ("PRZZAsymptoticCore", ["PRZZAsymptotic"] * 5),
                ("PRZZAsymptotic", ["PRZZAsymptotic"] * 6 + ["ArithmeticRegularity"])):
            source = (ROOT / "lean" / (module + ".lean")).read_text()
            names = re.findall(r"^#print axioms (\w+)$", source, re.MULTILINE)
            self.assertEqual(len(names), len(namespaces))
            good = "\n".join(f"'XiPrime8845.{ns}.{name}' depends on axioms: "
                "[propext, Classical.choice, Quot.sound]" for ns, name in zip(namespaces, names))
            audit_proved_input(good, module)
            for bad in ("\n".join(good.splitlines()[1:]), good + "\nsorryAx",
                        good + "\n" + good.splitlines()[0],
                        good.replace("Quot.sound]", "Quot.sound, PRZZ.przz41_case3_K2_witness]", 1)):
                with self.subTest(module=module), self.assertRaises(ValueError):
                    audit_proved_input(bad, module)


class LocalRegistryTests(unittest.TestCase):
    def test_apostrophe_and_empty_axiom_audits(self):
        source = "#print axioms N.foo'\n#print axioms N.empty\n"
        good = "'N.foo'' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
        good += "'N.empty' does not depend on any axioms\n"
        audit_standard_module(source, good, "probe")
        for bad in (good.replace("foo'", "other"), good + good,
                    good.replace("Quot.sound]", "Quot.sound, badInput]")):
            with self.subTest(output=bad), self.assertRaises(ValueError):
                audit_standard_module(source, bad, "probe")

    def test_axiom_declarations_not_docstring_words(self):
        code = '/- outer /- nested -/\naxiom not_a_declaration\n-/\n-- axiom comment\n'
        code += 'def s := "axiom string"\naxiom realInput : True\n'
        self.assertEqual(re.findall(r"^\s*axiom\s+(\w+)", lean_code_only(code), re.MULTILINE),
                         ["realInput"])

    def test_complete_topological_registry(self):
        tree = ast.parse((ROOT / "tools/verify_lean.py").read_text())
        function = next(n for n in tree.body if isinstance(n, ast.FunctionDef)
                        and n.name == "compile_sources")
        strings = []
        for node in ast.walk(function):
            if (isinstance(node, ast.For) and isinstance(node.target, ast.Name)
                    and node.target.id == "name" and isinstance(node.iter, ast.Tuple)):
                strings.extend(node.iter.elts)
            elif (isinstance(node, ast.Assign) and any(isinstance(t, ast.Name) and t.id == "name"
                    for t in node.targets) and isinstance(node.value, ast.Constant)):
                strings.append(node.value)
        strings = sorted((n for n in strings if isinstance(n, ast.Constant)
                          and isinstance(n.value, str) and n.value.endswith(".lean")),
                         key=lambda n: (n.lineno, n.col_offset))
        names = [n.value for n in strings]
        actual = {p.name for p in (ROOT / "lean").glob("*.lean")}
        self.assertEqual(set(names), actual)
        self.assertEqual(len(names), len(set(names)))
        seen = set()
        for name in names:
            source = (ROOT / "lean" / name).read_text()
            deps = re.findall(r"^import\s+([A-Za-z0-9_.]+)", source, re.MULTILINE)
            for dep in deps:
                if dep + ".lean" in actual:
                    self.assertIn(dep + ".lean", seen, (name, dep))
            seen.add(name)


if __name__ == "__main__":
    unittest.main()
