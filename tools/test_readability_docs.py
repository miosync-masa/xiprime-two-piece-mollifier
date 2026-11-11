#!/usr/bin/env python3
"""Regression tests for readability generators; only temporary copies are mutated."""
import json
import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
import xml.etree.ElementTree as ET

from gen_dependency_graph import wrap_svg_text
from gen_paper_correspondence import first_sentence
from readability_common import DEFAULT_RECORD, DEFAULT_AF_RECORD

ROOT = Path(__file__).resolve().parents[1]
RECORD_REL = DEFAULT_RECORD.relative_to(ROOT).as_posix()
AF_RECORD_REL = DEFAULT_AF_RECORD.relative_to(ROOT).as_posix()


class ReadabilityTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.storage = tempfile.TemporaryDirectory(prefix="przz-readability-tests-")
        cls.base = Path(cls.storage.name) / "base"
        cls.base.mkdir()
        for directory in ("tools", "lean"):
            shutil.copytree(ROOT / directory, cls.base / directory,
                            ignore=shutil.ignore_patterns("__pycache__", "*.pyc"))
        for name in ("README.md", "README.ja.md", "docs/STATUS.md", "docs/history.md",
                     "docs/REPRODUCIBILITY.md", "paper/manuscript.tex",
                     "paper/verify.py", ".github/workflows/verify.yml",
                     RECORD_REL, AF_RECORD_REL,
                     "checks/clean-af-verification-2026-11-07.json"):
            target = cls.base / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT / name, target)
        result = cls.command(cls.base, "generate_readability_docs.py")
        if result.returncode:
            raise RuntimeError(result.stdout + result.stderr)

    @classmethod
    def tearDownClass(cls):
        cls.storage.cleanup()

    def setUp(self):
        self.fixture = tempfile.TemporaryDirectory(dir=self.storage.name, prefix="case-")
        self.repo = Path(self.fixture.name) / "repo"
        shutil.copytree(self.base, self.repo)
        self.addCleanup(self.fixture.cleanup)

    @staticmethod
    def command(repo, script, *args):
        return subprocess.run([sys.executable, "-B", str(repo / "tools" / script), *args],
                              cwd=repo, env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"),
                              text=True, capture_output=True)

    def run_script(self, script, *args):
        return self.command(self.repo, script, *args)

    def snapshot(self):
        return {p.relative_to(self.repo).as_posix(): (p.read_bytes(), p.stat().st_mtime_ns)
                for p in self.repo.rglob("*") if p.is_file()}

    def record(self):
        return self.repo / RECORD_REL

    def test_markdown_avoids_rejected_operator_macro(self):
        # The reported Markdown renderer rejects this macro; upright labels
        # use the simpler mathrm form. This is not a restriction on TeX/PDF.
        for name in ("README.md", "README.ja.md", "docs/STATUS.md", "docs/history.md"):
            with self.subTest(path=name):
                self.assertNotIn(r"\operatorname", (self.repo / name).read_text())

    def test_default_records_are_the_complete_fresh_build(self):
        local = json.loads(self.record().read_text())
        af_path = self.repo / AF_RECORD_REL
        af = json.loads(af_path.read_text())
        self.assertTrue(local["full_project_rebuilt"])
        self.assertEqual(local["fresh_module_count"], len(local["checks"]))
        self.assertTrue(all(not row["reused_this_run"] for row in local["checks"].values()))
        self.assertEqual(local["upstream_verification_sha256"],
                         hashlib.sha256(af_path.read_bytes()).hexdigest())
        self.assertEqual(af["af_source_module_count"], af["af_newly_built_module_count"])
        self.assertFalse(af["old_af_build_outputs_used"])
        self.assertFalse(af["mathlib_source_rebuilt"])

    def test_check_preserves_manual_bytes_and_all_repository_files(self):
        manual = self.repo / "tools/paper_correspondence_manual.json"
        manual.write_text("\n" + manual.read_text())
        before = self.snapshot()
        for _ in range(2):
            result = self.run_script("generate_readability_docs.py", "--check")
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(self.snapshot(), before)

    def test_failed_check_is_also_read_only(self):
        doc = self.repo / "docs/modules.md"
        doc.write_text(doc.read_text() + "Stale documentation\n")
        before = self.snapshot()
        result = self.run_script("generate_readability_docs.py", "--check")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("STALE: docs/modules.md", result.stdout)
        self.assertEqual(self.snapshot(), before)

    def test_new_label_requires_explicit_manual_sync(self):
        tex = self.repo / "paper/manuscript.tex"
        tex.write_text(tex.read_text() + "\n\\begin{lemma}\\label{audit:new}New test.\\end{lemma}\n")
        manual = self.repo / "tools/paper_correspondence_manual.json"
        previous = json.loads(manual.read_text())
        before = self.snapshot()
        result = self.run_script("generate_readability_docs.py", "--check")
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(self.snapshot(), before)
        result = self.run_script("gen_paper_correspondence.py")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(manual.read_text()), previous)
        result = self.run_script("gen_paper_correspondence.py", "--sync-manual")
        self.assertEqual(result.returncode, 0, result.stderr)
        updated = json.loads(manual.read_text())
        self.assertIn("audit:new", updated)
        self.assertEqual({k: updated[k] for k in previous}, previous)

    def test_hypotheses_have_separate_numbers_and_manual_scope(self):
        tex = self.repo / "paper/manuscript.tex"
        tex.write_text(
            r"\begin{theorem}\label{t:a}First.\end{theorem}" + "\n" +
            r"\begin{hypothesis}\label{h:a}Input one.\end{hypothesis}" + "\n" +
            r"\begin{hypothesis}\label{h:b}Input two.\end{hypothesis}" + "\n" +
            r"\begin{lemma}\label{t:b}Second.\end{lemma}" + "\n")
        manual = self.repo / "tools/paper_correspondence_manual.json"
        before = manual.read_bytes()
        result = self.run_script("gen_paper_correspondence.py")
        self.assertEqual(result.returncode, 0, result.stderr)
        table = (self.repo / "docs/paper-correspondence.md").read_text()
        for number, label in (("1", "t:a"), ("H1", "h:a"), ("H2", "h:b"), ("2", "t:b")):
            self.assertIn(f"| {number} | \x60{label}\x60 |", table)
        self.assertEqual(manual.read_bytes(), before)

    def test_sentence_does_not_split_inline_math_decimal(self):
        self.assertEqual(first_sentence(r"At \(x=0.8845\) the bound holds. Next."),
                         "At $x=0.8845$ the bound holds.")

    def test_stale_source_rejected_before_any_output_or_manual_write(self):
        source = self.repo / "lean/WuProportion.lean"
        source.write_text(source.read_text().replace("0.8845", "0.9999"))
        before = self.snapshot()
        for script, args in [
                ("gen_trust_base.py", ("--out", "docs/rejected.md")),
                ("gen_modules_table.py", ("--out", "docs/rejected.md")),
                ("gen_dependency_graph.py", ("--out", "docs/rejected")),
                ("generate_readability_docs.py", ("--sync-manual",))]:
            with self.subTest(script=script):
                result = self.run_script(script, *args)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("source SHA256 mismatch=['WuProportion']", result.stderr)
                self.assertEqual(self.snapshot(), before)

    def test_missing_record_rejected(self):
        record = json.loads(self.record().read_text())
        del record["checks"]["WuProportion.lean"]
        self.record().write_text(json.dumps(record))
        before = self.snapshot()
        result = self.run_script("gen_trust_base.py")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("missing=['WuProportion']", result.stderr)
        self.assertEqual(self.snapshot(), before)

    def test_failed_and_unsound_compiler_records_rejected(self):
        original = json.loads(self.record().read_text())
        for field, value in [("exit_code", 1), ("output", "sorryAx"), ("output", "error: failed")]:
            with self.subTest(field=field, value=value):
                record = json.loads(json.dumps(original))
                record["checks"]["WuProportion.lean"][field] = value
                self.record().write_text(json.dumps(record))
                before = self.snapshot()
                result = self.run_script("generate_readability_docs.py", "--check")
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("failed=['WuProportion']", result.stderr)
                self.assertEqual(self.snapshot(), before)

    def test_check_rejects_writing_option(self):
        before = self.snapshot()
        result = self.run_script("generate_readability_docs.py", "--check", "--sync-manual")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("--check is read-only", result.stderr)
        self.assertEqual(self.snapshot(), before)

    def test_svg_label_bounds_and_scope_column(self):
        ns = {"s": "http://www.w3.org/2000/svg"}
        svg = ET.parse(self.repo / "docs/dependency-graph.svg").getroot()
        groups = svg.findall("s:g", ns)
        graph = json.loads((self.repo / "docs/dependency-graph.json").read_text())
        self.assertEqual(len(groups), len(graph["summary"]["nodes"]))
        self.assertGreater(len(groups), 0)
        for group in groups:
            rect = group.find("s:rect", ns)
            w, h, y = (float(rect.attrib[k]) for k in ("width", "height", "y"))
            for text in group.findall("s:text", ns):
                self.assertLessEqual(len(text.text or "") * float(text.attrib["font-size"]), w - 20)
                self.assertLess(float(text.attrib["y"]), y + h)
        table = (self.repo / "docs/modules.md").read_text()
        self.assertIn("当該ファイルの範囲・注意（コメント抽出）", table)
        self.assertNotIn("| 証明していないこと |", table)
        for name in ("dependency-graph.md", "modules.md", "paper-correspondence.md", "trust-base.md"):
            text = (self.repo / "docs" / name).read_text()
            self.assertTrue(text.endswith("\n"))
            self.assertFalse(text.endswith("\n\n"))
            self.assertTrue(all(line == line.rstrip() for line in text.splitlines()))

    def test_svg_wrap_preserves_identifiers_without_orphan_characters(self):
        for text in ("ratio_eventually_gt", "normalizedMoment_exactEvaluator_tendsto", "定理" * 35):
            parts = wrap_svg_text(text, 9.5, 200)
            self.assertEqual("".join(parts), text)
            self.assertTrue(all(len(p) * 9.5 <= 200 for p in parts))
            self.assertLessEqual(max(map(len, parts)) - min(map(len, parts)), 1)


if __name__ == "__main__":
    unittest.main(verbosity=2)
