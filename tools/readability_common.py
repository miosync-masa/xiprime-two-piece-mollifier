#!/usr/bin/env python3
"""Shared helpers for the readability documents under docs/.

Everything here is derived from `import` lines, the Lean sources and the
captured compiler output in checks/; no dependency or theorem name is
hand-written. All iteration orders are sorted so repeated runs are identical.
"""
import hashlib
import json
import re
from collections import deque
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN_DIR = ROOT / "lean"
DEFAULT_RECORD = ROOT / "checks" / "weil-di-proportion-verification.json"
DEFAULT_AF_RECORD = ROOT / "checks" / "clean-af-verification-2026-11-07.json"
ROOT_MODULE = "WuProportion"
STANDARD_AXIOMS = ("propext", "Classical.choice", "Quot.sound")

# ---------------------------------------------------------------------------
# Layer assignment: purely by module name. The rules are printed verbatim into
# docs/dependency-graph.md so readers can audit them.
# ---------------------------------------------------------------------------
NUMERICAL_CERTIFICATE = (
    "KernelAlgebra", "FiniteJet", "BetaKernel", "IntegralJet", "TaylorEnvelope",
    "CoefficientEvaluator", "NumericalGate", "RationalEvaluator", "RationalBounds",
    "FixedCertificate",
)
PRZZ_INPUT = ("PRZZInterface", "PRZZAsymptoticCore", "PRZZAsymptotic", "PRZZProvedInput", "PRZZWitnessBridge")
MAIN_TERM_PREFIXES = (
    "Conrey", "Feng", "Gcd", "ElementaryGcd", "Coprime", "Totient", "Mobius",
    "Euler", "BareEuler", "RawEuler", "Shifted", "Shift", "Smooth", "Expanded",
    "TwoPiece", "ZetaMoment", "ZetaPole", "Height", "Arithmetic", "CompactShift",
    "Outer", "LogProfile", "Multiplicative", "Support", "Weight", "Endpoint",
    "Witness", "Cauchy",
)
PRZZ_SUBLAYERS = (
    ("L0 入力（Weil / DI の仕様）", ("KloostermanInputs",)),
    ("L1 近似関数等式と Poisson", (
        "AFE", "Poisson", "CoupledAFE", "ContourAFE", "SeriesAFE", "IntegratedAFE",
        "IntegratedFreezeAFE", "ReconstructedAFE", "ExhaustiveAFE", "PrunedAFE",
        "LiteralAFE", "DiscardedAFE", "AllPoisson", "Congruence", "L1", "Moment",
        "BodyTail",
    )),
    ("L2 算術分解（A*, Type I/II, Weil–DI）", (
        "AStar", "Actual", "Active", "TypeI", "TypeII", "Weil", "DI", "Sharp",
        "HeathBrown", "HB", "Kloosterman", "Cases", "Allocation", "Lambda", "Nu",
        "Gcd", "Arithmetic", "Mobius",
    )),
)
PRZZ_UNASSIGNED = "細分未割当"

LAYER_NUMERICAL = "数値証明書"
LAYER_PRZZ_INPUT = "PRZZ 定義・証明済み接続"
LAYER_COUNTING = "計数（Wu）"
LAYER_PRZZ_PROOF = "PRZZ 4.1 の証明"
LAYER_MAIN_TERM = "主項"
LAYER_OTHER = "その他"
LAYER_MATHLIB = "Mathlib"
LAYER_AF = "AF"
LAYER_ORDER = (LAYER_COUNTING, LAYER_PRZZ_INPUT, LAYER_MAIN_TERM, LAYER_NUMERICAL,
               LAYER_PRZZ_PROOF, LAYER_OTHER, LAYER_AF, LAYER_MATHLIB)

LAYER_RULES_TEXT = [
    (LAYER_NUMERICAL, "モジュール名が次の固定集合に一致: " + ", ".join(NUMERICAL_CERTIFICATE)),
    (LAYER_PRZZ_INPUT, "モジュール名が次の固定集合に一致（定義層と Weil/DI からの証明済み接続。公理層ではない）: " + ", ".join(PRZZ_INPUT)),
    (LAYER_COUNTING, "接頭辞 `Wu`"),
    (LAYER_PRZZ_PROOF, "接頭辞 `PRZZ`（上の固定集合を除く）。細分は `PRZZ` を除いた残りの接頭辞で: "
        + "; ".join(f"{name} = {', '.join(p)}" for name, p in PRZZ_SUBLAYERS)
        + f"; それ以外 = {PRZZ_UNASSIGNED}"),
    (LAYER_MAIN_TERM, "接頭辞が次のいずれか: " + ", ".join(MAIN_TERM_PREFIXES)),
    (LAYER_OTHER, "上のどれにも当たらないローカルモジュール（一覧に列挙）"),
    (LAYER_MATHLIB, "`import Mathlib...` をまとめた外部ノード"),
    (LAYER_AF, "`import Zeta23...`（固定コミットの AF ライブラリ）をまとめた外部ノード"),
]


def classify(name):
    """Return (layer, sublayer or None) for a local module name."""
    if name in NUMERICAL_CERTIFICATE:
        return LAYER_NUMERICAL, None
    if name in PRZZ_INPUT:
        return LAYER_PRZZ_INPUT, None
    if name.startswith("Wu"):
        return LAYER_COUNTING, None
    if name.startswith("PRZZ"):
        rest = name[len("PRZZ"):]
        for sub, prefixes in PRZZ_SUBLAYERS:
            if any(rest.startswith(p) for p in prefixes):
                return LAYER_PRZZ_PROOF, sub
        return LAYER_PRZZ_PROOF, PRZZ_UNASSIGNED
    if any(name.startswith(p) for p in MAIN_TERM_PREFIXES):
        return LAYER_MAIN_TERM, None
    return LAYER_OTHER, None


def external_layer(module):
    if module == "Mathlib" or module.startswith("Mathlib."):
        return LAYER_MATHLIB
    if module == "Zeta23" or module.startswith("Zeta23."):
        return LAYER_AF
    return None


# ---------------------------------------------------------------------------
# Lean source parsing
# ---------------------------------------------------------------------------
IMPORT_RE = re.compile(r"^import\s+([A-Za-z0-9_.']+)", re.M)
PRINT_AXIOMS_RE = re.compile(r"^#print axioms\s+([^\s]+)", re.M)
BLOCK_COMMENT_RE = re.compile(r"/-[-!]?(.*?)-/", re.S)


def camel_words(name):
    return re.findall(r"[A-Z][a-z0-9]*|[A-Z]+(?![a-z])", name)


def sentences(text):
    text = re.sub(r"\s+", " ", text).strip()
    if not text:
        return []
    parts = re.split(r"(?<=[.!?])\s+(?=[A-Z`$(\[\"'*])", text)
    return [p.strip() for p in parts if p.strip()]


def header_docstring(source):
    """First block comment after the import lines (``/-!``, ``/--`` or ``/-``)."""
    body = re.sub(r"^(import[^\n]*\n|\s*\n)+", "", source, count=1)
    m = re.match(r"\s*/-[-!]?(.*?)-/", body, re.S)
    return m.group(1).strip() if m else ""


UNPROVED_PATTERNS = (
    r"\bdoes not\b", r"\bdo not\b", r"\bnot asserted\b", r"\bnot claimed\b",
    r"\bnot proved\b", r"\bnot supplied\b", r"\bnot assumed\b", r"\bnot inferred\b",
    r"\bremains?\b", r"\bNOT\b", r"^No\b", r"\bis not\b", r"\bare not\b",
    r"\bneither\b", r"\bnor\b", r"\bunproved\b", r"\bstill\b", r"\bnot yet\b",
)
UNPROVED_RE = re.compile("|".join(UNPROVED_PATTERNS))


def unproved_sentences(source):
    """Sentences from every block comment that state what is *not* proved.

    Rule: the sentence matches one of UNPROVED_PATTERNS (listed in the
    generated document). Theorem bodies are not scanned, only comments.
    """
    out = []
    for m in BLOCK_COMMENT_RE.finditer(source):
        for s in sentences(m.group(1)):
            if UNPROVED_RE.search(s) and s not in out:
                out.append(s)
    return out


class Module:
    __slots__ = ("name", "path", "source", "imports", "local_imports",
                 "external_imports", "header", "print_axioms")

    def __init__(self, path, local_names):
        self.name = path.stem
        self.path = path
        self.source = path.read_text(encoding="utf-8")
        self.imports = IMPORT_RE.findall(self.source)
        self.local_imports = sorted(i for i in self.imports if i in local_names)
        self.external_imports = sorted(i for i in self.imports if i not in local_names)
        self.header = header_docstring(self.source)
        self.print_axioms = PRINT_AXIOMS_RE.findall(self.source)

    @property
    def external_layers(self):
        return sorted({external_layer(i) for i in self.external_imports} - {None})

    @property
    def unknown_externals(self):
        return [i for i in self.external_imports if external_layer(i) is None]

    def sha256(self):
        return hashlib.sha256(self.path.read_bytes()).hexdigest()


def load_modules(lean_dir=LEAN_DIR):
    paths = sorted(lean_dir.glob("*.lean"))
    names = {p.stem for p in paths}
    return {p.stem: Module(p, names) for p in paths}


def reachable_from(modules, root=ROOT_MODULE):
    """Transitive local imports of ``root``; returns {name: depth}."""
    depth = {root: 0}
    queue = deque([root])
    while queue:
        m = queue.popleft()
        for i in modules[m].local_imports:
            if i not in depth:
                depth[i] = depth[m] + 1
                queue.append(i)
    return depth


def topological_order(modules, names):
    """Dependencies first; ties broken alphabetically (deterministic)."""
    names = set(names)
    done, order = set(), []
    remaining = sorted(names)
    while remaining:
        ready = [n for n in remaining if all(i in done for i in modules[n].local_imports if i in names)]
        if not ready:
            raise ValueError("import cycle among: " + ", ".join(remaining))
        for n in ready:
            done.add(n)
            order.append(n)
        remaining = [n for n in remaining if n not in done]
    return order


# ---------------------------------------------------------------------------
# Compiler-output record (checks/*.json written by tools/verify_lean.py)
# ---------------------------------------------------------------------------
AXIOM_LINE_RE = re.compile(r"^'([^']+)' depends on axioms: \[(.*?)\]$")


class RecordEntry:
    __slots__ = ("file", "sha256", "output", "axioms", "exit_code")

    def __init__(self, file, entry):
        self.file = file
        self.sha256 = entry["sha256"]
        self.output = entry["output"]
        self.exit_code = entry.get("exit_code")
        self.axioms = []  # list of (full_name, [axioms]) in output order
        joined = re.sub(r"\n[ \t]+", " ", self.output.strip())
        for line in joined.split("\n"):
            m = AXIOM_LINE_RE.match(line.strip())
            if m:
                axioms = [a.strip() for a in m.group(2).split(",") if a.strip()]
                self.axioms.append((m.group(1), axioms))

    def resolve(self, short_name):
        """Full name for a ``#print axioms`` target as written in the source."""
        hits = [n for n, _ in self.axioms if n == short_name or n.endswith("." + short_name)]
        return hits[-1] if hits else None

    def axioms_of(self, full_name):
        for n, ax in self.axioms:
            if n == full_name:
                return ax
        return None

    def raw_line(self, full_name):
        """The verbatim compiler lines for one theorem, as printed."""
        m = re.search(r"'" + re.escape(full_name) + r"' depends on axioms: \[[^\]]*\]", self.output)
        return m.group(0) if m else None


def load_record(path=DEFAULT_RECORD):
    data = json.loads(Path(path).read_text(encoding="utf-8"))
    entries = {Path(f).stem: RecordEntry(f, e) for f, e in data["checks"].items()}
    meta = {k: v for k, v in data.items() if k not in ("checks", "source_sha256")}
    return entries, meta


def record_matches_source(entry, module):
    return entry is not None and entry.sha256 == module.sha256()


def load_verified_record(modules, path=DEFAULT_RECORD):
    """Fail closed before mixing current declarations with recorded axioms."""
    entries, meta = load_record(path)
    missing = sorted(set(modules) - set(entries))
    extra = sorted(set(entries) - set(modules))
    stale = sorted(n for n in modules if n in entries
                   and not record_matches_source(entries[n], modules[n]))
    failed = sorted(n for n, e in entries.items()
                    if e.exit_code != 0 or "sorryAx" in e.output or "error:" in e.output)
    if missing or extra or stale or failed:
        raise ValueError("Unverified compiler record: "
                         f"missing={missing}, extra={extra}, "
                         f"source SHA256 mismatch={stale}, failed={failed}")
    return entries, meta


def axioms_label(axioms):
    """'標準' for exactly the three standard axioms, else the full list."""
    if axioms is None:
        return "（記録なし）"
    if sorted(axioms) == sorted(STANDARD_AXIOMS):
        return "標準"
    return "[" + ", ".join(axioms) + "]"


def representative(module, entry):
    """(short, full) for the last ``#print axioms`` in the file."""
    if not module.print_axioms:
        return None, None
    short = module.print_axioms[-1]
    full = entry.resolve(short) if entry else None
    return short, full


def file_sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write_markdown(path, lines):
    """Canonical Markdown: no trailing spaces, exactly one final newline."""
    text = "\n".join(line.rstrip() for line in "\n".join(lines).splitlines()).rstrip() + "\n"
    Path(path).write_text(text, encoding="utf-8")


def rel(path):
    return Path(path).resolve().relative_to(ROOT).as_posix()
