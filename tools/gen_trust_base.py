#!/usr/bin/env python3
"""Generate docs/trust-base.md: the one-page trust base of the main theorem.

Statements are copied from the Lean sources, axiom outputs from the captured
compiler record, library pins from lake-manifest.json / lean-toolchain of the
pinned AF checkout (``--af``) cross-checked against lean/dependencies.json and
the verification records, and reproduction commands from docs/REPRODUCIBILITY.md.
"""
import argparse
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import readability_common as rc  # noqa: E402

MAIN_THEOREM = "ratio_eventually_gt"
EXTERNAL_DEFS = (("PRZZKloostermanInputs", "WeilIncomplete"),
                 ("PRZZKloostermanInputs", "DeshouillersIwaniecLemma1"))
MOMENT_ROOT, MOMENT_THEOREM = "PRZZMomentOptimal", "moment_bound"
DECL_RE = r"^(?:axiom|theorem|def|lemma|structure|abbrev|noncomputable def)\s+{name}\b"


def declaration(source, name):
    """Docstring + declaration text of ``name`` up to the end of its statement."""
    lines = source.split("\n")
    start = next((i for i, l in enumerate(lines) if re.match(DECL_RE.format(name=re.escape(name)), l)), None)
    if start is None:
        return None
    # preceding docstring
    j = start
    if j > 0 and lines[j - 1].rstrip().endswith("-/"):
        k = j - 1
        while k >= 0 and not lines[k].lstrip().startswith("/--"):
            k -= 1
        if k >= 0:
            j = k
    body = []
    for l in lines[start:]:
        if len(body) > 0 and (l.strip() == "" or re.match(r"^(#|end |namespace |theorem |def |axiom |/--)", l)):
            break
        body.append(l)
        if re.search(r":=\s*by\s*$", l):
            break
    text = "\n".join(lines[j:start] + body)
    return text.rstrip()


def find_declaration(modules, name):
    for n in sorted(modules):
        d = declaration(modules[n].source, name)
        if d:
            return n, d
    return None, None


def header_sh_blocks(md, section):
    part = md.split(section, 1)[1] if section in md else ""
    part = re.split(r"\n## ", part, 1)[0]
    return re.findall(r"```sh\n(.*?)```", part, re.S)


def references(readme):
    part = readme.split("## References", 1)[1] if "## References" in readme else ""
    return [l[2:].strip() for l in part.split("\n") if l.startswith("- ")]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--af", help="pinned AF checkout (reads lake-manifest.json and lean-toolchain)")
    ap.add_argument("--out", default=str(rc.ROOT / "docs" / "trust-base.md"))
    args = ap.parse_args()
    modules = rc.load_modules()
    record, meta = rc.load_verified_record(modules)
    af_record = json.loads(rc.DEFAULT_AF_RECORD.read_text(encoding="utf-8"))
    pins = json.loads((rc.LEAN_DIR / "dependencies.json").read_text(encoding="utf-8"))
    closure = rc.reachable_from(modules, rc.ROOT_MODULE)
    moment_closure = rc.reachable_from(modules, MOMENT_ROOT) if MOMENT_ROOT in modules else {}

    main_mod = modules[rc.ROOT_MODULE]
    main_entry = record[rc.ROOT_MODULE]
    main_full = main_entry.resolve(MAIN_THEOREM)
    main_axioms = main_entry.axioms_of(main_full)
    strict_full = main_entry.resolve("strict_proportion")
    sp_mod, sp_decl = find_declaration(modules, "StrictProportion")
    prop_mod, prop_decl = find_declaration(modules, "proportion")

    L = []
    L.append("# 信頼の基盤（trust base）")
    L.append("")
    L.append("生成: `python3 tools/gen_trust_base.py --af <固定 AF checkout>`。定理文は Lean ソースから、公理出力は "
             f"[{rc.rel(rc.DEFAULT_RECORD)}](../{rc.rel(rc.DEFAULT_RECORD)})（SHA-256 `{rc.file_sha(rc.DEFAULT_RECORD)[:16]}…`）から、"
             "ライブラリの固定情報は `lake-manifest.json` / `lean-toolchain` と "
             "[lean/dependencies.json](../lean/dependencies.json) から自動抽出しています。")
    L.append("")
    L.append("生成前に全ローカル Lean ソースの SHA-256 と記録の完全一致、"
             "成功終了コード、`sorryAx` / コンパイルエラーの不在を確認します。"
             "不一致・記録欠落時には生成を中止します。これは新たな Lean 再ビルドではなく、記録と現在のソースの照合です。")
    L.append("")
    L.append("## 1. 主定理")
    L.append("")
    L.append(f"[lean/{rc.ROOT_MODULE}.lean](../lean/{rc.ROOT_MODULE}.lean) の `{main_full}`:")
    L.append("")
    L.append("```lean")
    L.append(declaration(main_mod.source, MAIN_THEOREM))
    L.append("```")
    L.append("")
    L.append(f"同じファイルの `{strict_full}`（固定余白の形）:")
    L.append("")
    L.append("```lean")
    L.append(declaration(main_mod.source, "strict_proportion"))
    L.append("```")
    if sp_decl:
        L.append("")
        L.append(f"`StrictProportion` の定義（[lean/{sp_mod}.lean](../lean/{sp_mod}.lean)）:")
        L.append("")
        L.append("```lean")
        L.append(sp_decl)
        L.append("```")
    if prop_decl:
        L.append("")
        L.append(f"`proportion` の定義（[lean/{prop_mod}.lean](../lean/{prop_mod}.lean)）:")
        L.append("")
        L.append("```lean")
        L.append(prop_decl)
        L.append("```")
    L.append("")
    L.append(f"今回のビルド（{meta.get('lean_version', '')}）での `#print axioms {MAIN_THEOREM}` 出力の全文:")
    L.append("")
    L.append("```text")
    L.append(main_entry.raw_line(main_full))
    L.append("```")
    L.append("")
    L.append("同ファイルの他の `#print axioms` 出力:")
    L.append("")
    L.append("```text")
    for name, _ in main_entry.axioms:
        if name != main_full:
            L.append(main_entry.raw_line(name))
    L.append("```")
    nonstd = [a for a in main_axioms if a not in rc.STANDARD_AXIOMS]
    L.append("")
    L.append(f"標準三公理以外: {', '.join(f'`{a}`' for a in nonstd) if nonstd else 'なし'}。`sorryAx` は{'含まれる' if 'sorryAx' in main_axioms else '含まれない'}。")
    L.append("")

    # ---- 2. external inputs
    L.append("## 2. 外部入力")
    L.append("")
    L.append("### 2a. 主定理が依存する公理: `XiPrime8845.PRZZ.przz41_case3_K2_profiles`")
    L.append("")
    pi = modules["PRZZInterface"]
    L.append("[lean/PRZZInterface.lean](../lean/PRZZInterface.lean) のファイル冒頭コメント:")
    L.append("")
    L.append("> " + pi.header.replace("\n", "\n> "))
    L.append("")
    L.append("```lean")
    L.append(declaration(pi.source, "przz41_case3_K2_profiles"))
    L.append("```")
    L.append("")
    refs = references((rc.ROOT / "README.md").read_text(encoding="utf-8"))
    przz_refs = [r for r in refs if "Pratt" in r or "PRZZ" in r]
    L.append("原典（README の参考文献から）: " + ("; ".join(przz_refs) if przz_refs else "README に記載なし"))
    L.append("")
    L.append("照合メモ: この公理は PRZZ Theorem 4.1 第三の場合を K2 プロファイル族に特殊化した文で、"
             "主項は literal な gcd/lcm 二重和、誤差は `C T^eps (N^{7/4} + N^{7/8} T^{1/2})`。公理の文面と原典の対応は人による照合対象。")
    L.append("")
    L.append("### 2b. `WeilIncomplete` と `DeshouillersIwaniecLemma1`（`Prop` としての仕様。公理ではない）")
    L.append("")
    ki = modules["PRZZKloostermanInputs"]
    in_main = "PRZZKloostermanInputs" in closure
    in_moment = "PRZZKloostermanInputs" in moment_closure
    L.append(f"定義ファイル [lean/PRZZKloostermanInputs.lean](../lean/PRZZKloostermanInputs.lean) は、"
             f"主定理 `{rc.ROOT_MODULE}` の import 閉包に{'含まれます' if in_main else '**含まれません**'}"
             f"（`{MOMENT_ROOT}` の閉包には{'含まれます' if in_moment else '含まれません'}）。"
             "つまり主定理の論理には入らず、§2c の moment 定理の明示的仮定としてのみ使われます。")
    L.append("")
    L.append("ファイル冒頭コメント（原典と照合メモ）:")
    L.append("")
    L.append("> " + ki.header.replace("\n", "\n> "))
    L.append("")
    for mod, name in EXTERNAL_DEFS:
        L.append(f"`XiPrime8845.{mod}.{name}`:")
        L.append("")
        L.append("```lean")
        L.append(declaration(modules[mod].source, name))
        L.append("```")
        L.append("")
        raw = record[mod].raw_line(record[mod].resolve(name) or "")
        if raw:
            L.append("```text")
            L.append(raw)
            L.append("```")
            L.append("")
    L.append("<details><summary>lean/PRZZKloostermanInputs.lean 全文（補助定義 `e`, `inverseResidue`, `completeSum`, `WeilPrime`, `incompleteSum`, `diSum`, `diBound` を含む）</summary>")
    L.append("")
    L.append("```lean")
    L.append(ki.source.rstrip())
    L.append("```")
    L.append("")
    L.append("</details>")
    L.append("")
    if MOMENT_ROOT in modules:
        L.append(f"### 2c. 参考: `{MOMENT_ROOT}.{MOMENT_THEOREM}`（主定理の閉包外）")
        L.append("")
        me = record[MOMENT_ROOT]
        mfull = me.resolve(MOMENT_THEOREM)
        L.append(f"[lean/{MOMENT_ROOT}.lean](../lean/{MOMENT_ROOT}.lean) の `{mfull}` は Weil / DI を仮定にとる moment 評価で、"
                 f"`{rc.ROOT_MODULE}` からは到達{'可能' if MOMENT_ROOT in closure else '不能'}です。今回のビルドの出力:")
        L.append("")
        L.append("```text")
        L.append(me.raw_line(mfull))
        L.append("```")
        L.append("")
        L.append("<details><summary>定理文</summary>")
        L.append("")
        L.append("```lean")
        L.append(declaration(modules[MOMENT_ROOT].source, MOMENT_THEOREM))
        L.append("```")
        L.append("")
        L.append("</details>")
        L.append("")

    # ---- 3. libraries
    L.append("## 3. 依存する外部ライブラリ")
    L.append("")
    rows = [("lean/dependencies.json", pins.get("lean_toolchain"), pins.get("mathlib_commit"), pins.get("af_commit")),
            (rc.rel(rc.DEFAULT_RECORD), meta.get("lean_version"), meta.get("mathlib_commit"), meta.get("af_commit")),
            (rc.rel(rc.DEFAULT_AF_RECORD), None, af_record.get("mathlib_commit"), af_record.get("af_commit"))]
    if args.af:
        af = Path(args.af)
        manifest = json.loads((af / "lake-manifest.json").read_text(encoding="utf-8"))
        toolchain = (af / "lean-toolchain").read_text(encoding="utf-8").strip()
        mathlib = next((p["rev"] for p in manifest["packages"] if p["name"] == "mathlib"), None)
        rows.insert(0, ("AF checkout の lake-manifest.json / lean-toolchain", toolchain, mathlib, None))
        L.append("AF checkout の `lake-manifest.json` に記録された全パッケージ:")
        L.append("")
        L.append("| パッケージ | rev | URL |")
        L.append("| --- | --- | --- |")
        for p in sorted(manifest["packages"], key=lambda p: p["name"]):
            L.append(f"| {p['name']} | `{p['rev']}` | {p['url']} |")
        L.append("")
    else:
        L.append("（`--af` 未指定のため `lake-manifest.json` は未照合。lean/dependencies.json と検証記録の値のみ。）")
        L.append("")
    L.append("| 出典 | Lean | Mathlib | AF |")
    L.append("| --- | --- | --- | --- |")
    for src, lean, ml, afc in rows:
        L.append(f"| {src} | {lean or ''} | `{ml}` | {('`' + afc + '`') if afc else ''} |")
    mls = {r[2] for r in rows if r[2]}
    afs = {r[3] for r in rows if r[3]}
    L.append("")
    L.append(f"Mathlib の rev は全出典で{'一致' if len(mls) == 1 else '**不一致**'}、AF コミットは{'一致' if len(afs) == 1 else '**不一致**'}。")
    L.append("")
    af_mods = sorted(af_record.get("af_source_sha256", {}))
    direct = sorted({i for n in closure for i in modules[n].external_imports if rc.external_layer(i) == rc.LAYER_AF})
    L.append(f"AF（`{pins.get('af_repository')}` @ `{pins.get('af_commit')}`）の必須ソース閉包は **{len(af_mods)} モジュール**"
             f"（[{rc.rel(rc.DEFAULT_AF_RECORD)}](../{rc.rel(rc.DEFAULT_AF_RECORD)}) の `af_source_sha256`）。"
             f"主定理の閉包内のローカルモジュールが直接 import する AF モジュールは {len(direct)} 件:")
    L.append("")
    for i in direct:
        L.append(f"- `{i}`")
    L.append("")
    L.append("<details><summary>AF 必須モジュール一覧（{} 件）</summary>".format(len(af_mods)))
    L.append("")
    for m in af_mods:
        L.append(f"- `{m}`")
    L.append("")
    L.append("</details>")
    L.append("")
    mathlib_direct = sorted({i for n in closure for i in modules[n].external_imports if rc.external_layer(i) == rc.LAYER_MATHLIB})
    L.append(f"Mathlib（rev `{pins.get('mathlib_commit')}`）: 主定理の閉包内で直接 import される Mathlib モジュールは {len(mathlib_direct)} 件"
             + ("（`import Mathlib` を含む）" if "Mathlib" in mathlib_direct else "") + "。")
    L.append("")

    # ---- 4. redundant Python check
    L.append("## 4. 冗長な確認（Python 区間証明書）")
    L.append("")
    vp = (rc.ROOT / "paper" / "verify.py").read_text(encoding="utf-8")
    doc = re.match(r'\s*"""(.*?)"""', vp, re.S)
    L.append("[paper/verify.py](../paper/verify.py) の冒頭 docstring:")
    L.append("")
    L.append("> " + (doc.group(1).strip() if doc else "").replace("\n", "\n> "))
    L.append("")
    refs_py = [n for n in sorted(modules) if re.search(r"verify\.py|certificate\.json|numerical_interval\.py", modules[n].source)]
    fc = record["FixedCertificate"]
    fc_full = fc.resolve("fixed_functional_gate")
    L.append("Python の区間証明書は Lean の `FixedCertificate` と独立の確認であり、主定理の論理には入りません。機械的な裏付け:")
    L.append("")
    L.append(f"- `paper/verify.py` / `certificate.json` / `numerical_interval.py` を文字列として参照する Lean ソース: "
             + (", ".join(f"`{n}`" for n in refs_py) if refs_py else "なし") + "（コメント中の言及のみ。Lean の `import` は Mathlib / AF / ローカルモジュールに限られ、JSON や Python の出力を読み込む経路はありません）。")
    L.append(f"- `{fc_full}` の出力: `{fc.raw_line(fc_full)}`（数値公理・`native_decide`・外部データへの依存なし）。")
    L.append("- 二つの囲いは別物です: Python は `1.12818163807203565629105 < M < 1.12818163807203565629124`、Lean は上界 `1.128201` と目標下界 `1.1282054105`（README）。")
    L.append("")

    # ---- 5. reproduction
    L.append("## 5. 再現手順")
    L.append("")
    repro = (rc.ROOT / "docs" / "REPRODUCIBILITY.md").read_text(encoding="utf-8")
    L.append("### 5a. 数値証明書（Python、ネットワーク不要）")
    L.append("")
    for b in header_sh_blocks(repro, "## Numerical certificate"):
        L.append("```sh")
        L.append(b.rstrip())
        L.append("```")
        L.append("")
    wf = (rc.ROOT / ".github" / "workflows" / "verify.yml").read_text(encoding="utf-8")
    tm = re.search(r"timeout-minutes:\s*(\d+)", wf)
    L.append(f"期待される出力: `PASS` 3 行（ハッシュ数、有理数検査、証明書 JSON の一致）。CI の制限時間は {tm.group(1) if tm else '?'} 分。")
    L.append("")
    L.append("### 5b. Lean のクリーンビルドと公理監査")
    L.append("")
    L.append("[docs/REPRODUCIBILITY.md](REPRODUCIBILITY.md) の手順:")
    L.append("")
    for b in header_sh_blocks(repro, "## Lean verification"):
        L.append("```sh")
        L.append(b.rstrip())
        L.append("```")
        L.append("")
    L.append("2026-11-07 のクリーン検証で実際に使われたコマンド（記録から）:")
    L.append("")
    L.append("```sh")
    L.append("# AF 必須閉包の新規ビルド（隔離 worktree、Mathlib キャッシュは固定版を再利用）")
    L.append(af_record.get("command", ""))
    L.append("# 本体 698 モジュールの新規コンパイルと公理監査")
    L.append(af_record.get("project_command", ""))
    L.append("```")
    L.append("")
    L.append("期待される出力:")
    L.append("")
    L.append(f"- AF: `{af_record.get('lake_result', '')}`（新規ビルド {af_record.get('af_newly_built_module_count')} / {af_record.get('af_source_module_count')} モジュール）")
    L.append(f"- 本体: {af_record.get('project_module_count')} モジュールをすべて新規コンパイル、公理監査 {af_record.get('project_axiom_audit_count')} 件、"
             f"`existing_build_used: {json.dumps(meta.get('existing_build_used'))}`、`clean_upstream_build_performed: {json.dumps(meta.get('clean_upstream_build_performed'))}`")
    L.append(f"- `#print axioms {MAIN_THEOREM}` が §1 の全文と一致（標準三公理 + `{nonstd[0] if nonstd else ''}` のみ、`sorryAx` なし）")
    L.append("")
    L.append("所要時間の目安: 検証記録には経過時間が記録されていません（`parallel_jobs: "
             f"{meta.get('parallel_jobs')}` で実行）。次回の実行時に計測して追記してください。")
    L.append("")
    rc.write_markdown(args.out, L)
    print("trust-base written")


if __name__ == "__main__":
    main()
