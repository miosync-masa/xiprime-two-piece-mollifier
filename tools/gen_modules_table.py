#!/usr/bin/env python3
"""Generate docs/modules.md: one row per module reachable from WuProportion.

Columns are extracted mechanically: layer (name rule), role (first sentence of
the header comment), representative theorem (last `#print axioms` in the file,
resolved to its full name through the recorded compiler output), its axioms
from that output, and mechanically selected scope/caution comment sentences.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import readability_common as rc  # noqa: E402


def cell(text):
    return text.replace("|", "\\|").replace("\n", " ")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=rc.ROOT_MODULE)
    ap.add_argument("--out", default=str(rc.ROOT / "docs" / "modules.md"))
    args = ap.parse_args()
    modules = rc.load_modules()
    record, meta = rc.load_verified_record(modules)
    depth = rc.reachable_from(modules, args.root)
    rank = {l: i for i, l in enumerate(rc.LAYER_ORDER)}
    names = sorted(depth, key=lambda n: (rank[rc.classify(n)[0]], n))

    rows, no_role, stale, nonstandard_others = [], [], [], []
    for n in names:
        m = modules[n]
        entry = record.get(n)
        fresh = rc.record_matches_source(entry, m)
        if not fresh:
            stale.append(n)
        layer, sub = rc.classify(n)
        role = rc.sentences(m.header)
        role = role[0] if role else ""
        if not role:
            no_role.append(n)
        short, full = rc.representative(m, entry)
        axioms = entry.axioms_of(full) if (entry and full) else None
        ax_label = rc.axioms_label(axioms)
        if entry:
            others = [(name, ax) for name, ax in entry.axioms
                      if name != full and not set(ax) <= set(rc.STANDARD_AXIOMS)]
            if others:
                nonstandard_others.append((n, others))
                ax_label += "（同ファイル内の他の非標準出力 " + str(len(others)) + " 件: " + "; ".join(
                    f"`{name}` → [{', '.join(ax)}]" for name, ax in others) + "）"
        if not fresh:
            ax_label += "（ソースが記録と不一致: 要再ビルド）"
        unproved = rc.unproved_sentences(m.source)
        rows.append((n, layer + (f"／{sub}" if sub else ""), role, full or short or "", ax_label, unproved))

    L = []
    L.append(f"# モジュール表（`{args.root}` から到達可能な {len(names)} モジュール）")
    L.append("")
    L.append("生成: `python3 tools/gen_modules_table.py`。すべて `import` 行・ファイル冒頭のコメント・"
             f"[{rc.rel(rc.DEFAULT_RECORD)}](../{rc.rel(rc.DEFAULT_RECORD)}) に記録されたコンパイラ出力から自動抽出しています。")
    L.append("")
    L.append("列の意味:")
    L.append("")
    L.append("- **層**: [dependency-graph.md](dependency-graph.md#層の割り当て規則モジュール名から機械的に判定) の名前規則で機械的に割り当て。")
    L.append("- **役割**: ファイル冒頭の docstring（`/-! ... -/` など）の最初の一文。無い場合は空欄にし、末尾に列挙。")
    L.append("- **代表定理**: そのファイルで最後に `#print axioms` されている対象。完全名は記録された出力行から取得。")
    L.append("- **公理**: 代表定理の `#print axioms` 出力。`propext, Classical.choice, Quot.sound` のみなら「標準」、それ以外は全文。"
             "同じファイルの他の `#print axioms` に標準三公理以外を含む出力があれば併記（過小申告を防ぐため）。"
             "定理の明示的仮定は公理一覧には現れません。主定理の Weil/DI 仮定は [trust-base.md](trust-base.md) の定理文で確認します。")
    L.append("- **当該ファイルの範囲・注意（コメント抽出）**: ファイル内のすべてのコメントから、次の語を含む文を機械抽出: "
             + ", ".join(f"`{p}`" for p in rc.UNPROVED_PATTERNS) + "。"
             "肯定的な証明記述も含むため、未証明事項の一覧とは解釈しません。"
             "文脈を切り離した抽出なので、原文での確認を前提とした「見落とし防止」列です。削らないこと。")
    L.append("")
    L.append(f"記録のビルド環境: {meta.get('lean_version', '')}; AF `{meta.get('af_commit', '')}`; Mathlib `{meta.get('mathlib_commit', '')}`。")
    L.append("")
    L.append("| モジュール | 層 | 役割 | 代表定理 | 公理 | 当該ファイルの範囲・注意（コメント抽出） |")
    L.append("| --- | --- | --- | --- | --- | --- |")
    for n, layer, role, rep, ax, unproved in rows:
        L.append(f"| [{n}](../lean/{n}.lean) | {layer} | {cell(role)} | `{rep}` | {cell(ax)} | "
                 + cell("<br>".join(f"- {s}" for s in unproved)) + " |")
    L.append("")
    L.append("## 役割（冒頭 docstring）が空のモジュール")
    L.append("")
    L.append(", ".join(f"[{n}](../lean/{n}.lean)" for n in no_role) if no_role else "なし。")
    L.append("")
    L.append("## 代表定理以外に非標準の公理出力を持つモジュール")
    L.append("")
    if nonstandard_others:
        for n, others in nonstandard_others:
            L.append(f"- [{n}](../lean/{n}.lean): " + "; ".join(f"`{name}` → [{', '.join(ax)}]" for name, ax in others))
    else:
        L.append("なし。")
    L.append("")
    L.append("## ソースが記録と不一致のモジュール")
    L.append("")
    L.append(", ".join(f"[{n}](../lean/{n}.lean)" for n in stale) if stale else "なし（全モジュールの SHA-256 が記録と一致）。")
    L.append("")
    rc.write_markdown(args.out, L)
    print(f"{len(rows)} rows; no role: {len(no_role)}; stale: {len(stale)}; files with extra nonstandard outputs: {len(nonstandard_others)}")


if __name__ == "__main__":
    main()
