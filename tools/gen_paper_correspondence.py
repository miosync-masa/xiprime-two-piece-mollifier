#!/usr/bin/env python3
"""Generate docs/paper-correspondence.md from paper/manuscript.tex.

Every theorem/lemma/proposition/hypothesis environment is listed with its label and the
first sentence of its statement. The Lean theorem column is filled by a human
in tools/paper_correspondence_manual.json; the script never guesses. Labels
new to the manuscript are rendered with empty entries. Updating the human
input file requires the explicit --sync-manual option, never --check.
"""
import argparse
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import readability_common as rc  # noqa: E402

MANUSCRIPT = rc.ROOT / "paper" / "manuscript.tex"
MANUAL = rc.ROOT / "tools" / "paper_correspondence_manual.json"
ENV_RE = re.compile(r"\\begin\{(theorem|lemma|proposition|corollary|conjecture|definition|claim|hypothesis)\}"
                    r"(?:\[([^\]]*)\])?\s*(?:\\label\{([^}]*)\})?(.*?)\\end\{\1\}", re.S)


def detex(s):
    s = s.replace(r"\(", "$").replace(r"\)", "$")
    s = re.sub(r"\\label\{[^}]*\}", "", s)
    s = re.sub(r"\\eqref\{([^}]*)\}", r"(\1)", s)
    s = re.sub(r"\\ref\{([^}]*)\}", r"\1", s)
    s = re.sub(r"\\cite(?:\[[^\]]*\])?\{([^}]*)\}", r"[\1]", s)
    s = re.sub(r"\\(emph|textbf|textit|text)\{([^}]*)\}", r"\2", s)
    s = re.sub(r"\\begin\{(equation|align)\*?\}(.*?)\\end\{\1\*?\}", lambda m: " $" + m.group(2).strip() + "$ ", s, flags=re.S)
    s = re.sub(r"\\\[(.*?)\\\]", lambda m: " $" + m.group(1).strip() + "$ ", s, flags=re.S)
    s = s.replace("~", " ").replace("\\,", " ").replace("\\;", " ")
    s = re.sub(r"\s+", " ", s)
    return s.strip()


def first_sentence(body):
    text = detex(body)
    # do not split inside $...$
    out, depth = [], False
    for ch in text:
        if ch == "$":
            depth = not depth
        out.append(ch)
        if ch == "." and not depth:
            break
    return "".join(out).strip()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--manuscript", default=str(MANUSCRIPT))
    ap.add_argument("--manual", default=str(MANUAL))
    ap.add_argument("--sync-manual", action="store_true",
                    help="explicitly add missing labels and normalize the manual JSON")
    ap.add_argument("--out", default=str(rc.ROOT / "docs" / "paper-correspondence.md"))
    args = ap.parse_args()
    tex = Path(args.manuscript).read_text(encoding="utf-8")
    manual_path = Path(args.manual)
    manual = json.loads(manual_path.read_text(encoding="utf-8")) if manual_path.exists() else {}
    counter = {}
    entries = []
    numbered = 0
    hypotheses = 0
    for m in ENV_RE.finditer(tex):
        env, title, label, body = m.groups()
        # This manuscript uses a separate hypothesis counter.
        if env == "hypothesis":
            hypotheses += 1
            number = f"H{hypotheses}"
        else:
            numbered += 1
            number = str(numbered)
        line = tex[:m.start()].count("\n") + 1
        key = label or f"{env}@line{line}"
        counter[key] = counter.get(key, 0) + 1
        entries.append({"label": key, "env": env, "number": number, "title": title or "",
                        "line": line, "summary": first_sentence(body)})
        manual.setdefault(key, {"lean": "", "candidates": [], "note": ""})
    # Rendering (including the parent --check) must not mutate human input.
    if args.sync_manual:
        manual_path.write_text(json.dumps(dict(sorted(manual.items())), ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    stale = sorted(set(manual) - {e["label"] for e in entries})
    L = []
    L.append("# 論文 ↔ Lean 対応表")
    L.append("")
    L.append(f"生成: `python3 tools/gen_paper_correspondence.py`。[{rc.rel(args.manuscript)}](../{rc.rel(args.manuscript)}) の "
             "`theorem` / `lemma` / `proposition` / `hypothesis` 環境を抽出し、ラベルと主張の最初の一文を並べています。"
             "仮定は独立の番号 H1, H2 を用います。仮定の Lean 欄は証明済み定理ではなく命題定義です。"
             "**Lean 定理名の列は人が記入します**（記入先: "
             f"[{rc.rel(manual_path)}](../{rc.rel(manual_path)})。再生成しても記入内容は保持されます）。"
             "「候補」列は README など既存文書に明記された対応だけを候補として挙げ、推測は入れていません。")
    L.append("")
    L.append("通常の生成・`--check` は人手記入 JSON を変更しません。原稿の新しいラベルを JSON に追加するときだけ "
             "`python3 tools/gen_paper_correspondence.py --sync-manual` を明示的に実行してください。")
    L.append("")
    L.append("| # | ラベル | 環境 | 原稿行 | 主張の要約（最初の一文） | Lean 定理名（人が記入） | 候補（根拠付き） | 備考 |")
    L.append("| --- | --- | --- | --- | --- | --- | --- | --- |")
    for e in entries:
        man = manual[e["label"]]
        cands = "<br>".join(f"候補: `{c['name']}`（{c['reason']}）" if isinstance(c, dict) else f"候補: `{c}`" for c in man.get("candidates", []))
        lean = f"`{man['lean']}`" if man.get("lean") else ""
        title = f" [{e['title']}]" if e["title"] else ""
        L.append(f"| {e['number']} | `{e['label']}` | {e['env']}{title} | {e['line']} | {e['summary'].replace('|', chr(92) + '|')} | {lean} | {cands} | {man.get('note', '')} |")
    L.append("")
    L.append("主定理の文面と `#print axioms` 出力は [trust-base.md](trust-base.md) に、Lean 側の代表定理一覧は [modules.md](modules.md) にあります。")
    if stale:
        L.append("")
        L.append("原稿に存在しないラベルが記入ファイルに残っています: " + ", ".join(f"`{s}`" for s in stale))
    L.append("")
    rc.write_markdown(args.out, L)
    print(f"{len(entries)} environments; manual entries {len(manual)}; stale {len(stale)}")


if __name__ == "__main__":
    main()
