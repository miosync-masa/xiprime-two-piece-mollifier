#!/usr/bin/env python3
"""Generate docs/dependency-graph.{json,dot,svg,md} from `import` lines.

Full version (.json/.dot): every local module reachable from WuProportion by
following imports, plus one external node each for Mathlib and AF.
Summary version (.svg/.md): modules bundled by layer and name prefix.
Representative theorems come from the captured compiler output, never typed.
"""
import argparse
import json
import math
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import readability_common as rc  # noqa: E402

SPLIT_MIN = 20          # a first-word group this large is tried for a two-word split
SPLIT_MAX_SUBGROUPS = 12
LAYER_COLORS = {
    rc.LAYER_COUNTING: "#f6d8ae", rc.LAYER_PRZZ_INPUT: "#f4b6b6",
    rc.LAYER_MAIN_TERM: "#cfe3f5", rc.LAYER_NUMERICAL: "#d9efd3",
    rc.LAYER_PRZZ_PROOF: "#e6d5f2", rc.LAYER_OTHER: "#e8e8e8",
    rc.LAYER_AF: "#fff3b0", rc.LAYER_MATHLIB: "#ffffff",
}


def common_prefix(names):
    words = [rc.camel_words(n) for n in names]
    out = []
    for i in range(min(len(w) for w in words)):
        col = {w[i] for w in words}
        if len(col) != 1:
            break
        out.append(col.pop())
    return "".join(out) or names[0]


def group_modules(reachable, modules):
    """Assign each reachable module to a summary group. Rules (documented in the .md):
    1. Layers other than 主項/計数 form one group each.
    2. 主項 and 計数 are grouped by the first CamelCase word of the module name.
    3. A first-word group with >= SPLIT_MIN members is split by its first two words
       when that gives <= SPLIT_MAX_SUBGROUPS subgroups of size >= 2 and the
       leftover singletons are fewer than half of the group.
    4. Within a layer, groups with exactly one module merge into "<layer>: 単独".
    """
    by_first = defaultdict(list)
    for name in sorted(reachable):
        layer, _ = rc.classify(name)
        if layer in (rc.LAYER_MAIN_TERM, rc.LAYER_COUNTING):
            by_first[(layer, rc.camel_words(name)[0])].append(name)
        else:
            by_first[(layer, "")].append(name)
    groups = {}
    for (layer, first), names in sorted(by_first.items()):
        if first and len(names) >= SPLIT_MIN:
            two = defaultdict(list)
            for n in names:
                two["".join(rc.camel_words(n)[:2])].append(n)
            multi = {k: v for k, v in two.items() if len(v) >= 2}
            single = [n for k, v in two.items() if len(v) == 1 for n in v]
            if len(multi) <= SPLIT_MAX_SUBGROUPS and len(single) < len(names) / 2:
                for k, v in sorted(multi.items()):
                    groups[(layer, k)] = v
                if single:
                    groups[(layer, first + "（その他）")] = single
                continue
        groups[(layer, first)] = names
    merged = {}
    singles = defaultdict(list)
    for (layer, key), names in sorted(groups.items()):
        if len(names) == 1 and key:
            singles[layer].extend(names)
        else:
            merged[(layer, key)] = names
    for layer, names in sorted(singles.items()):
        merged[(layer, "単独")] = sorted(names)
    return merged


def build(modules, record, root):
    depth = rc.reachable_from(modules, root)
    reachable = sorted(depth)
    unreached = sorted(set(modules) - set(depth))
    groups = group_modules(reachable, modules)
    group_of = {}
    for key, names in groups.items():
        for n in names:
            group_of[n] = key
    layer_rank = {l: i for i, l in enumerate(rc.LAYER_ORDER)}

    def gid(key):
        layer, k = key
        return layer_rank[layer], k

    ordered_groups = sorted(groups, key=gid)
    ext_used = sorted({l for n in reachable for l in modules[n].external_layers})
    summary_nodes = []
    ids = {}
    for i, key in enumerate(ordered_groups):
        layer, k = key
        names = groups[key]
        rep_module = min(names, key=lambda n: (depth[n], n))
        short, full = rc.representative(modules[rep_module], record.get(rep_module))
        if not k:
            label = layer
        elif k == "単独":
            label = f"{layer}: 単独モジュール群"
        elif k.endswith("（その他）"):
            label = k
        else:
            label = common_prefix(names)
        ids[key] = f"g{i:02d}"
        summary_nodes.append({
            "id": ids[key], "label": label, "layer": layer, "count": len(names),
            "modules": names, "min_depth": depth[rep_module],
            "representative_module": rep_module,
            "representative": full, "representative_axioms": record[rep_module].axioms_of(full) if full else None,
        })
    for layer in ext_used:
        ids[(layer, "")] = f"x{layer}"
        summary_nodes.append({"id": f"x{layer}", "label": layer, "layer": layer,
                              "count": None, "modules": [], "min_depth": None,
                              "representative_module": None, "representative": None,
                              "representative_axioms": None})
    sum_edges = Counter()
    full_edges = []
    for n in reachable:
        for i in modules[n].local_imports:
            full_edges.append([n, i])
            if group_of[n] != group_of[i]:
                sum_edges[(ids[group_of[n]], ids[group_of[i]])] += 1
        for layer in modules[n].external_layers:
            full_edges.append([n, layer])
            sum_edges[(ids[group_of[n]], ids[(layer, "")])] += 1
    module_rows = []
    for n in reachable:
        layer, sub = rc.classify(n)
        short, full = rc.representative(modules[n], record.get(n))
        module_rows.append({
            "name": n, "file": f"lean/{n}.lean", "layer": layer, "sublayer": sub,
            "depth": depth[n], "imports": modules[n].local_imports,
            "external": modules[n].external_imports, "summary_group": ids[group_of[n]],
            "representative": full,
            "representative_axioms": record[n].axioms_of(full) if full else None,
        })
    return {
        "root": root,
        "root_file": f"lean/{root}.lean",
        "edge_direction": "A -> B means A imports B",
        "record": {"path": rc.rel(rc.DEFAULT_RECORD), "sha256": rc.file_sha(rc.DEFAULT_RECORD)},
        "layer_rules": [{"layer": l, "rule": r} for l, r in rc.LAYER_RULES_TEXT],
        "counts": {"local_modules": len(modules), "reachable": len(reachable),
                   "unreached": len(unreached), "edges": len(full_edges)},
        "modules": module_rows,
        "edges": sorted(full_edges),
        "external_nodes": ext_used,
        "unreached": [{"name": n, "layer": rc.classify(n)[0], "sublayer": rc.classify(n)[1]} for n in unreached],
        "summary": {
            "grouping_rules": group_modules.__doc__.strip().splitlines(),
            "nodes": summary_nodes,
            "edges": [{"from": a, "to": b, "count": c} for (a, b), c in sorted(sum_edges.items())],
        },
    }


def write_dot(data, path):
    lines = ["digraph xiprime {", "  rankdir=TB;", '  node [shape=box, fontname="Helvetica", fontsize=9];',
             f'  // root: {data["root"]}; A -> B means A imports B']
    by_layer = defaultdict(list)
    for m in data["modules"]:
        by_layer[m["layer"]].append(m["name"])
    for i, layer in enumerate(l for l in rc.LAYER_ORDER if l in by_layer):
        lines.append(f'  subgraph cluster_{i} {{ label="{layer}"; style=filled; fillcolor="{LAYER_COLORS[layer]}";')
        for n in sorted(by_layer[layer]):
            lines.append(f'    "{n}";')
        lines.append("  }")
    for layer in data["external_nodes"]:
        lines.append(f'  "{layer}" [shape=box3d, style=filled, fillcolor="{LAYER_COLORS[layer]}"];')
    for a, b in data["edges"]:
        lines.append(f'  "{a}" -> "{b}";')
    lines.append("}")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


# ---------------------------------------------------------------------------
# Deterministic layered SVG (no graphviz dependency)
# ---------------------------------------------------------------------------
def layout(nodes, edges, root_id):
    succ = defaultdict(list)
    for e in edges:
        succ[e["from"]].append(e["to"])
    for k in succ:
        succ[k].sort()
    # DFS from root; drop back edges so the remaining graph is a DAG
    state, keep = {}, set()
    stack = [(root_id, iter(succ[root_id]))]
    state[root_id] = 1
    while stack:
        node, it = stack[-1]
        for nxt in it:
            if state.get(nxt) == 1:
                continue  # back edge
            keep.add((node, nxt))
            if nxt not in state:
                state[nxt] = 1
                stack.append((nxt, iter(succ[nxt])))
                break
        else:
            state[node] = 2
            stack.pop()
    ids = [n["id"] for n in nodes]
    layer = {root_id: 0}
    changed = True
    while changed:
        changed = False
        for a, b in sorted(keep):
            if a in layer and layer.get(b, -1) < layer[a] + 1:
                layer[b] = layer[a] + 1
                changed = True
    ext = [n["id"] for n in nodes if n["count"] is None]
    bottom = max(v for k, v in layer.items() if k not in ext) + 1
    for e in ext:
        layer[e] = bottom
    for n in ids:
        layer.setdefault(n, bottom)
    rows = defaultdict(list)
    for n in ids:
        rows[layer[n]].append(n)
    for r in rows:
        rows[r].sort()
    pred = defaultdict(list)
    for e in edges:
        pred[e["to"]].append(e["from"])
    pos = {}
    for r in rows:
        for i, n in enumerate(rows[r]):
            pos[n] = i
    for _ in range(4):
        for r in sorted(rows):
            def bary(n):
                ps = [pos[p] for p in pred[n] if layer[p] < r]
                return (sum(ps) / len(ps) if ps else pos[n], n)
            rows[r].sort(key=bary)
            for i, n in enumerate(rows[r]):
                pos[n] = i
        for r in sorted(rows, reverse=True):
            def bary2(n):
                ss = [pos[s] for s in succ[n] if layer[s] > r]
                return (sum(ss) / len(ss) if ss else pos[n], n)
            rows[r].sort(key=bary2)
            for i, n in enumerate(rows[r]):
                pos[n] = i
    return layer, rows


def esc(s):
    return (s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;").replace('"', "&quot;"))


def wrap_svg_text(text, font_size, width):
    """Conservative one-em glyph bound; never clip/omit identifier characters."""
    limit = max(1, int(width // font_size))
    count = max(1, math.ceil(len(text) / limit))
    short, extra = divmod(len(text), count)
    parts, start = [], 0
    for i in range(count):
        end = start + short + (i < extra)
        parts.append(text[start:end])
        start = end
    return parts


def write_svg(data, path):
    nodes = data["summary"]["nodes"]
    edges = data["summary"]["edges"]
    root_group = next(m["summary_group"] for m in data["modules"] if m["name"] == data["root"])
    layer, rows = layout(nodes, edges, root_group)
    byid = {n["id"]: n for n in nodes}
    LH, PAD, GAP, ROWH = 14, 10, 26, 118

    def lines_of(n):
        if n["count"] is None:
            return [(n["label"], 11, True), ("外部ライブラリ", 11, False)]
        rep = (n["representative"] or "—").split(".")[-1]
        return [(n["label"], 11, True), (f"{n['count']} モジュール", 11, False),
                (rep, 9.5, False)]

    size, display = {}, {}
    for n in nodes:
        ls = lines_of(n)
        w = max(len(text) * fs for text, fs, _ in ls)
        w = max(110, min(300, math.ceil(w) + 2 * PAD))
        display[n["id"]] = [(part, fs, bold) for text, fs, bold in ls
                              for part in wrap_svg_text(text, fs, w - 2 * PAD)]
        size[n["id"]] = (w, LH * len(display[n["id"]]) + 2 * PAD)
    width = max(sum(size[n][0] for n in rows[r]) + GAP * (len(rows[r]) + 1) for r in rows)
    legend_h = 20 + 18 * len([l for l in rc.LAYER_ORDER if any(n["layer"] == l for n in nodes)])
    row_y, cursor = {}, 30
    for r in sorted(rows):
        row_y[r] = cursor
        cursor += max(ROWH, max(size[n][1] for n in rows[r]) + 40)
    height = cursor + 30 + legend_h
    xy = {}
    for r in rows:
        total = sum(size[n][0] for n in rows[r]) + GAP * (len(rows[r]) - 1)
        x = (width - total) / 2
        for n in rows[r]:
            w, h = size[n]
            xy[n] = (x, row_y[r], w, h)
            x += w + GAP
    out = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{int(width)}" height="{int(height)}" '
           f'viewBox="0 0 {int(width)} {int(height)}" font-family="Helvetica, Arial, sans-serif" font-size="11">',
           '<defs><marker id="arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">'
           '<path d="M 0 0 L 10 5 L 0 10 z" fill="#555"/></marker></defs>',
           f'<rect width="100%" height="100%" fill="white"/>',
           f'<text x="{int(width/2)}" y="18" text-anchor="middle" font-size="13" font-weight="bold">'
           f'{esc(data["root"])} からの依存グラフ（要約版、矢印は import 方向）</text>']
    for e in edges:
        ax, ay, aw, ah = xy[e["from"]]
        bx, by, bw, bh = xy[e["to"]]
        x1, y1 = ax + aw / 2, ay + ah
        x2, y2 = bx + bw / 2, by
        dy = max(20, (y2 - y1) / 2)
        sw = 1 + min(3, math.log2(e["count"]) * 0.6)
        out.append(f'<path d="M {x1:.1f} {y1:.1f} C {x1:.1f} {y1+dy:.1f} {x2:.1f} {y2-dy:.1f} {x2:.1f} {y2:.1f}" '
                   f'fill="none" stroke="#555" stroke-opacity="0.55" stroke-width="{sw:.1f}" marker-end="url(#arrow)">'
                   f'<title>{esc(byid[e["from"]]["label"])} → {esc(byid[e["to"]]["label"])}: {e["count"]} import</title></path>')
    for n in nodes:
        x, y, w, h = xy[n["id"]]
        title = n["label"] if n["count"] is None else (
            f'{n["label"]}: ' + ", ".join(n["modules"]) + (f'\n代表定理: {n["representative"]}' if n["representative"] else ""))
        out.append(f'<g><title>{esc(title)}</title>'
                   f'<rect x="{x:.1f}" y="{y:.1f}" width="{w}" height="{h}" rx="6" fill="{LAYER_COLORS[n["layer"]]}" stroke="#333"/>')
        for i, (text, fs, bold) in enumerate(display[n["id"]]):
            weight = ' font-weight="bold"' if bold else ""
            out.append(f'<text x="{x + w/2:.1f}" y="{y + PAD + LH*(i+0.8):.1f}" '
                       f'text-anchor="middle"{weight} font-size="{fs}">{esc(text)}</text>')
        out.append("</g>")
    ly = cursor + 20
    out.append(f'<text x="20" y="{ly}" font-weight="bold">層</text>')
    for i, l in enumerate(x for x in rc.LAYER_ORDER if any(n["layer"] == x for n in nodes)):
        out.append(f'<rect x="20" y="{ly + 8 + 18*i}" width="14" height="12" fill="{LAYER_COLORS[l]}" stroke="#333"/>'
                   f'<text x="40" y="{ly + 18 + 18*i}">{esc(l)}</text>')
    out.append("</svg>")
    path.write_text("\n".join(out) + "\n", encoding="utf-8")


def write_md(data, path):
    nodes = data["summary"]["nodes"]
    edges = data["summary"]["edges"]
    L = []
    L.append("# 依存グラフ（要約版）")
    L.append("")
    L.append(f"主定理モジュール [`{data['root']}`]({'../' + data['root_file']}) から `import` を逆向きにたどって到達できる"
             f"ローカルモジュール **{data['counts']['reachable']} 件**（全 {data['counts']['local_modules']} 件中）を、層と名前の接頭辞で束ねた図です。"
             "矢印は import 方向（A → B は A が B を import）。各ノードはモジュール数と代表定理（そのノードで主定理に最も近いモジュールの、最後の `#print axioms` 対象）を示します。")
    L.append("")
    L.append("生成: `python3 tools/gen_dependency_graph.py`（`import` 行と "
             f"[{data['record']['path']}](../{data['record']['path']}) の記録から自動生成。手書きの依存関係・定理名はありません）。")
    L.append("")
    L.append("- 全体版（機械可読）: [dependency-graph.json](dependency-graph.json), [dependency-graph.dot](dependency-graph.dot)")
    L.append("- 要約版（画像）: [dependency-graph.svg](dependency-graph.svg)")
    L.append("- モジュール表: [modules.md](modules.md)")
    L.append("")
    L.append("要約図の群間に見える循環は、複数モジュールを同じ群へ集約したことによるものです。"
             "Lean モジュールの import 循環を意味しません。個別の辺は JSON / DOT を参照してください。")
    L.append("")
    L.append("```mermaid")
    L.append("flowchart TD")
    for n in nodes:
        if n["count"] is None:
            label = f"{n['label']}<br/>外部ライブラリ"
        else:
            rep = (n["representative"] or "—").split(".")[-1]
            label = f"{n['label']}<br/>{n['count']} モジュール<br/>{rep}"
        L.append(f'  {n["id"]}["{label}"]')
    for e in edges:
        L.append(f'  {e["from"]} --> {e["to"]}')
    for i, layer in enumerate(rc.LAYER_ORDER):
        members = [n["id"] for n in nodes if n["layer"] == layer]
        if members:
            L.append(f"  classDef layer{i} fill:{LAYER_COLORS[layer]},stroke:#333;")
            L.append(f"  class {','.join(members)} layer{i};")
    L.append("```")
    L.append("")
    L.append("## 要約ノード一覧")
    L.append("")
    L.append("| ノード | 層 | モジュール数 | 代表定理 | 代表定理の公理 | 含まれるモジュール |")
    L.append("| --- | --- | --- | --- | --- | --- |")
    for n in nodes:
        if n["count"] is None:
            L.append(f"| {n['label']} | {n['layer']} | 外部 | | | |")
            continue
        rep = f"`{n['representative']}`" if n["representative"] else ""
        mods = ", ".join(f"[{m}](../lean/{m}.lean)" for m in n["modules"])
        L.append(f"| {n['label']} | {n['layer']} | {n['count']} | {rep} | {rc.axioms_label(n['representative_axioms'])} | {mods} |")
    L.append("")
    L.append("## 層の割り当て規則（モジュール名から機械的に判定）")
    L.append("")
    L.append("| 層 | 規則 |")
    L.append("| --- | --- |")
    for layer, rule in rc.LAYER_RULES_TEXT:
        L.append(f"| {layer} | {rule} |")
    L.append("")
    L.append("要約ノードへの束ね方:")
    L.append("")
    for line in data["summary"]["grouping_rules"]:
        L.append(f"    {line}")
    L.append("")
    other = [m for m in data["modules"] if m["layer"] == rc.LAYER_OTHER]
    L.append(f"「{rc.LAYER_OTHER}」に入った到達可能モジュール: " + (", ".join(f"[{m['name']}](../lean/{m['name']}.lean)" for m in other) or "なし"))
    L.append("")
    L.append("## 主定理から到達しないモジュール")
    L.append("")
    L.append(f"`{data['root']}` の import 閉包に含まれないローカルモジュールは **{data['counts']['unreached']} 件**です。"
             "これらは主定理の論理に入りません（別の根、たとえば `PRZZMomentOptimal` から到達するものを含みます）。")
    L.append("")
    by = defaultdict(list)
    for u in data["unreached"]:
        by[(u["layer"], u["sublayer"] or "")].append(u["name"])
    rank = {l: i for i, l in enumerate(rc.LAYER_ORDER)}
    L.append("| 層 | 細分 | 件数 | モジュール |")
    L.append("| --- | --- | --- | --- |")
    for (layer, sub), names in sorted(by.items(), key=lambda kv: (rank[kv[0][0]], kv[0][1])):
        L.append(f"| {layer} | {sub} | {len(names)} | " + ", ".join(f"[{n}](../lean/{n}.lean)" for n in names) + " |")
    L.append("")
    rc.write_markdown(path, L)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=rc.ROOT_MODULE)
    ap.add_argument("--out", default=str(rc.ROOT / "docs"))
    args = ap.parse_args()
    modules = rc.load_modules()
    record, _ = rc.load_verified_record(modules)
    data = build(modules, record, args.root)
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    (out / "dependency-graph.json").write_text(json.dumps(data, ensure_ascii=False, indent=1) + "\n", encoding="utf-8")
    write_dot(data, out / "dependency-graph.dot")
    write_svg(data, out / "dependency-graph.svg")
    write_md(data, out / "dependency-graph.md")
    print(f"reachable {data['counts']['reachable']}, unreached {data['counts']['unreached']}, "
          f"summary nodes {len(data['summary']['nodes'])}, summary edges {len(data['summary']['edges'])}")


if __name__ == "__main__":
    main()
