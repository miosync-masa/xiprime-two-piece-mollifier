# 論文 ↔ Lean 対応表

生成: `python3 tools/gen_paper_correspondence.py`。[paper/manuscript.tex](../paper/manuscript.tex) の `theorem` / `lemma` / `proposition` 環境を抽出し、ラベルと主張の最初の一文を並べています。**Lean 定理名の列は人が記入します**（記入先: [tools/paper_correspondence_manual.json](../tools/paper_correspondence_manual.json)。再生成しても記入内容は保持されます）。「候補」列は README など既存文書に明記された対応だけを候補として挙げ、推測は入れていません。

通常の生成・`--check` は人手記入 JSON を変更しません。原稿の新しいラベルを JSON に追加するときだけ `python3 tools/gen_paper_correspondence.py --sync-manual` を明示的に実行してください。

| # | ラベル | 環境 | 原稿行 | 主張の要約（最初の一文） | Lean 定理名（人が記入） | 候補（根拠付き） | 備考 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | `thm:main` | theorem [Claim submitted for verification] | 56 | The explicit construction below gives $\liminf_{T\to\infty}\frac{N_{\xi',c}(T)}{N(T)}>0.8845.$ |  | 候補: `XiPrime8845.WuProportion.ratio_eventually_gt`（README「Final theorem and axiom audit」節が主定理として掲載）<br>候補: `XiPrime8845.WuProportion.strict_proportion`（README 冒頭。固定余白 b > 0.8845 の形） | Lean 版は PRZZ.przz41_case3_K2_profiles を公理として仮定した条件付き |
| 2 | `lem:count` | lemma | 102 | For the fixed data above, suppose $\frac1T\int_T^{2T}\|U(a+\ii t)\Psi(a+\ii t)\|^2\dd t=M+o(1),$ and the same mollified second moments for each $L^{-k}\zeta^{(k)}$, $0\le k\le6$, are bounded. |  |  |  |
| 3 | `prop:mainterm` | proposition | 270 | For (eq:psi), the constant in (eq:moment) is (eq:I). |  |  |  |
| 4 | `lem:finite` | lemma | 319 | For the rational data (eq:constants)--(eq:p2), the functional (eq:I) satisfies the outward enclosure $1.12818163807203565629105 <M<1.12818163807203565629124.$ Moreover, $1.12820541062467513417945 <e^{R(1-0.8845)}<1.12820541062467513417947.$ |  | 候補: `XiPrime8845.FixedCertificate.fixed_functional_gate`（README「Executable rational evaluator and fixed finite gate」行。ただし Lean の囲いは 1.128201 で、原稿 (eq:interval) の Python 区間とは別物） | Python 区間（paper/verify.py）と Lean 有限ゲートは独立の確認 |

主定理の文面と `#print axioms` 出力は [trust-base.md](trust-base.md) に、Lean 側の代表定理一覧は [modules.md](modules.md) にあります。
