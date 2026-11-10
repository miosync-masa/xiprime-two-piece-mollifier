# ξ′の二枚mollifierと重複度込み零点割合

公開ソフトウェア版：[v0.2.0 — The PRZZ axiom is gone: 88.45% from explicit Weil and Deshouillers–Iwaniec hypotheses](https://github.com/miosync-masa/xiprime-two-piece-mollifier/releases/tag/v0.2.0)。
版 DOI：[10.5281/zenodo.24101490](https://doi.org/10.5281/zenodo.24101490)。
固定コミット：`8fbfbe376d879274c5be7e2f655551c967dfdf99`。
今回の文献・投稿用メタデータ改訂は、この保存版の公開後の更新です。タグ・保存済みPDFは上書きしません。

> **主定理と外部入力（三行要約）**
> 1. `XiPrime8845.WuProportion.ratio_eventually_gt`：十分大きいすべての実数 `X` で `0.8845 < N0 0 X / Ncount 0 X`。`N0` は ξ′ の臨界線上零点の重複度込みの個数、`Ncount` は ξ′ の全零点の個数（AF の `Zeta23.XiPrime` の計数）。
> 2. 主定理は `hWeil : WeilIncomplete` と `hDI : DeshouillersIwaniecLemma1` を明示的に受け取ります。この二つの深い評価自体を証明したとは主張しません。
> 3. 旧 PRZZ witness 公理は `PRZZFamilyMomentOptimal`・`PRZZWitnessBridge` を経て導く定理に置換しました。公開接続は `PRZZProvedInput` にあり、ローカル解析公理の宣言はありません。
>
> **v0.1.0 正誤表：** 一般プロファイル公理をまず密度に合う witness 専用入力へ限定し、現在はその評価を Weil・DI の仮定から導く定理に置換しました。有限 witness 主項はシフト交換に厳密に不変で、証明された数値区間は不変です。[STATUS](docs/STATUS.md#v010-erratum-shift-placement-7-november-2026)参照。以下の自動生成資料は、現在のソースと照合したWeil・DI接続の監査記録から再生成しています。
>
> 読み方の資料（`import` 行とコンパイラ出力から `tools/generate_readability_docs.py` で自動生成）：[依存グラフ](docs/dependency-graph.md) · [モジュール表](docs/modules.md) · [論文 ↔ Lean 対応表](docs/paper-correspondence.md) · [信頼の基盤](docs/trust-base.md)。10 月 28 日以前の開発台帳は [docs/history.md](docs/history.md) に移しました。

ξ′の臨界線上零点の割合が、**明示したWeil・DI仮定の下で、重複度込みで88.45%より真に大きい**ことを導くプロジェクトです。
`WuProportion.strict_proportion` は、ある固定 `b > 0.8845` に対し、十分大きいすべての実数高さ `X` で `b * Ncount 0 X ≤ N0 0 X` を証明します。`ratio_eventually_gt` は実際の比率の不等式です。旧 `PRZZ.przz41_case3_K2_witness` は公理ではなく証明済み定理となり、Weil・DIの仕様自体は明示的な仮定に残ります。`LocalizedEstimate`・未証明の計数仮定・単純零点仮定は主定理にありません。

[現行の全件クリーン検証記録](checks/clean-verification-2026-11-10-local.json)では、**本体778本をすべて新規コンパイルし、再利用は0本**です。4,405件の公理出力を検査し、主定理の閉包730モジュールも含みます。[上流AFの新記録](checks/clean-verification-2026-11-10-af.json)では、固定コミットの必須依存**101本をすべて新規ビルド**し、旧AF成果物は使っていません。Mathlibとパッケージのみ固定版キャッシュを再利用します。実測コンパイル時間はAF190.253秒、本体2,939.546秒（6並列枠）、合計約52分10秒です。[旧Weil・DI接続記録](checks/weil-di-proportion-verification.json)の「1本新規・777本再利用」は当時の実行の履歴として変更せず保持しています。[witness専用入力の記録](checks/witness-only-proportion-verification.json)・[五モジュールの記録](checks/wu-proportion-verification.json)・[旧最終監査](checks/wu-proportion-final-audit.json)も、それぞれの旧インターフェースの履歴です。

2026年11月10日に原稿TeXとPDFを現行のWeil・DI条件付き証明へ改訂し、今回の全件クリーン検証を反映しました。[描画検証記録](checks/manuscript-render-verification.json)に全ページの目視確認と対象ハッシュを記録しています。数値結果は不変で、証明書では原稿出典ハッシュのみを更新しました。

査読はまず [現行の査読ガイド](docs/REVIEW_GUIDE.md)、[定理文と信頼境界](docs/trust-base.md)、[証明状態](docs/STATUS.md)の順でご覧ください。改訂原稿とPDFは両入力の量化子・正確な数式、49対の一様評価、主項と実計数への接続を記述しています。[論文↔Lean対応表](docs/paper-correspondence.md)は仮定の定義と定理の対応を区別し、Pythonの細い数値区間には同値なLean定理を割り当てていません。独立した人間査読の完了を意味するものではありません。
数値検証の成功と、解析的移植の証明・最終定理のLean化は区別します。simple+on-lineの改善は主張していません。

**正誤表以前の11月7日クリーン検証：** [本体698モジュールの記録](checks/clean-project-verification-2026-11-07.json)と[AF必須依存101モジュールの記録](checks/clean-af-verification-2026-11-07.json)は歴史的記録として変更せず保持しています。現在の監査は[11月10日の全件クリーン検証](checks/clean-verification-2026-11-10-local.json)を参照してください。

## 保存版の引用

MASAMICHI IIZUMI (2026), *miosync-masa/xiprime-two-piece-mollifier:
v0.2.0 — The PRZZ axiom is gone: 88.45% from explicit Weil and
Deshouillers–Iwaniec hypotheses*. Zenodo.
[doi:10.5281/zenodo.24101490](https://doi.org/10.5281/zenodo.24101490)。
再現には固定タグ・コミットと、その版の
[査読ガイド](https://github.com/miosync-masa/xiprime-two-piece-mollifier/blob/v0.2.0/docs/REVIEW_GUIDE.md)を使ってください。

二つの入力は文献上の既知の評価で、新しい予想ではありません。
「conditional」は、その証明自体を今回のLean開発に含めていないという形式化上の境界を指します。
原稿の第2.1節に不完全和への完備化を記し、DIの出典を明示しています。
正確なLean仕様と原典の対応の独立査読は、別途重要です。
現行原稿には著者・連絡先、MSC・キーワード、データ／コード入手先、資金提供・利益相反、
AFへの謝辞、およびClaude・ChatGPT/Codexの使用宣言を追加しています。


## 主定理の公理監査

`#print axioms ratio_eventually_gt` の出力全文を、省略せず掲載します。

```text
'XiPrime8845.WuProportion.ratio_eventually_gt' depends on axioms: [propext, Classical.choice, Quot.sound]
```

標準三公理以外の公理と `sorryAx` はありません。ただし Weil・DI は定理の明示的引数です。この公理一覧は、両評価自体を証明したという意味ではありません。結論は重複度込み・十分大きいすべての実数高さに対する固定の余白です。[リリースノート](docs/RELEASE_NOTES.md)に接続内容と検証範囲を、[主定理のソース](lean/WuProportion.lean)に厳密な定理文を掲載しています。

## 元のmoment評価：2026年11月7日

[`PRZZMomentOptimal.moment_bound`](lean/PRZZMomentOptimal.lean) で、実際のζのmomentから `PRZZCoupledAFE.diagonalMain` を引いた誤差を

$$C T^\tau\bigl(N^{7/4}+T^{1/2}N^{7/8}\bigr)$$

へ接続しました。Weil不完全和評価・DI Lemma 1は明示的仮定です。係数ラベル、滑らかな単調plateau seed、支持が `[1,2]` の滑らかな時間cutoffを固定し、十分大きい高さ、`1 ≤ N ≤ T^(4/7)`、`N+1 ≤ T`、有界な対数スケールシフトと正の分離 `r ≤ ‖A+B‖` に対して定数を一様化しています。実際の両枝Fourier尾部も評価済みで、この定理に尾部予算の仮定は残りません。[現在の証明状態](docs/STATUS.md#original-moment-estimate-7-november-2026)を参照してください。

固定ラベル版だけでは公開入力の置換には足りませんでした。現在は高さ依存の七基底族を扱う [`PRZZFamilyMomentOptimal`](lean/PRZZFamilyMomentOptimal.lean) と、公開積分・正配置主項を同定する [`PRZZWitnessBridge.witness_estimate`](lean/PRZZWitnessBridge.lean) を経て、[`PRZZProvedInput`](lean/PRZZProvedInput.lean) から計数側へ接続しています。無条件の零点割合や単純零点の新主張はありません。

## PRZZ入力の分解：2026年11月2日（履歴）

[`PRZZActiveRows.literal_absorbed`](lean/PRZZActiveRows.lean) で、空の元行を除外し、非空行ごとの外側質量を保持したまま、元のliteralなA-starを次の形で評価しました。

$$
|A^*|\le C T^{\delta+\gamma}\frac{\lambda}{d}
\bigl(N^{7/4}+T^{1/2}N^{7/8}\bigr)
\int_{\mathbb R}(1+|t|)|\operatorname{mellin}\Phi(it)|\,dt.
$$

Weilの不完全和評価とDI Lemma 1は、新しい公理ではなく明示的な`Prop`仮定です。Type I・Type II・小スケールの三場合、allocation和、dyadic多重度の吸収を接続しました。周波数・スケール条件、シフトの分離、損失指数の厳密な余白は仮定に残しています。定数は後から量化する高さ・行データに一様ですが、cutoff関数は定数より先に固定します。詳細は[証明状態](docs/STATUS.md#przz-decomposition-milestone-2-november-2026)をご覧ください。

この段階はPRZZ公理そのものの置換完了ではありませんでした。当時未完だったAFE・切断除去・実核の接続は、現在は上記の元のmoment評価まで発展しています。その後、上記の有限基底族への一様化と公開入力への接続を追加しました。

## 再実行

このディレクトリで実行します。

```sh
python3 -m venv .venv
. .venv/bin/activate
python -m pip install -r requirements.txt
python tools/verify_release.py
```

依存はmpmath 1.3.0のみ。ファイルのSHA256、元の有限検証器、保存JSONとの完全一致を確認します。
Leanは別途、固定版AFのビルド済み環境が必要です。[再現手順](docs/REPRODUCIBILITY.md)を参照してください。

## 収録範囲と開発履歴

- `lean/`：現行の定理・明示的仮定・固定依存情報。
- `checks/`：現在の検証記録と、変更せず保持した過去の記録。
- `paper/`：現行の条件付き証明に合わせた改訂TeX・PDF、独立の数値検証器。
- `docs/`：査読入口、現状、再現手順、生成された依存資料と開発履歴。
- `tools/`：検証・資料生成スクリプト。`.github/` のCIは数値・配布・資料生成の確認で、Lean再ビルドではありません。

旧READMEの初期モジュール説明は [history.md](docs/history.md#archived-japanese-readme-module-notes) へ保存しました。当時の「未完」「PRZZ公理を仮定」は現在の状態を示しません。現行の数学的ソースは `2418fd5` の接続を保持し、本整備では証明コード・数値計算を変更していません。

## 著作権とライセンス

Copyright (c) 2026 MASAMICHI IIZUMI

[MIT License](LICENSE.md) に基づき提供します。
