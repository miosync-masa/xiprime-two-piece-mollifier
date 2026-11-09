# ξ′の二枚mollifierと重複度込み零点割合

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

[Weil・DI接続の検証記録](checks/weil-di-proportion-verification.json)は全778ソース・4,405件の公理出力を照合します。主定理の閉包は730モジュールです。最終実行では主定理を新規コンパイルし、先行段階のコンパイルを含む残り777件をソース・依存・成果物ハッシュで照合しました。全778件の新規再ビルドとは区別します。[witness 専用入力の記録](checks/witness-only-proportion-verification.json)は直前のインターフェースの履歴です。[五モジュールの検証記録](checks/wu-proportion-verification.json)・[旧最終監査](checks/wu-proportion-final-audit.json)は旧公理に対する歴史的記録で、下記の改訂後の公理一覧の根拠ではありません。原稿 TeX に正誤注記を追加しました。PDF は注記追加前の版で、再生成は未実施です。数値結果は不変ですが、証明書の原稿出典ハッシュは更新します。

最初に [原稿PDF](paper/manuscript.pdf)、[証明状態](docs/STATUS.md)、[監査ガイド](paper/README.md)をご覧ください。
数値検証の成功と、解析的移植の証明・最終定理のLean化は区別します。simple+on-lineの改善は主張していません。

**正誤表以前の11月7日クリーン検証：** [本体698モジュールの記録](checks/clean-project-verification-2026-11-07.json)と[AF必須依存101モジュールの記録](checks/clean-af-verification-2026-11-07.json)は歴史的記録として変更せず保持しています。現在の監査は別の[Weil・DI接続記録](checks/weil-di-proportion-verification.json)を参照してください。

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

## 収録範囲と初期段階の記録

以下は初期モジュールの役割を記した履歴です。「未完」「残る」とした接続は、現在は後続の算術・moment・Wu計数モジュールから主定理へ接続済みです。現時点の結論と検証範囲は上記および [証明状態](docs/STATUS.md) の最新節を優先してください。

- `paper/`：原稿・数値検証器・出力。既存の監査用bundleを内容変更せず収録。
- `lean/`：kernel恒等式、dual、候補の基本条件、係数の一様上界・Subpower・正規化誤差の極限、明示的なPRZZ公理、AFのAPI検査。
- `tools/`・`checks/`：可搬な再実行scriptと検証記録。
- `docs/`：未形式化部分、再現手順。
- `.github/`：数値検証CI。

`lean/IntegralJet.lean`では、逆作用素・外側積分との微分交換を証明し、元のK2積分functionalの微分を未打切りの`W`評価式へ接続しました。交差項を二倍にまとめる操作も微分・縮約後に証明しています。

`lean/TaylorEnvelope.lean`では、微分後にTaylor打切りした式との差を、逆作用素・積・外側積分・四つのkernel・`W`縮約を通して明示的に囲みました。主定理は`K2_Taylor_enclosure`で、新たな解析公理や未証明の剰余仮定を置きません。

`lean/CoefficientEvaluator.lean`では、その多項式積分を有限beta係数和へ落とし、既存評価器の厳密演算モデルへ接続しました。`finiteEvaluator_cached`は、`fs`の係数加算、積の次数加算、`W`先行縮約、交差項の二倍化、二符号のdual合成を含む同値定理です。`K2_cached_enclosure`は元の微分functionalとこの係数評価式との差を囲みます。

`lean/NumericalGate.lean`では、目標指数関数の下界 `1.1282054105`、dual指数関数の上下界、24次打切りの合成誤差 `10^-6` 以下をLeanで証明しています。元の固定候補との一致も検査します。

`lean/RationalEvaluator.lean`は実行可能な有理数係数リストを既存の係数式へ同定し、`lean/RationalBounds.lean`は固定された負側・正側の有理数上界を `decide +kernel` で検査します。これらを合成した `lean/FixedCertificate.lean` の `fixed_functional_gate` は、**数値条件を仮定せず**、元の微分functionalの実部が目標指数関数を下回ることを証明しました。Leanでの上界は `1.128201`、目標の下界は `1.1282054105` です。`native_decide`、数値公理、外部JSONへの信頼は使いません。

この合成誤差上界はPython検証器の次数別上界と同一ではなく、Python実行やmpmathの丸めを形式検証したものでもありません。算術主項・零点計数への接続も別の未完部分です。

`lean/PRZZAsymptotic.lean`では、PRZZ公理の実際のmomentとgcd主項の差をTで割り、`(-R,-R)`を中心とする各半径`R/4`の双円板で一様に0へ収束することを証明しました。gcd主項の極限からmomentの極限へ移す定理では、未証明のgcd主項の評価を引数に明示しています。

`lean/CompactShiftIntegral.lean`はコンパクトな実区間上の複素パラメータ積分の微分交換と任意階の滑らかさを証明します。`lean/ArithmeticRegularity.lean`は実際のζ積分・gcd和へ適用し、`T > 1`、両shiftの実部が負の領域で二変数の正則性を証明しました。重みの台の制限、ζの極回避、複素冪の枝、混合微分後の正則性を含みます。これにより `ArithmeticRegularity.normalized_mixed_error_tendsto` は、**正則性を仮定に残さず**、任意の有限混合微分の正規化PRZZ誤差が0へ収束することを証明します。正則性部分は通常三公理のみ、誤差収束で追加するのは既存のPRZZ一公理のみです。gcd和から有限kernelへの主項同定・Wu計数はまだ別の未完部分です。

`lean/LogarithmicBudget.lean`は、有限証明書の上界から `1 - log(1.128201)/R > 0.8845` を証明します。正のmomentがこの上界以下と証明できれば同じ余白を使えますが、そのmomentとの同定・Wuの計数不等式そのものはまだ証明していません。

`lean/GcdDecomposition.lean`はliteralなgcd主項をdirect／dualへ厳密に分離し、反射shift `(-B,-A)` と必要な `log T` 正規化を保持します。`lean/ZetaPoleScaling.lean`は外側のζ極の一様極限、`lean/HeightScaling.lean`は `t=Tu` の厳密変数変換と正規化高さ積分の一様極限 `exp(-S)∫Φ` を証明します。これらは通常三公理のみで、新しい解析公理を置きません。**残る核心は `log T × 算術gcd和 → 四つのH項` の一様評価**であり、Euler積・Mellin輪郭移動・剰余の証明は未完です。

元の研究台帳、私的なセッションID、依存ライブラリ本体、作業用キャッシュは含めません。

## 著作権とライセンス

Copyright (c) 2026 MASAMICHI IIZUMI

[MIT License](LICENSE.md) に基づき提供します。
