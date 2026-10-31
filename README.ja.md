# ξ′の二枚mollifierと重複度込み零点割合

ξ′の臨界線上零点の割合が、**既存のPRZZ入力の下で、重複度込みで88.45%より真に大きい**ことを導くプロジェクトです。
`WuProportion.strict_proportion` は、ある固定 `b > 0.8845` に対し、十分大きいすべての実数高さ `X` で `b * Ncount 0 X ≤ N0 0 X` を証明します。`ratio_eventually_gt` は実際の比率の不等式です。追加公理は既存の `PRZZ.przz41_case3_K2_profiles` のみで、PRZZ自体の証明は本リポジトリの外部入力です。`LocalizedEstimate`・未証明の計数仮定・単純零点仮定は主定理にありません。

[五モジュールの検証記録](checks/wu-proportion-verification.json)は新規五モジュールを再コンパイルし、既存182モジュールのソースハッシュ照合後に全187モジュールの記録済み公理出力を再監査しています。[最終監査](checks/wu-proportion-final-audit.json)では `WuProportion.lean` を改めてコンパイルし、下記の公理一覧との完全一致を確認しています。全187モジュールやAFのクリーン再ビルドとは区別します。五頁原稿と数値bundleは変更していません。

最初に [原稿PDF](paper/manuscript.pdf)、[証明状態](docs/STATUS.md)、[監査ガイド](paper/README.md)をご覧ください。
数値検証の成功と、解析的移植の証明・最終定理のLean化は区別します。simple+on-lineの改善は主張していません。

## 主定理の公理監査

`#print axioms ratio_eventually_gt` の出力全文を、省略せず掲載します。

```text
'XiPrime8845.WuProportion.ratio_eventually_gt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PRZZ.przz41_case3_K2_profiles]
```

通常三公理以外は既存PRZZ一公理だけで、`sorryAx` はありません。結論は重複度込み・十分大きいすべての実数高さに対する固定の余白です。[リリースノート](docs/RELEASE_NOTES.md)に接続内容と検証範囲を、[主定理のソース](lean/WuProportion.lean)に厳密な定理文を掲載しています。

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
