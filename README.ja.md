# ξ′の二枚mollifier候補

ξ′の臨界線上零点の割合について、**重複度込みで88.45%を目指す明示候補**の監査用プロジェクトです。
専門家向けの五頁原稿、有限主項の数値証明書、Leanの部分的な形式化を収録しています。

最初に [原稿PDF](paper/manuscript.pdf)、[証明状態](docs/STATUS.md)、[監査ガイド](paper/README.md)をご覧ください。
数値検証の成功と、解析的移植の証明・最終定理のLean化は区別します。simple+on-lineの改善は主張していません。

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

## 収録範囲

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

元の研究台帳、私的なセッションID、依存ライブラリ本体、作業用キャッシュは含めません。

## 著作権とライセンス

Copyright (c) 2026 MASAMICHI IIZUMI

[MIT License](LICENSE.md) に基づき提供します。
