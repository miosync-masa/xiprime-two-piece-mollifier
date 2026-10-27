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
- `lean/`：kernel恒等式、dual、候補の基本条件、明示的なPRZZ公理、AFのAPI検査。
- `tools/`・`checks/`：可搬な再実行scriptと検証記録。
- `docs/`：未形式化部分、再現手順。
- `.github/`：数値検証CI。

元の研究台帳、私的なセッションID、依存ライブラリ本体、作業用キャッシュは含めません。

## 著作権とライセンス

Copyright (c) 2026 MASAMICHI IIZUMI

[MIT License](LICENSE.md) に基づき提供します。
