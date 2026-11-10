# 信頼の基盤（trust base）

生成: `python3 tools/gen_trust_base.py --af <固定 AF checkout>`。定理文は Lean ソースから、公理出力は [checks/clean-verification-2026-11-10-local.json](../checks/clean-verification-2026-11-10-local.json)（SHA-256 `62f738653be50059…`）から、ライブラリの固定情報は `lake-manifest.json` / `lean-toolchain` と [lean/dependencies.json](../lean/dependencies.json) から自動抽出しています。

生成前に全ローカル Lean ソースの SHA-256 と記録の完全一致、成功終了コード、`sorryAx` / コンパイルエラーの不在を確認します。不一致・記録欠落時には生成を中止します。これは新たな Lean 再ビルドではなく、記録と現在のソースの照合です。

## 1. 主定理

[lean/WuProportion.lean](../lean/WuProportion.lean) の `XiPrime8845.WuProportion.ratio_eventually_gt`:

```lean
/-- Literal quotient statement. The denominator is eventually positive,
as supplied by the actual AF zero-count growth theorem. -/
theorem ratio_eventually_gt
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1) :
    ∀ᶠ X : ℝ in atTop, (0.8845:ℝ) < (N0 0 X:ℝ)/(Ncount 0 X:ℝ) := by
```

同じファイルの `XiPrime8845.WuProportion.strict_proportion`（固定余白の形）:

```lean
/-- More than 88.45 percent, with multiplicity, under explicit Weil and DI
hypotheses. A strict margin is retained; this is stronger than an eventual
non-strict 0.8845 bound. -/
theorem strict_proportion
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1) : StrictProportion := by
```

`StrictProportion` の定義（[lean/WuDyadicCounting.lean](../lean/WuDyadicCounting.lean)）:

```lean
/-- The final intended strict proportion assertion, for the literal AF
counts. This definition records a target, not a new assumption or axiom. -/
def StrictProportion : Prop :=
  ∃ b : ℝ, (0.8845:ℝ) < b ∧ ∀ᶠ X : ℝ in atTop,
    b*(Ncount 0 X:ℝ) ≤ (N0 0 X:ℝ)
```

`proportion` の定義（[lean/WuDyadicCounting.lean](../lean/WuDyadicCounting.lean)）:

```lean
def proportion : ℝ := 1-Real.log WitnessMomentBound.countingCap/PRZZAsymptotic.R
```

今回のビルド（Lean (version 4.33.0-rc2, arm64-apple-darwin24.6.0, commit d8b18978322de05a8f3dba51ef03cf5461676c17, Release)）での `#print axioms ratio_eventually_gt` 出力の全文:

```text
'XiPrime8845.WuProportion.ratio_eventually_gt' depends on axioms: [propext, Classical.choice, Quot.sound]
```

同ファイルの他の `#print axioms` 出力:

```text
'XiPrime8845.WuProportion.dyadic_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]
'XiPrime8845.WuProportion.cumulative_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]
'XiPrime8845.WuProportion.strict_proportion' depends on axioms: [propext, Classical.choice, Quot.sound]
```

標準三公理以外: なし。`sorryAx` は含まれない。

## 2. 外部入力

### 2a. 旧公開入力を置き換える証明済み定理: `XiPrime8845.PRZZ.przz41_case3_K2_witness`

[lean/PRZZProvedInput.lean](../lean/PRZZProvedInput.lean) のファイル冒頭コメント:

> Proved replacement of the former public PRZZ witness axiom.
> DeepInputs bundles explicit Weil/DI hypotheses, not an axiom or a default
> instance. Headline theorems expose both hypotheses separately.

```lean
/-- The former witness input, now proved from the two stated deep inputs. -/
theorem przz41_case3_K2_witness
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (theta : ℝ) (hTheta0 : 0 < theta) (hTheta1 : theta < 4/7)
    (Phi : ℝ → ℝ) (hPhi : SmoothWeight Phi)
    (shiftBound poleGap eps : ℝ) (hShift : 0 < shiftBound)
    (hGap : 0 < poleGap) (hEps : 0 < eps) :
    ∃ C T0 : ℝ, 0 < C ∧ 2 ≤ T0 ∧ ∀ T : ℝ, T0 ≤ T → ∀ A B : ℂ,
      ‖A‖ ≤ shiftBound → ‖B‖ ≤ shiftBound → poleGap ≤ ‖A+B‖ →
      ‖twistedMoment witness witness theta T Phi A B -
        densityGcdMainTerm witness witness theta T Phi A B‖ ≤
        C * Real.rpow T eps *
          (Real.rpow (length theta T) (7/4) +
           Real.rpow (length theta T) (7/8) * Real.rpow T (1/2)) :=
  PRZZWitnessBridge.witness_estimate hWeil hDI theta hTheta0 hTheta1 Phi hPhi
    shiftBound poleGap eps hShift hGap hEps
```

原典（README の参考文献から）: K. Pratt, N. Robles, A. Zaharescu and D. Zeindler, *More than five-twelfths of the zeros of ζ are on the critical line*, Res. Math. Sci. **7** (2020), Article 2, [doi:10.1007/s40687-019-0199-8](https://doi.org/10.1007/s40687-019-0199-8). The theorem/page references use [arXiv:1802.10521v3](https://arxiv.org/pdf/1802.10521v3), Theorem 4.1 and the main-term analysis.

照合メモ: この定理は旧 witness 専用入力と同じ結論を Weil/DI の明示的仮定から導きます。主項は literal な gcd/lcm 二重和、誤差は `C T^eps (N^{7/4} + N^{7/8} T^{1/2})`。元の入力との結論の一致は Lean が検査し、Weil/DI の仕様と原典の対応は別途人による照合対象です。

### 2b. `WeilIncomplete` と `DeshouillersIwaniecLemma1`（`Prop` としての仕様。公理ではない）

定義ファイル [lean/PRZZKloostermanInputs.lean](../lean/PRZZKloostermanInputs.lean) は、主定理 `WuProportion` の import 閉包に含まれます（`PRZZFamilyMomentOptimal` の閉包には含まれます）。現在は主定理の二つの明示的仮定です。Prop として定義されているだけで、その仕様自体をこのリポジトリで証明したという意味ではありません。

ファイル冒頭コメント（原典と照合メモ）:

> L0 specifications, NOT axioms and NOT proved estimates.
>
> DI source: Deshouillers--Iwaniec, *Power mean-values for Dirichlet's
> polynomials and the Riemann zeta-function, II*, Acta Arith. 43 (1984),
> 305--312, Lemma 1 on p. 310, DOI 10.4064/aa-43-3-305-312.
> Publisher scan: https://www.impan.pl/shop/en/publication/transaction/download/product/104164
> PRZZ v3 reference [27] prints volume 48; the original scan/publisher is 43.
>
> The incomplete Weil input below is a completion corollary, NOT a literal
> theorem statement in Weil (1948). PRZZ v3 p. 21 invokes this corollary
> together with partial summation. The weighted Type I and Type II adapters
> are NOT supplied by these definitions. No implication to PRZZ 4.1 is asserted.

`XiPrime8845.PRZZKloostermanInputs.WeilIncomplete`:

```lean
/-- Explicit unweighted completion obligation behind PRZZ's Type I step.
The q^eps loss absorbs divisor/log factors; the gcd is retained (not
silently set to one). M and H are unrestricted, hence the 1+H/q factor.
Proving WeilPrime -> this statement still requires prime-power estimates,
CRT and completion; it is intentionally NOT claimed as a theorem here. -/
def WeilIncomplete : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ q : ℕ, 1 ≤ q → ∀ a : ℤ, ∀ M H : ℕ,
      ‖incompleteSum q a M H‖ ≤
        C*Real.rpow q (1/2+ε)*(a.natAbs.gcd q)*(1+(H:ℝ)/q)
```

```text
'XiPrime8845.PRZZKloostermanInputs.WeilIncomplete' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`XiPrime8845.PRZZKloostermanInputs.DeshouillersIwaniecLemma1`:

```lean
/-- DI Lemma 1, p. 310, with the implied constant quantified BEFORE rho,
the four length parameters and the coefficients. rho is a positive integer
(the rho introduced before (10) on the same page). No extra smoothness,
factorization of b(u,v), or coprimality of u is inserted. -/
def DeshouillersIwaniecLemma1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧
    ∀ C D U V : ℝ, 1 ≤ C → 1 ≤ D → 1 ≤ U → 1 ≤ V →
    ∀ rho : ℕ, 1 ≤ rho → ∀ b : ℕ → ℕ → ℂ,
    (∀ u ∈ Icc 1 ⌊U⌋₊, ∀ v ∈ Icc 1 ⌊V⌋₊, ‖b u v‖ ≤ 1) →
      diSum C D U V rho b ≤ K*diBound ε C D U V rho
```

```text
'XiPrime8845.PRZZKloostermanInputs.DeshouillersIwaniecLemma1' depends on axioms: [propext, Classical.choice, Quot.sound]
```

<details><summary>lean/PRZZKloostermanInputs.lean 全文（補助定義 `e`, `inverseResidue`, `completeSum`, `WeilPrime`, `incompleteSum`, `diSum`, `diBound` を含む）</summary>

```lean
import Mathlib

/-! L0 specifications, NOT axioms and NOT proved estimates.

DI source: Deshouillers--Iwaniec, *Power mean-values for Dirichlet's
polynomials and the Riemann zeta-function, II*, Acta Arith. 43 (1984),
305--312, Lemma 1 on p. 310, DOI 10.4064/aa-43-3-305-312.
Publisher scan: https://www.impan.pl/shop/en/publication/transaction/download/product/104164
PRZZ v3 reference [27] prints volume 48; the original scan/publisher is 43.

The incomplete Weil input below is a completion corollary, NOT a literal
theorem statement in Weil (1948). PRZZ v3 p. 21 invokes this corollary
together with partial summation. The weighted Type I and Type II adapters
are NOT supplied by these definitions. No implication to PRZZ 4.1 is asserted.
-/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZKloostermanInputs

def e (x : ℝ) : ℂ := Complex.exp (2*Real.pi*Complex.I*(x:ℂ))

/-- Least nonnegative representative of the modular inverse. Every use in
the estimates is guarded by coprimality; this is not the real reciprocal. -/
def inverseResidue (q n : ℕ) : ℕ := ((n : ZMod q)⁻¹).val

def completeSum (q : ℕ) (a b : ℤ) : ℂ :=
  ∑ n ∈ (range q).filter (fun n => n.Coprime q),
    e (((a:ℝ)*n+(b:ℝ)*inverseResidue q n)/q)

/-- Prime-field form of Weil's bound (odd prime, both coefficients nonzero).
Weil, *On some exponential sums*, PNAS 34 (1948), 204--207, p. 207,
the prime-field display following the Kloosterman-sum display:
https://pmc.ncbi.nlm.nih.gov/articles/PMC1079093/
Paper (p,c,d,x) = Lean (p,a,b,n); coprimality expresses c,d nonzero mod p.
See also Harcos, *Weil's bound for Kloosterman sums*, Theorem 1, p. 1,
https://users.renyi.hu/~gharcos/weil.pdf.
This proposition is an input type, with no inhabitant supplied here. -/
def WeilPrime : Prop :=
  ∀ p : ℕ, p.Prime → 2 < p → ∀ a b : ℤ,
    a.natAbs.Coprime p → b.natAbs.Coprime p →
    ‖completeSum p a b‖ ≤ 2*Real.sqrt p

def incompleteSum (q : ℕ) (a : ℤ) (M H : ℕ) : ℂ :=
  ∑ n ∈ (Ioc M (M+H)).filter (fun n => n.Coprime q),
    e ((a:ℝ)*inverseResidue q n/q)

/-- Explicit unweighted completion obligation behind PRZZ's Type I step.
The q^eps loss absorbs divisor/log factors; the gcd is retained (not
silently set to one). M and H are unrestricted, hence the 1+H/q factor.
Proving WeilPrime -> this statement still requires prime-power estimates,
CRT and completion; it is intentionally NOT claimed as a theorem here. -/
def WeilIncomplete : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ q : ℕ, 1 ≤ q → ∀ a : ℤ, ∀ M H : ℕ,
      ‖incompleteSum q a M H‖ ≤
        C*Real.rpow q (1/2+ε)*(a.natAbs.gcd q)*(1+(H:ℝ)/q)

/-- The outer sums and inner absolute value are exactly those of DI Lemma 1.
Paper (C,D,U,V,rho,b(u,v)) = Lean (C,D,U,V,rho,b u v).
Real upper bounds are encoded using natural floors. -/
def diSum (C D U V : ℝ) (rho : ℕ) (b : ℕ → ℕ → ℂ) : ℝ :=
  ∑ c ∈ Icc 1 ⌊C⌋₊, ∑ d ∈ (Icc 1 ⌊D⌋₊).filter (fun d => c.Coprime (rho*d)),
    ‖∑ u ∈ Icc 1 ⌊U⌋₊, ∑ v ∈ (Icc 1 ⌊V⌋₊).filter (fun v => v.Coprime c),
      b u v * e ((u:ℝ)*inverseResidue c (rho*v*d)/c)‖

def diBound (ε C D U V : ℝ) (rho : ℕ) : ℝ :=
  Real.rpow (C*D*U*V) (1/2+ε) *
    (Real.sqrt (C*D) + Real.rpow (U+V) (1/4) *
      Real.rpow (C*D*(U+(rho:ℝ)*V)*(C+(rho:ℝ)*V^2)+(rho:ℝ)*U*V^2*D^2) (1/4))

/-- DI Lemma 1, p. 310, with the implied constant quantified BEFORE rho,
the four length parameters and the coefficients. rho is a positive integer
(the rho introduced before (10) on the same page). No extra smoothness,
factorization of b(u,v), or coprimality of u is inserted. -/
def DeshouillersIwaniecLemma1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧
    ∀ C D U V : ℝ, 1 ≤ C → 1 ≤ D → 1 ≤ U → 1 ≤ V →
    ∀ rho : ℕ, 1 ≤ rho → ∀ b : ℕ → ℕ → ℂ,
    (∀ u ∈ Icc 1 ⌊U⌋₊, ∀ v ∈ Icc 1 ⌊V⌋₊, ‖b u v‖ ≤ 1) →
      diSum C D U V rho b ≤ K*diBound ε C D U V rho

#print axioms WeilPrime
#print axioms WeilIncomplete
#print axioms DeshouillersIwaniecLemma1
end XiPrime8845.PRZZKloostermanInputs
```

</details>

### 2c. 参考: `PRZZFamilyMomentOptimal.moment_bound`（主定理の証明経路）

[lean/PRZZFamilyMomentOptimal.lean](../lean/PRZZFamilyMomentOptimal.lean) の `XiPrime8845.PRZZFamilyMomentOptimal.moment_bound` は Weil / DI を仮定にとる moment 評価で、`WuProportion` からは到達可能です。今回のビルドの出力:

```text
'XiPrime8845.PRZZFamilyMomentOptimal.moment_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

<details><summary>定理文</summary>

```lean
/-- Every positive final loss is available; none is fixed by the Weil/DI
loss parameters. The two coordinate vectors and the basis may vary with T. -/
theorem moment_bound (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (P Phi : ℝ → ℝ)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ))) (hm : Antitone P)
    (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hPhi : PRZZ.SmoothWeight Phi) (tau S r : ℝ)
    (htau : 0 < tau) (hS : 0 ≤ S) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (theta : ℝ) (N : ℕ)
      (z w : Fin 7 → ℂ) (A B : ℂ),
      0 < theta → 1 ≤ N → (N:ℝ)+1 ≤ T → (N:ℝ) ≤ T^(4/7:ℝ) →
      1 ≤ Real.log (PRZZ.length theta T) → (N:ℝ) ≤ PRZZ.length theta T →
      (∀ i, ‖z i‖ ≤ 2) → (∀ i, ‖w i‖ ≤ 2) →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖error Phi N T A B (family (PRZZWitnessBasis.basis theta T) z)
        (family (PRZZWitnessBasis.basis theta T) w)‖ ≤
        C*T^tau*PRZZOptimalPowers.target N T := by
```

</details>

## 3. 依存する外部ライブラリ

AF checkout の `lake-manifest.json` に記録された全パッケージ:

| パッケージ | rev | URL |
| --- | --- | --- |
| Cli | `1319485273bf87833fa472afbcefdedecb16b45f` | https://github.com/leanprover/lean4-cli |
| LeanSearchClient | `f5c090429dff3cf66cb65562526c9ea6e8edfbcb` | https://github.com/leanprover-community/LeanSearchClient |
| Qq | `ef42f8944eaf5b6cbfbe75d1917d824c7dd6cf33` | https://github.com/leanprover-community/quote4 |
| aesop | `7db8190085343afde2f5d2cdcc9bac719b6ec02c` | https://github.com/leanprover-community/aesop |
| batteries | `76e1c118b0700b4ceafe99532e887d6431625e1a` | https://github.com/leanprover-community/batteries |
| importGraph | `bb3469a87774349fe01898d8bf2fc6a1ce6411ca` | https://github.com/leanprover-community/import-graph |
| mathlib | `51e6992efd06126df61a496bebf8f49482a4e129` | https://github.com/leanprover-community/mathlib4 |
| plausible | `123d15766ba49356c02ebad2a4462dfe12d79899` | https://github.com/leanprover-community/plausible |
| proofwidgets | `222c58dad7706a6e7cae46c0edd65ea881d3ee27` | https://github.com/leanprover-community/ProofWidgets4 |

| 出典 | Lean | Mathlib | AF |
| --- | --- | --- | --- |
| AF checkout の lake-manifest.json / lean-toolchain | leanprover/lean4:v4.33.0-rc2 | `51e6992efd06126df61a496bebf8f49482a4e129` |  |
| lean/dependencies.json | leanprover/lean4:v4.33.0-rc2 | `51e6992efd06126df61a496bebf8f49482a4e129` | `3635e74826a4c1fcece7d1cd2b6fa75e43a00510` |
| checks/clean-verification-2026-11-10-local.json | Lean (version 4.33.0-rc2, arm64-apple-darwin24.6.0, commit d8b18978322de05a8f3dba51ef03cf5461676c17, Release) | `51e6992efd06126df61a496bebf8f49482a4e129` | `3635e74826a4c1fcece7d1cd2b6fa75e43a00510` |
| checks/clean-verification-2026-11-10-af.json |  | `51e6992efd06126df61a496bebf8f49482a4e129` | `3635e74826a4c1fcece7d1cd2b6fa75e43a00510` |

Mathlib の rev は全出典で一致、AF コミットは一致。

AF（`https://github.com/anthropics/formal-math.git` @ `3635e74826a4c1fcece7d1cd2b6fa75e43a00510`）の必須ソース閉包は **101 モジュール**（[checks/clean-verification-2026-11-10-af.json](../checks/clean-verification-2026-11-10-af.json) の `af_source_sha256`）。主定理の閉包内のローカルモジュールが直接 import する AF モジュールは 15 件:

- `Zeta23.Analytic.RectangleLogDeriv`
- `Zeta23.Assembly`
- `Zeta23.FromPNTPlus.MediumPNT`
- `Zeta23.FromPNTPlus.ResidueCalcOnRectangles`
- `Zeta23.FromPNTPlus.ZetaBounds`
- `Zeta23.GammaFacts.StirlingVert`
- `Zeta23.RvM.ZetaGrowth`
- `Zeta23.WeilEF.Effective`
- `Zeta23.XiPrime.Coeff.PrimeSums`
- `Zeta23.XiPrime.ExplicitFormula.ZeroFree`
- `Zeta23.XiPrime.Seam`
- `Zeta23.XiPrime.ZeroCount`
- `Zeta23.XiPrime.ZeroCount.ArgBound`
- `Zeta23.XiPrime.ZeroCount.Generic`
- `Zeta23.XiPrime.ZeroCount.Landau`

<details><summary>AF 必須モジュール一覧（101 件）</summary>

- `Zeta23.Analytic.RectangleLogDeriv`
- `Zeta23.Analytic.Stirling`
- `Zeta23.Assembly`
- `Zeta23.Assembly.Inputs`
- `Zeta23.Chebyshev`
- `Zeta23.Defs`
- `Zeta23.Defs.Counting`
- `Zeta23.ExplicitFormula`
- `Zeta23.ExplicitFormula.Bridge`
- `Zeta23.FromPNTPlus.Auxiliary`
- `Zeta23.FromPNTPlus.EulerMaclaurin`
- `Zeta23.FromPNTPlus.Fourier`
- `Zeta23.FromPNTPlus.Mathlib.Algebra.Notation.Support`
- `Zeta23.FromPNTPlus.Mathlib.Analysis.SpecialFunctions.Log.Basic`
- `Zeta23.FromPNTPlus.MediumPNT`
- `Zeta23.FromPNTPlus.MellinCalculus`
- `Zeta23.FromPNTPlus.Mertens`
- `Zeta23.FromPNTPlus.Rectangle`
- `Zeta23.FromPNTPlus.ResidueCalcOnRectangles`
- `Zeta23.FromPNTPlus.SmoothExistence`
- `Zeta23.FromPNTPlus.Sobolev`
- `Zeta23.FromPNTPlus.StrongPNTPrefix`
- `Zeta23.FromPNTPlus.Tactic.AdditiveCombination`
- `Zeta23.FromPNTPlus.ZetaBounds`
- `Zeta23.FromPNTPlus.ZetaConj`
- `Zeta23.GammaFacts`
- `Zeta23.GammaFacts.Complete`
- `Zeta23.GammaFacts.IntMu`
- `Zeta23.GammaFacts.Mu`
- `Zeta23.GammaFacts.Series`
- `Zeta23.GammaFacts.StirlingVert`
- `Zeta23.Hypotheses`
- `Zeta23.LinAlg`
- `Zeta23.LinAlg.HermitianPosPart`
- `Zeta23.LinAlg.Inertia`
- `Zeta23.LinAlg.PosIndex`
- `Zeta23.LinAlg.RankTrace`
- `Zeta23.LinAlg.Sylvester`
- `Zeta23.LinAlg.VonNeumann`
- `Zeta23.LinAlg.Weyl`
- `Zeta23.Poisson.PaperFT`
- `Zeta23.Prelude.InstancePriorities`
- `Zeta23.PrimeSideTemp`
- `Zeta23.RvM.Backlund`
- `Zeta23.RvM.BacklundDefs`
- `Zeta23.RvM.CountByIntegral`
- `Zeta23.RvM.Defs`
- `Zeta23.RvM.Fold`
- `Zeta23.RvM.GammaSide`
- `Zeta23.RvM.Halving`
- `Zeta23.RvM.LocalCount`
- `Zeta23.RvM.MainTerm`
- `Zeta23.RvM.NcountWindow`
- `Zeta23.RvM.ReZeroCount`
- `Zeta23.RvM.Statement`
- `Zeta23.RvM.ZetaGrowth`
- `Zeta23.Statement`
- `Zeta23.Statement.Seam`
- `Zeta23.Statement.SeamClosed`
- `Zeta23.Tail`
- `Zeta23.Tail.Basic`
- `Zeta23.Tail.Count`
- `Zeta23.Tail.Grid`
- `Zeta23.Tail.RankOne`
- `Zeta23.ThmE.GammaFactsChiProof`
- `Zeta23.ThmE.Hypotheses`
- `Zeta23.ThmE.IntMuChi`
- `Zeta23.TracesBoundsE`
- `Zeta23.WeilEF.Contour`
- `Zeta23.WeilEF.Effective`
- `Zeta23.WeilEF.FullLine`
- `Zeta23.WeilEF.FullLineAssembly`
- `Zeta23.WeilEF.GammaRBracket`
- `Zeta23.WeilEF.GoodHeights`
- `Zeta23.WeilEF.Horizontal`
- `Zeta23.WeilEF.Landau`
- `Zeta23.WeilEF.Main`
- `Zeta23.WeilEF.VerticalLine`
- `Zeta23.WeilEF.XiLogDeriv`
- `Zeta23.WeilEF.ZeroSumLimit`
- `Zeta23.WeilEF.ZeroSummability`
- `Zeta23.XiPrime.Coeff.Abel`
- `Zeta23.XiPrime.Coeff.Basic`
- `Zeta23.XiPrime.Coeff.NonSquarefree`
- `Zeta23.XiPrime.Coeff.PowerSums`
- `Zeta23.XiPrime.Coeff.PrimeSums`
- `Zeta23.XiPrime.Defs`
- `Zeta23.XiPrime.ExplicitFormula`
- `Zeta23.XiPrime.ExplicitFormula.ZeroFree`
- `Zeta23.XiPrime.Seam`
- `Zeta23.XiPrime.Statement`
- `Zeta23.XiPrime.ZeroCount`
- `Zeta23.XiPrime.ZeroCount.ArgBound`
- `Zeta23.XiPrime.ZeroCount.Basic`
- `Zeta23.XiPrime.ZeroCount.Contour`
- `Zeta23.XiPrime.ZeroCount.Generic`
- `Zeta23.XiPrime.ZeroCount.GenericRvM`
- `Zeta23.XiPrime.ZeroCount.Landau`
- `Zeta23.XiPrime.ZeroCount.Sides`
- `Zeta23.XiPrime.ZeroCount.Y`
- `Zeta23.ZetaReflect`

</details>

Mathlib（rev `51e6992efd06126df61a496bebf8f49482a4e129`）: 主定理の閉包内で直接 import される Mathlib モジュールは 37 件（`import Mathlib` を含む）。

## 4. 冗長な確認（Python 区間証明書）

[paper/verify.py](../paper/verify.py) の冒頭 docstring:

> Offline finite certificate for the fixed 88.45% witness. No optimization.
>
> Run: python3 verify.py [--manifest]
> Only dependency: mpmath==1.3.0. JSON goes to stdout; no files are written.
> The analytic counting and PRZZ transplantation are not verified by this code.

Python の区間証明書は Lean の `FixedCertificate` と独立の確認であり、主定理の論理には入りません。機械的な裏付け:

- `paper/verify.py` / `certificate.json` / `numerical_interval.py` を文字列として参照する Lean ソース: `BetaKernel`（コメント中の言及のみ。Lean の `import` は Mathlib / AF / ローカルモジュールに限られ、JSON や Python の出力を読み込む経路はありません）。
- `XiPrime8845.FixedCertificate.fixed_functional_gate` の出力: `'XiPrime8845.FixedCertificate.fixed_functional_gate' depends on axioms: [propext, Classical.choice, Quot.sound]`（数値公理・`native_decide`・外部データへの依存なし）。
- 二つの囲いは別物です: Python は `1.12818163807203565629105 < M < 1.12818163807203565629124`、Lean は上界 `1.128201` と目標下界 `1.1282054105`（README）。

## 5. 再現手順

### 5a. 数値証明書（Python、ネットワーク不要）

```sh
python3 -m pip install -r requirements.txt
python3 -B tools/verify_release.py
```

```sh
python3 -B paper/verify.py --manifest
```

期待される出力: `PASS` 3 行（ハッシュ数、有理数検査、証明書 JSON の一致）。CI の制限時間は 20 分。

### 5b. 現在の Lean 依存切替と公理監査

[docs/REPRODUCIBILITY.md](REPRODUCIBILITY.md) の手順:

```sh
git clone https://github.com/anthropics/formal-math.git af
git -C af switch --detach 3635e74826a4c1fcece7d1cd2b6fa75e43a00510
cd af
lake build
cd ..
```

```sh
python3 -B tools/verify_finite_family_rows.py --target WuProportion --all-local \
  --af /absolute/path/to/pinned-af --build /absolute/path/to/new-empty-scratch \
  --output build/review-verification.json --jobs 6
```

```sh
python3 -B tools/verify_lean.py --af /absolute/path/to/pinned-af \
  --output build/full-lean-verification.json --jobs 6
```

```sh
python3 -B tools/verify_clean_build.py \
  --af /absolute/path/to/pinned-af \
  --packages /absolute/path/to/pinned-af/.lake/packages \
  --output-prefix build/new-clean-verification --jobs 6
```

現在の記録: 全 778 ローカルソースを照合、主定理閉包 730 モジュール。この実行での新規コンパイル 778、再利用 0。`full_project_rebuilt: true`。
上流 AF 必須依存は 101 / 101 件を新規ビルド。旧 AF 成果物は不使用、Mathlib とパッケージは固定版キャッシュを再利用しています。
今回の実測コンパイル時間: AF 190.253 秒、本体 2939.546 秒、合計 3129.799 秒。本体並列枠 6。環境構築・文書/PDF 検査はこの時間に含みません。再実行時の保証値ではありません。

### 5c. 参考: 2026-11-07 の歴史的クリーン検証（現在の記録とは別）

当時実際に使われたコマンド（歴史的 AF/本体記録から）:

```sh
# AF 必須閉包の新規ビルド（隔離 worktree、Mathlib キャッシュは固定版を再利用）
env -u LEAN_PATH lake build Zeta23.Analytic.RectangleLogDeriv:olean Zeta23.Assembly:olean Zeta23.FromPNTPlus.MediumPNT:olean Zeta23.FromPNTPlus.ResidueCalcOnRectangles:olean Zeta23.FromPNTPlus.ZetaBounds:olean Zeta23.GammaFacts.StirlingVert:olean Zeta23.RvM.ZetaGrowth:olean Zeta23.WeilEF.Effective:olean Zeta23.XiPrime.Coeff.PrimeSums:olean Zeta23.XiPrime.ExplicitFormula.ZeroFree:olean Zeta23.XiPrime.Seam:olean Zeta23.XiPrime.ZeroCount:olean Zeta23.XiPrime.ZeroCount.ArgBound:olean Zeta23.XiPrime.ZeroCount.Contour:olean Zeta23.XiPrime.ZeroCount.Generic:olean Zeta23.XiPrime.ZeroCount.Landau:olean
# 本体 698 モジュールの新規コンパイルと公理監査
env -u LEAN_PATH python3 -B tools/verify_lean.py --af <isolated-pinned-af> --jobs 6 --output checks/clean-project-verification-2026-11-07.json
```

歴史的検証の結果（現在のソースを検証したという意味ではありません）:

- AF: `Build completed successfully (3788 jobs).`（新規ビルド 101 / 101 モジュール）
- 本体: 698 モジュールをすべて新規コンパイル、公理監査 3971 件、これは現在の依存切替記録ではありません。

現在の再現時には `#print axioms ratio_eventually_gt` が §1 の全文と一致（標準三公理のみ、`sorryAx` なし）。Weil/DI の明示的引数も §1 の定理文で確認。
