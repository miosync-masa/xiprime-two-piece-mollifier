import PRZZUniformGrid
import PRZZArithmeticWindowCutoff

/-! Variable Fourier cutoffs in the original moment collector. The strict
spatial mask is unchanged. Every cell uses its own fixed arithmetic-window
cutoff; both the negative modes and the exact remaining tail are retained.
The Weil/DI cap supplier is uniform before all scales and all cutoffs.
No optimal bound for the remaining window budget is asserted. -/
noncomputable section
open scoped BigOperators ContDiff Topology
open Complex Finset MeasureTheory Set Filter
namespace XiPrime8845.PRZZWindowMoment
open PRZZMellinSeparation PRZZCentralArithmeticJoin PRZZCentralMainAssembly
open PRZZActualAggregate PRZZLiteralFourierLimit PRZZCentralGridWeilDI
set_option maxHeartbeats 10000000
attribute [local instance] Classical.propDecidable

def collect (P : ℝ → ℂ) (K L N : ℕ) (T eps : ℝ)
    (cut : (ℕ × ℕ) → ℕ → ℕ → ℕ)
    (f : ℕ → ℕ → ℝ → ℝ → (ℝ → ℂ) → (ℝ → ℂ) → ℂ) : ℂ :=
  ∑ p ∈ range K ×ˢ range K,
    ∑ s ∈ (range (L+2)).filter (fun s => (2:ℝ)^s < T^(4:ℝ)), ∑ d ∈ Icc 1 N,
      f d (cut p s d) (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) ((2:ℝ)^p.1) eps)
        ((2:ℝ)^s) (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.1))
        (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^p.2))

def window (T eH : ℝ) (p : ℕ × ℕ) (s d : ℕ) : ℕ :=
  PRZZArithmeticWindowCutoff.cutoff d T ((2:ℝ)^s) ((2:ℝ)^p.2) eH

def positive (P F Phi : ℝ → ℂ) (K L N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (cut : (ℕ × ℕ) → ℕ → ℕ → ℕ) (alpha beta : ℂ) : ℂ :=
  collect P K L N T eps cut (fun d J D M G H =>
    positiveCell N d J D T M a (PRZZWRowLimit.profile F) G H Phi alpha beta)

def negative (P F Phi : ℝ → ℂ) (K L N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (cut : (ℕ × ℕ) → ℕ → ℕ → ℕ) (alpha beta : ℂ) : ℂ :=
  collect P K L N T eps cut (fun d J D M G H =>
    negativeCell N d J D T M a (PRZZWRowLimit.profile F) G H Phi alpha beta)

def tail (P F Phi : ℝ → ℂ) (K L N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (cut : (ℕ × ℕ) → ℕ → ℕ → ℕ) (alpha beta : ℂ) : ℂ :=
  collect P K L N T eps cut (fun d J D M G H =>
    cellTail N d J D T M a (PRZZWRowLimit.profile F) G H Phi alpha beta)

/-- Cutoff invariance is an exact finite-cell identity, before norms and
without an exchange of non-integrable time or spatial integrals. -/
theorem nonzero_tail (P F Phi : ℝ → ℂ) (K L N J : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (cut : (ℕ × ℕ) → ℕ → ℕ → ℕ) (alpha beta : ℂ) :
    positive P F Phi K L N a T eps cut alpha beta+
      negative P F Phi K L N a T eps cut alpha beta+
      tail P F Phi K L N a T eps cut alpha beta =
    positivePart P F Phi K L J N a T eps alpha beta+
      negativePart P F Phi K L J N a T eps alpha beta+
      tailPart P F Phi K L J N a T eps alpha beta := by
  unfold positive negative tail collect positivePart negativePart tailPart PRZZCentralMainAssembly.collect
  simp only [← sum_add_distrib]
  apply sum_congr rfl; intro p hp
  apply sum_congr rfl; intro s hs
  apply sum_congr rfl; intro d hd
  simp only [cellTail,prefix_split]
  ring

def residual (P F Phi : ℝ → ℂ) (K N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (cut : (ℕ × ℕ) → ℕ → ℕ → ℕ) (alpha beta : ℂ) : ℂ :=
  zeroMismatch P F Phi K N a T eps alpha beta+
    branchPair (fun Phi alpha beta => positive P F Phi K
      (PRZZLiteralExhaustion.spatialLength T) N a T eps cut alpha beta) Phi T alpha beta+
    branchPair (fun Phi alpha beta => negative P F Phi K
      (PRZZLiteralExhaustion.spatialLength T) N a T eps cut alpha beta) Phi T alpha beta+
    branchPair (fun Phi alpha beta => tail P F Phi K
      (PRZZLiteralExhaustion.spatialLength T) N a T eps cut alpha beta) Phi T alpha beta

theorem residual_eq (P F Phi : ℝ → ℂ) (K N J : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (cut : (ℕ × ℕ) → ℕ → ℕ → ℕ) (alpha beta : ℂ) :
    residual P F Phi K N a T eps cut alpha beta =
      arithmeticResidual P F Phi K J N a T eps alpha beta := by
  have h := nonzero_tail P F Phi K (PRZZLiteralExhaustion.spatialLength T) N J a T eps cut alpha beta
  have hd := nonzero_tail P F (PRZZKeptLiteral.dualProfile Phi T alpha beta)
    K (PRZZLiteralExhaustion.spatialLength T) N J a T eps cut (-beta) (-alpha)
  unfold residual arithmeticResidual branchPair
  linear_combination h+hd

theorem model_main (P F Phi : ℝ → ℂ) (K N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (cut : (ℕ × ℕ) → ℕ → ℕ → ℕ) (alpha beta : ℂ) :
    fullModel P F Phi K N a T eps alpha beta =
      PRZZCoupledAFE.diagonalMain N a alpha beta T (scaledCutoff Phi T)+
        residual P F Phi K N a T eps cut alpha beta+
        ∫ t in Icc T (2*T), scaledCutoff Phi T t*PRZZZeroCross.gammaDefect N a alpha beta t := by
  rw [residual_eq P F Phi K N 0]
  exact model_main_arithmetic P F Phi K 0 N a T eps alpha beta

def budget (caps : (List ℕ × List ℕ) → Caps) (w : (List ℕ × List ℕ) → ℝ)
    (C : ℝ) (js : List ℕ) (K Kgrid L N : ℕ) (eps eta b T eCut : ℝ)
    (cut : (ℕ × ℕ) → ℕ → ℕ → ℕ) (Phi : ℝ → ℂ) (alpha beta : ℂ) : ℝ :=
  ∑ p ∈ range Kgrid ×ˢ range Kgrid,
    ∑ s ∈ (range (L+2)).filter (fun s => (2:ℝ)^s < T^(4:ℝ)), ∑ d ∈ Icc 1 N,
      positiveBudget C w caps js K N d (cut p s d) eps eta b
        (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) ((2:ℝ)^p.1) eCut) T ((2:ℝ)^s)
        Phi alpha beta

theorem positive_weil_di
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js : List ℕ) (eps eta b S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hb : 0 < b) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (P F : ℝ → ℂ) (hP : ContDiff ℝ ∞ P) (hF : ContDiff ℝ ∞ F)
    (hPl : ∀ x ≤ (1/2:ℝ), P x = 1) (hPr : ∀ x, 1 ≤ x → P x = 0)
    (hFl : ∀ x ≤ (1/2:ℝ), F x = 1) (hFr : ∀ x, 1 ≤ x → F x = 0) :
    ∃ caps : (List ℕ × List ℕ) → Caps, ∃ w : (List ℕ × List ℕ) → ℝ, ∃ C : ℝ,
      0 < C ∧ (∀ q, 0 < w q) ∧
      ∀ Kgrid L N : ℕ, ∀ T eCut : ℝ, ∀ cut : (ℕ × ℕ) → ℕ → ℕ → ℕ, ∀ alpha beta : ℂ,
      1 ≤ N → (N:ℝ)+1 ≤ T → 1 ≤ Real.log T →
      |beta.re| ≤ S/Real.log T → 1+‖beta‖ ≤ Z → |alpha.re| ≤ S/Real.log T →
      alpha+beta ≠ 0 → ∀ Phi : ℝ → ℂ,
      ContDiff ℝ ∞ Phi → Function.support Phi ⊆ Icc (1:ℝ) 2 →
      ‖positive P F Phi Kgrid L N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
          T eCut cut alpha beta‖ ≤
        budget caps w C js K Kgrid L N eps eta b T eCut cut Phi alpha beta := by
  have hp := PRZZWRowLimit.profile_regular P hP hPl hPr
  have hf := PRZZWRowLimit.profile_regular F hF hFl hFr
  obtain ⟨caps,w,C,hC,hw,hbound⟩ := PRZZUniformOuter.positive_cell_uniform hWeil hDI K hK js eps eta b S Z
    heps heta hb hS hZ (PRZZWRowLimit.profile P) (PRZZWRowLimit.profile P) (PRZZWRowLimit.profile F)
    hp.1 hp.2.1 hp.1.continuous hp.2.1 hf.1.continuous hf.2.1 hf.2.2
  refine ⟨caps,w,C,hC,hw,?_⟩
  intro Kgrid L N T eCut cut alpha beta hN hNT hlog hbeta hz halpha hs Phi hPhi hsPhi
  have hT : 1 < T := by
    have : (1:ℝ) ≤ N := by exact_mod_cast hN
    linarith
  unfold positive collect budget
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro p hp'
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro s hs'
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro d hd
  have hd0 : 0 < d := (mem_Icc.mp hd).1
  have hdT : (d:ℝ) ≤ T := (by exact_mod_cast (mem_Icc.mp hd).2 : (d:ℝ) ≤ N).trans (by linarith)
  exact hbound ((2:ℝ)^s) ((2:ℝ)^p.2) N d (cut p s d) T ((2:ℝ)^p.1)
    (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) ((2:ℝ)^p.1) eCut) alpha beta
    (by positivity) (by omega) hd0 hT hNT hdT hlog
    (frequency_positive d (cut p s d) _ hd0 (by unfold PRZZSourceCutoffs.deltaCutoff; positivity))
    hbeta hz halpha hs Phi hPhi hsPhi

theorem negative_weil_di
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js : List ℕ) (eps eta b S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hb : 0 < b) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (P F : ℝ → ℂ) (hP : ContDiff ℝ ∞ P) (hF : ContDiff ℝ ∞ F)
    (hPl : ∀ x ≤ (1/2:ℝ), P x = 1) (hPr : ∀ x, 1 ≤ x → P x = 0)
    (hFl : ∀ x ≤ (1/2:ℝ), F x = 1) (hFr : ∀ x, 1 ≤ x → F x = 0) :
    ∃ caps : (List ℕ × List ℕ) → Caps, ∃ w : (List ℕ × List ℕ) → ℝ, ∃ C : ℝ,
      0 < C ∧ (∀ q, 0 < w q) ∧
      ∀ Kgrid L N : ℕ, ∀ T eCut : ℝ, ∀ cut : (ℕ × ℕ) → ℕ → ℕ → ℕ, ∀ alpha beta : ℂ,
      1 ≤ N → (N:ℝ)+1 ≤ T → 1 ≤ Real.log T →
      |beta.re| ≤ S/Real.log T → 1+‖beta‖ ≤ Z → |alpha.re| ≤ S/Real.log T →
      alpha+beta ≠ 0 → ∀ Phi : ℝ → ℂ,
      ContDiff ℝ ∞ Phi → Function.support Phi ⊆ Icc (1:ℝ) 2 →
      ‖negative P F Phi Kgrid L N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
          T eCut cut alpha beta‖ ≤
        budget caps w C js K Kgrid L N eps eta b T eCut cut Phi alpha beta := by
  have hp := PRZZWRowLimit.profile_regular P hP hPl hPr
  have hf := PRZZWRowLimit.profile_regular F hF hFl hFr
  obtain ⟨caps,w,C,hC,hw,hbound⟩ := PRZZUniformOuter.negative_cell_uniform hWeil hDI K hK js eps eta b S Z
    heps heta hb hS hZ (PRZZWRowLimit.profile P) (PRZZWRowLimit.profile P) (PRZZWRowLimit.profile F)
    hp.1 hp.2.1 hp.1.continuous hp.2.1 hf.1.continuous hf.2.1 hf.2.2
  refine ⟨caps,w,C,hC,hw,?_⟩
  intro Kgrid L N T eCut cut alpha beta hN hNT hlog hbeta hz halpha hs Phi hPhi hsPhi
  have hT : 1 < T := by
    have : (1:ℝ) ≤ N := by exact_mod_cast hN
    linarith
  unfold negative collect budget
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro p hp'
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro s hs'
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro d hd
  have hd0 : 0 < d := (mem_Icc.mp hd).1
  have hdT : (d:ℝ) ≤ T := (by exact_mod_cast (mem_Icc.mp hd).2 : (d:ℝ) ≤ N).trans (by linarith)
  exact hbound ((2:ℝ)^s) ((2:ℝ)^p.2) N d (cut p s d) T ((2:ℝ)^p.1)
    (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) ((2:ℝ)^p.1) eCut) alpha beta
    (by positivity) (by omega) hd0 hT hNT hdT hlog
    (frequency_positive d (cut p s d) _ hd0 (by unfold PRZZSourceCutoffs.deltaCutoff; positivity))
    hbeta hz halpha hs Phi hPhi hsPhi

/-- Return the variable-cutoff arithmetic residual to the ORIGINAL moment.
The constants of the already proved AFE reduction are unchanged. -/
theorem moment_main_bound (P : ℝ → ℝ) (Phi : ℝ → ℂ)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ))) (hm : Antitone P)
    (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (js : List ℕ) (S r eps eH eta delta : ℝ)
    (hS : 0 ≤ S) (hr : 0 < r) (heps : 0 < eps) (heps1 : eps < 1)
    (he : eps < eH) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hmargin : 6*eps+2*eta < delta) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ᶠ T : ℝ in atTop, ∀ (N : ℕ) (A B : ℂ),
      1 ≤ N → (N:ℝ) ≤ T^(4/7:ℝ) → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ∀ cut : (ℕ × ℕ) → ℕ → ℕ → ℕ,
      let a := fun n => (PRZZGCoefficient.coefficient js n:ℂ)
      let alpha := A/(Real.log T:ℂ)
      let beta := B/(Real.log T:ℂ)
      ‖PRZZExhaustiveAFEError.moment N a alpha beta T (scaledCutoff Phi T)-
          PRZZCoupledAFE.diagonalMain N a alpha beta T (scaledCutoff Phi T)‖ ≤
        C*T^delta*PRZZOptimalPowers.target N T+
          ‖residual (fun x => (P x:ℂ)) (fun x => (P x:ℂ)) Phi
            (Nat.log 2 N+2) N a T eps cut alpha beta‖+
          D*(1+16*(Real.log T)^2/r^2)*(N:ℝ)^(1/4:ℝ)*T^(-(9/8:ℝ))*
            (1+Real.log N)^(2*PRZZGCoefficient.degree js+2)*
              (∫ t in Icc T (2*T), ‖scaledCutoff Phi T t‖) := by
  obtain ⟨C,D,hC,hD,h⟩ := PRZZCentralMainAssembly.moment_main_bound P Phi hP hm hlo hhi hl hright
    hPhi hcPhi hsPhi js S r eps eH eta delta hS hr heps heps1 he heta heta1 hmargin
  refine ⟨C,D,hC,hD,?_⟩
  filter_upwards [h] with T h
  intro N A B hN hscale hA hB hsep cut
  dsimp only
  rw [residual_eq _ _ _ _ _ 0]
  exact h 0 N A B hN hscale hA hB hsep

theorem residual_weil_di
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js : List ℕ) (eps eta b S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hb : 0 < b) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (P F : ℝ → ℂ) (hP : ContDiff ℝ ∞ P) (hF : ContDiff ℝ ∞ F)
    (hPl : ∀ x ≤ (1/2:ℝ), P x = 1) (hPr : ∀ x, 1 ≤ x → P x = 0)
    (hFl : ∀ x ≤ (1/2:ℝ), F x = 1) (hFr : ∀ x, 1 ≤ x → F x = 0) :
    ∃ capsP capsN : (List ℕ × List ℕ) → Caps,
      ∃ wP wN : (List ℕ × List ℕ) → ℝ, ∃ CP CN : ℝ,
      0 < CP ∧ 0 < CN ∧ (∀ q, 0 < wP q) ∧ (∀ q, 0 < wN q) ∧
      ∀ Kgrid N : ℕ, ∀ T eCut : ℝ, ∀ cut : (ℕ × ℕ) → ℕ → ℕ → ℕ, ∀ alpha beta : ℂ,
      1 ≤ N → (N:ℝ)+1 ≤ T → 1 ≤ Real.log T →
      |beta.re| ≤ S/Real.log T → 1+‖beta‖ ≤ Z → |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z →
      ‖alpha‖ ≤ 1/4 → ‖beta‖ ≤ 1/4 → alpha+beta ≠ 0 → ∀ Phi : ℝ → ℂ,
      ContDiff ℝ ∞ Phi → Function.support Phi ⊆ Icc (1:ℝ) 2 →
      let a := fun n => (PRZZGCoefficient.coefficient js n:ℂ)
      let L := PRZZLiteralExhaustion.spatialLength T
      ‖residual P F Phi Kgrid N a T eCut cut alpha beta‖ ≤
        ‖zeroMismatch P F Phi Kgrid N a T eCut alpha beta‖+
        (budget capsP wP CP js K Kgrid L N eps eta b T eCut cut Phi alpha beta+
          budget capsP wP CP js K Kgrid L N eps eta b T eCut cut
            (PRZZKeptLiteral.dualProfile Phi T alpha beta) (-beta) (-alpha))+
        (budget capsN wN CN js K Kgrid L N eps eta b T eCut cut Phi alpha beta+
          budget capsN wN CN js K Kgrid L N eps eta b T eCut cut
            (PRZZKeptLiteral.dualProfile Phi T alpha beta) (-beta) (-alpha))+
        ‖branchPair (fun Phi alpha beta => tail P F Phi Kgrid L N a T eCut cut alpha beta)
          Phi T alpha beta‖ := by
  obtain ⟨capsP,wP,CP,hCP,hwP,hp⟩ := positive_weil_di hWeil hDI K hK js eps eta b S Z
    heps heta hb hS hZ P F hP hF hPl hPr hFl hFr
  obtain ⟨capsN,wN,CN,hCN,hwN,hn⟩ := negative_weil_di hWeil hDI K hK js eps eta b S Z
    heps heta hb hS hZ P F hP hF hPl hPr hFl hFr
  refine ⟨capsP,capsN,wP,wN,CP,CN,hCP,hCN,hwP,hwN,?_⟩
  intro Kgrid N T eCut cut alpha beta hN hNT hlog hbeta hzb halpha hza ha hb' hs Phi hPhi hsPhi
  dsimp only
  have hd : ContDiff ℝ ∞ (PRZZKeptLiteral.dualProfile Phi T alpha beta) :=
    hPhi.mul ((PRZZDualSmooth.multiplier_contDiff alpha beta ha hb').comp
      (contDiff_const.mul contDiff_id))
  have hsd := (PRZZKeptLiteral.dual_profile_regular Phi hPhi.continuous hsPhi T alpha beta ha hb').2
  have hsdiff : -beta+-alpha ≠ 0 := by
    rw [show -beta+-alpha = -(alpha+beta) by ring]
    exact neg_ne_zero.mpr hs
  have hp1 := hp Kgrid (PRZZLiteralExhaustion.spatialLength T) N T eCut cut alpha beta hN hNT hlog hbeta hzb halpha hs Phi hPhi hsPhi
  have hp2 := hp Kgrid (PRZZLiteralExhaustion.spatialLength T) N T eCut cut (-beta) (-alpha) hN hNT hlog
    (by simpa using halpha) (by simpa using hza) (by simpa using hbeta) hsdiff _ hd hsd
  have hn1 := hn Kgrid (PRZZLiteralExhaustion.spatialLength T) N T eCut cut alpha beta hN hNT hlog hbeta hzb halpha hs Phi hPhi hsPhi
  have hn2 := hn Kgrid (PRZZLiteralExhaustion.spatialLength T) N T eCut cut (-beta) (-alpha) hN hNT hlog
    (by simpa using halpha) (by simpa using hza) (by simpa using hbeta) hsdiff _ hd hsd
  have hpos := (norm_add_le _ _).trans (add_le_add hp1 hp2)
  have hneg := (norm_add_le _ _).trans (add_le_add hn1 hn2)
  unfold residual
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add le_rfl hpos)) hneg)) le_rfl)

theorem moment_weil_di
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (epsA etaA b : ℝ)
    (hepsA : 0 < epsA) (hetaA : 0 < etaA) (hb : 0 < b)
    (P : ℝ → ℝ) (Phi : ℝ → ℂ)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ))) (hm : Antitone P)
    (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (js : List ℕ) (S r eps eH eta delta : ℝ)
    (hS : 0 ≤ S) (hr : 0 < r) (heps : 0 < eps) (heps1 : eps < 1)
    (he : eps < eH) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hmargin : 6*eps+2*eta < delta) :
    ∃ capsP capsN : (List ℕ × List ℕ) → Caps,
      ∃ wP wN : (List ℕ × List ℕ) → ℝ, ∃ CP CN C D : ℝ,
      0 < CP ∧ 0 < CN ∧ (∀ q, 0 < wP q) ∧ (∀ q, 0 < wN q) ∧ 0 < C ∧ 0 < D ∧ ∀ᶠ T : ℝ in atTop, ∀ (N : ℕ) (A B : ℂ),
      1 ≤ N → (N:ℝ) ≤ T^(4/7:ℝ) → (N:ℝ)+1 ≤ T → 1 ≤ Real.log T → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ∀ cut : (ℕ × ℕ) → ℕ → ℕ → ℕ,
      let a := fun n => (PRZZGCoefficient.coefficient js n:ℂ)
      let alpha := A/(Real.log T:ℂ)
      let beta := B/(Real.log T:ℂ)
      let F : ℝ → ℂ := fun x => (P x:ℂ)
      let Kgrid := Nat.log 2 N+2
      let L := PRZZLiteralExhaustion.spatialLength T
      ‖PRZZExhaustiveAFEError.moment N a alpha beta T (scaledCutoff Phi T)-
          PRZZCoupledAFE.diagonalMain N a alpha beta T (scaledCutoff Phi T)‖ ≤
        C*T^delta*PRZZOptimalPowers.target N T+
          (‖zeroMismatch F F Phi Kgrid N a T eps alpha beta‖+
            (budget capsP wP CP js K Kgrid L N epsA etaA b T eps cut Phi alpha beta+
              budget capsP wP CP js K Kgrid L N epsA etaA b T eps cut
                (PRZZKeptLiteral.dualProfile Phi T alpha beta) (-beta) (-alpha))+
            (budget capsN wN CN js K Kgrid L N epsA etaA b T eps cut Phi alpha beta+
              budget capsN wN CN js K Kgrid L N epsA etaA b T eps cut
                (PRZZKeptLiteral.dualProfile Phi T alpha beta) (-beta) (-alpha))+
            ‖branchPair (fun Phi alpha beta => tail F F Phi Kgrid L N a T eps cut alpha beta)
              Phi T alpha beta‖)+
          D*(1+16*(Real.log T)^2/r^2)*(N:ℝ)^(1/4:ℝ)*T^(-(9/8:ℝ))*
            (1+Real.log N)^(2*PRZZGCoefficient.degree js+2)*
              (∫ t in Icc T (2*T), ‖scaledCutoff Phi T t‖) := by
  let F : ℝ → ℂ := fun x => (P x:ℂ)
  have hFl : ∀ x ≤ (1/2:ℝ), F x = 1 := by intro x hx; simp [F,hl x hx]
  have hFr : ∀ x, 1 ≤ x → F x = 0 := by intro x hx; simp [F,hright x hx]
  obtain ⟨capsP,capsN,wP,wN,CP,CN,hCP,hCN,hwP,hwN,hres⟩ :=
    residual_weil_di hWeil hDI K hK js epsA etaA b S (1+S)
      hepsA hetaA hb hS (by linarith) F F hP hP hFl hFr hFl hFr
  obtain ⟨C,D,hC,hD,hmain⟩ := moment_main_bound P Phi hP hm hlo hhi hl hright
    hPhi hcPhi hsPhi js S r eps eH eta delta hS hr heps heps1 he heta heta1 hmargin
  refine ⟨capsP,capsN,wP,wN,CP,CN,C,D,hCP,hCN,hwP,hwN,hC,hD,?_⟩
  filter_upwards [hmain,PRZZScaledReplacement.shifts_eventually S (1/4) (by norm_num)] with T hmain hsmall
  intro N A B hN hscale hNT hlog hA hB hsep cut
  dsimp only
  have hab : A+B ≠ 0 := norm_pos_iff.mp (hr.trans_le hsep)
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]
    exact div_ne_zero hab (by exact_mod_cast (show Real.log T ≠ 0 by linarith))
  have hsc := scaled_shift_conditions S T A B hS hlog hA hB
  have hsc' := scaled_shift_conditions S T B A hS hlog hB hA
  have hrb := hres (Nat.log 2 N+2) N T eps cut _ _ hN hNT hlog
    hsc.1 hsc.2.1 hsc.2.2 hsc'.2.1 (hsmall.2 A hA) (hsmall.2 B hB) hs Phi hPhi hsPhi
  exact (hmain N A B hN hscale hA hB hsep cut).trans
    (add_le_add (add_le_add le_rfl hrb) le_rfl)

#print axioms moment_weil_di
#print axioms residual_weil_di
#print axioms negative_weil_di
#print axioms moment_main_bound
#print axioms nonzero_tail
#print axioms residual_eq
#print axioms model_main
#print axioms positive_weil_di
end XiPrime8845.PRZZWindowMoment
