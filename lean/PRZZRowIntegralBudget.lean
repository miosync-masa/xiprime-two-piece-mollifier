import PRZZLiteralRows
import PRZZActualAggregate
import PRZZNonemptyRowBudget

/-! Norm transfer for the original row integrals. The local row window is
kept inside the dyadic sum; the global cutoff is not discarded from the
identity. The arithmetic envelope is supplied separately by Weil and DI. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset MeasureTheory Set Complex
namespace XiPrime8845.PRZZRowIntegralBudget
open PRZZAStar PRZZOriginalRowWindow PRZZRowMellinBranches PRZZMellinSeparation
set_option maxHeartbeats 4000000

theorem row_integral_bound (N d j l : ℕ) (D H T M B : ℝ) (a : ℕ → ℂ)
    (F1 F2 FM W Phi : ℝ → ℂ) (alpha beta : ℂ)
    (hN : 0 < N) (hd : 0 < d) (hT : 0 < T) (hM : 0 < M)
    (hFM : Continuous FM) (hW : ContinuousOn W (Ioi 0))
    (hPhi : ContDiff ℝ ∞ Phi) (hsM : Function.support FM ⊆ Icc (M/2) (3*M))
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2) (hB : 0 ≤ B)
    (hb : ∀ p ∈ PRZZDyadicWindow.box T M ((2:ℝ)^j) ((2:ℝ)^l), ∀ t : ℝ,
      ‖signedRow N d j l D H a F1 F2 FM alpha beta p.1 p.2 t‖ ≤ B*(1+|t|)) :
    ‖∫ x in Ioi (0:ℝ), ∫ y, rowKernel N d j l D H T a F1 F2 FM W Phi alpha beta (x,y)‖ ≤
      (1/(2*Real.pi))*(∫ p, ‖PRZZDyadicEnvelope.common d T M ((2:ℝ)^j) ((2:ℝ)^l)
        W (alpha+beta) p‖)*B*(∫ t : ℝ, (1+|t|)*‖mellin Phi (t*I)‖) := by
  let s := PRZZDyadicWindow.box T M ((2:ℝ)^j) ((2:ℝ)^l)
  let c := PRZZDyadicEnvelope.common d T M ((2:ℝ)^j) ((2:ℝ)^l) W (alpha+beta)
  let f := fun p t => s.indicator (fun p =>
    ∑ z ∈ rowIndices N d j l D H,
      PRZZActualMellin.localized N d T (M/2) (3*M) a F1 F2 FM W Phi alpha beta z p t) p
  have hc : Integrable c := PRZZDyadicEnvelope.common_integrable d T M _ _ W (alpha+beta)
    hd hT hM (by positivity) (by positivity) hW
  have hm : Integrable (fun t : ℝ => (1+|t|)*‖mellin Phi (t*I)‖) := by
    simpa [add_mul,Pi.add_def] using
      (PRZZMellinMoment.polynomial_integrable Phi 1 2 (by norm_num) hsP hPhi 0).add
        (PRZZMellinMoment.polynomial_integrable Phi 1 2 (by norm_num) hsP hPhi 1)
  have hpoint (p : ℝ × ℝ) (t : ℝ) :
      ‖f p t‖ ≤ ‖c p‖*B*((1+|t|)*‖mellin Phi (t*I)‖) := by
    by_cases hp : p ∈ s
    · dsimp only [f]
      rw [Set.indicator_of_mem hp,row_localized]
      by_cases hw : p ∈ PRZZAStarWindow.window N T (M/2) (3*M)
      · rw [Set.indicator_of_mem hw]
        have hx : 0 < p.1 := (show 0 < M/(4*(2:ℝ)^l) by positivity).trans_le hp.1.1
        have hy : 0 < p.2 := (show 0 < T/(12*M*(2:ℝ)^j) by positivity).trans_le hp.2.1
        simp only [norm_mul,twist_norm _ _ (div_pos (mul_pos hx hy) hT),mul_one]
        have hh := mul_le_mul_of_nonneg_left (hb p hp t)
          (mul_nonneg (norm_nonneg (W (2*Real.pi*p.1/p.2)/((d:ℂ)*(p.1:ℂ)^(alpha+beta))))
            (norm_nonneg (mellin Phi (t*I))))
        have hp' : p ∈ PRZZDyadicWindow.box T M ((2:ℝ)^j) ((2:ℝ)^l) := hp
        dsimp only [c,PRZZDyadicEnvelope.common]
        rw [Set.indicator_of_mem hp']
        exact hh.trans_eq (by ring)
      · simp only [Set.indicator_of_notMem hw,zero_mul,norm_zero]
        positivity
    · simp only [f,Set.indicator_of_notMem hp,norm_zero]
      positivity
  have hinner (t : ℝ) : ‖∫ p, f p t‖ ≤
      (∫ p, ‖c p‖)*B*((1+|t|)*‖mellin Phi (t*I)‖) := by
    have hh := norm_integral_le_of_norm_le
      ((hc.norm.mul_const B).mul_const ((1+|t|)*‖mellin Phi (t*I)‖))
      (Filter.Eventually.of_forall (fun p => hpoint p t))
    simpa only [integral_mul_const] using hh
  have hout := norm_integral_le_of_norm_le
    (hm.const_mul ((∫ p, ‖c p‖)*B)) (Filter.Eventually.of_forall hinner)
  rw [row_iterated_eq N d j l D H T M a F1 F2 FM W Phi alpha beta hT hM hFM hW hPhi.continuous hsM hsP,
    row_mellin_window N d j l D H T M a F1 F2 FM W Phi alpha beta hN hT hM hFM hW hPhi hsM hsP]
  change ‖(1/(2*Real.pi):ℂ)*(∫ t, ∫ p, f p t)‖ ≤ _
  rw [norm_mul,show ‖(1/(2*Real.pi):ℂ)‖ = 1/(2*Real.pi) by
    simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]]
  exact (mul_le_mul_of_nonneg_left hout (by positivity)).trans_eq (by rw [integral_const_mul]; ring)

#print axioms row_integral_bound

open PRZZActualAggregate PRZZCoefficientSeparation PRZZAllSignedSources
open PRZZSupportedSplit PRZZGCoefficient

def rowBudget (C : ℝ) (w : (List ℕ × List ℕ) → ℝ)
    (caps : (List ℕ × List ℕ) → Caps) (js : List ℕ)
    (eps eta beta T A : ℝ) (N d K j l : ℕ) : ℝ :=
  C*(d:ℝ)^eta*(N:ℝ)^beta*((allocations js).map (fun q =>
    w q*T^eta*row (caps q) eps eta T A N K j l q.2)).sum

theorem rowBudget_nonneg (C : ℝ) (w : (List ℕ × List ℕ) → ℝ)
    (caps : (List ℕ × List ℕ) → Caps) (js : List ℕ)
    (eps eta beta T A : ℝ) (N d K j l : ℕ)
    (hC : 0 ≤ C) (hw : ∀ q, 0 ≤ w q) (hT : 0 ≤ T) (hA : 0 ≤ A) :
    0 ≤ rowBudget C w caps js eps eta beta T A N d K j l := by
  unfold rowBudget
  apply mul_nonneg (by positivity)
  apply List.sum_nonneg
  intro x hx
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
  exact mul_nonneg (mul_nonneg (hw q) (Real.rpow_nonneg hT _))
    (row_nonneg _ _ _ _ _ _ _ _ _ _ hT hA)

private theorem list_scale {ι : Type*} (qs : List ι) (f : ι → ℝ) (r : ℝ) :
    (qs.map (fun q => f q*r)).sum = (qs.map f).sum*r := by
  induction qs with
  | nil => simp
  | cons q qs ih => simp only [List.map_cons,List.sum_cons,ih]; ring

/-- The actual supported h sum and every allocation, before summing j,l.
Only Weil and DI are analytic estimate premises. -/
theorem signedRow_bound
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js : List ℕ) (eps eta beta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hbeta : 0 < beta) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (F0 F2 FM : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM) :
    ∃ caps : (List ℕ × List ℕ) → Caps, ∃ w : (List ℕ × List ℕ) → ℝ,
      ∃ C : ℝ, 0 < C ∧ (∀ q, 0 < w q) ∧
      ∀ N d j l : ℕ, ∀ T Q D H x y t : ℝ, ∀ alpha betaShift : ℂ,
      0 < N → 0 < d → 1 < T → (N:ℝ)+1 ≤ T → (d:ℝ) ≤ T → 1 ≤ Real.log T →
      1 ≤ (PRZZActualSignedBranches.frequencyBound d D H:ℝ) →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z → |betaShift.re| ≤ S/Real.log T →
      ‖signedRow N d j l D H (fun n => (coefficient js n:ℂ))
        (scaledCutoff F0 Q) F2 FM alpha betaShift x y t‖ ≤
      rowBudget C w caps js eps eta beta T
        (PRZZActualSignedBranches.frequencyBound d D H) N d K j l*(1+|t|) := by
  choose caps w hw hblocks using fun q : List ℕ × List ℕ =>
    actual_blocks hWeil hDI K hK q.2 js eps eta S Z heps heta hS hZ F0 F2 FM hf hc hF hcF hM hcM
  obtain ⟨C,hC,halloc⟩ := PRZZAllCellsBound.allocation_bound js eta beta heta hbeta
  refine ⟨caps,w,C,hC,hw,?_⟩
  intro N d j l T Q D H x y t alpha betaShift hN hd hT hNT hdT hlog hA ha hz hb
  let A : ℝ := PRZZActualSignedBranches.frequencyBound d D H
  rw [signedRow_blocks N d j l K hd (by omega)]
  have hnq (q : List ℕ × List ℕ) :
      0 ≤ w q*T^eta*row (caps q) eps eta T A N K j l q.2 :=
    mul_nonneg (mul_nonneg (hw q).le (Real.rpow_nonneg (by linarith) eta))
      (row_nonneg _ _ _ _ _ _ _ _ _ _ (by linarith) (by dsimp [A]; positivity))
  have hh := halloc d N hd hN
    (fun q => (w q*T^eta*row (caps q) eps eta T A N K j l q.2)*(1+|t|))
    (fun q h => blocks N d h j l K q.2 js D H x y t (scaledCutoff F0 Q) F2 FM alpha betaShift)
    (fun q _ => mul_nonneg (hnq q) (by positivity)) (by
      intro q hq h hh
      have hs := mem_hSupport N d h hh
      have hhn : h ≤ N := by nlinarith [hs.2.1]
      exact hblocks q N d h j l T Q D H x y t alpha betaShift hN hd hs.1 hT hNT hdT
        ((by exact_mod_cast hhn : (h:ℝ) ≤ N).trans (by linarith)) hlog hA ha hz hb)
  rw [list_scale] at hh
  exact hh.trans_eq (by dsimp [rowBudget,A]; ring)

/-- Bulk substitution into the original literal A*. Each dyadic row keeps
its own outer mass, paired with its own three-case arithmetic budget. -/
theorem literal_row_budgets
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js : List ℕ) (eps eta beta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hbeta : 0 < beta) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (F0 F2 FM : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM) :
    ∃ caps : (List ℕ × List ℕ) → Caps, ∃ w : (List ℕ × List ℕ) → ℝ,
      ∃ C : ℝ, 0 < C ∧ (∀ q, 0 < w q) ∧
      ∀ N d : ℕ, ∀ T Q D H M : ℝ, ∀ alpha betaShift : ℂ, ∀ W Phi : ℝ → ℂ,
      0 < N → 0 < d → 1 < T → (N:ℝ)+1 ≤ T → (d:ℝ) ≤ T → 1 ≤ Real.log T →
      1 ≤ (PRZZActualSignedBranches.frequencyBound d D H:ℝ) →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z → |betaShift.re| ≤ S/Real.log T →
      0 < M → Function.support FM ⊆ Icc (M/2) (3*M) → ContinuousOn W (Ioi 0) →
      ContDiff ℝ ∞ Phi → Function.support Phi ⊆ Icc (1:ℝ) 2 →
      ‖literal N d D H T (fun n => (coefficient js n:ℂ))
        (scaledCutoff F0 Q) F2 FM W Phi alpha betaShift‖ ≤
      ∑ j ∈ range (Nat.log 2 N+1), ∑ l ∈ range (Nat.log 2 N+1),
        (1/(2*Real.pi))*(∫ p, ‖PRZZDyadicEnvelope.common d T M ((2:ℝ)^j) ((2:ℝ)^l)
          W (alpha+betaShift) p‖)*
        rowBudget C w caps js eps eta beta T (PRZZActualSignedBranches.frequencyBound d D H) N d K j l*
        (∫ t : ℝ, (1+|t|)*‖mellin Phi (t*I)‖) := by
  obtain ⟨caps,w,C,hC,hw,hrow⟩ := signedRow_bound hWeil hDI K hK js eps eta beta S Z
    heps heta hbeta hS hZ F0 F2 FM hf hc hF hcF hM hcM
  refine ⟨caps,w,C,hC,hw,?_⟩
  intro N d T Q D H M alpha betaShift W Phi hN hd hT hNT hdT hlog hfreq ha hz hb hMp hsM hW hPhi hsP
  rw [PRZZLiteralRows.literal_rows N d D H T M _ _ F2 FM W Phi alpha betaShift
    hN (by linarith) hMp hM hW hPhi.continuous hsM hsP]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro j hj
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro l hl
  apply row_integral_bound N d j l D H T M _ _ _ F2 FM W Phi alpha betaShift
    hN hd (by linarith) hMp hM hW hPhi hsM hsP
    (rowBudget_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ hC.le (fun q => (hw q).le)
      (by linarith) (by positivity))
  intro p hp t
  exact hrow N d j l T Q D H p.1 p.2 t alpha betaShift hN hd hT hNT hdT hlog hfreq ha hz hb

#print axioms rowBudget_nonneg
#print axioms signedRow_bound
#print axioms literal_row_budgets

/-- The actual sourceW specialization: no global continuity premise on W,
no assumed row bound, and no assumed Fubini identity. The sharp row masses
stay paired with their budgets, ready for nonempty_row_absorbed. -/
theorem literal_sourceW_rows
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js : List ℕ) (eps eta beta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hbeta : 0 < beta) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (F0 F2 FM : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM) :
    ∃ caps : (List ℕ × List ℕ) → Caps, ∃ w : (List ℕ × List ℕ) → ℝ,
      ∃ C : ℝ, 0 < C ∧ (∀ q, 0 < w q) ∧
      ∀ N d : ℕ, ∀ T Q D H M : ℝ, ∀ alpha betaShift sigma : ℂ, ∀ Phi : ℝ → ℂ,
      0 < N → 0 < d → 1 < T → (N:ℝ)+1 ≤ T → (d:ℝ) ≤ T → 1 ≤ Real.log T →
      1 ≤ (PRZZActualSignedBranches.frequencyBound d D H:ℝ) →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z → |betaShift.re| ≤ S/Real.log T →
      0 < M → Function.support FM ⊆ Icc (M/2) (3*M) → sigma ≠ 0 →
      ContDiff ℝ ∞ Phi → Function.support Phi ⊆ Icc (1:ℝ) 2 →
      ‖literal N d D H T (fun n => (coefficient js n:ℂ))
        (scaledCutoff F0 Q) F2 FM (PRZZDyadicEnvelope.sourceW sigma) Phi alpha betaShift‖ ≤
      ∑ j ∈ range (Nat.log 2 N+1), ∑ l ∈ range (Nat.log 2 N+1),
        (1/(2*Real.pi))*(∫ p, ‖PRZZDyadicEnvelope.common d T M ((2:ℝ)^j) ((2:ℝ)^l)
          (PRZZDyadicEnvelope.sourceW sigma) (alpha+betaShift) p‖)*
        rowBudget C w caps js eps eta beta T (PRZZActualSignedBranches.frequencyBound d D H) N d K j l*
        (∫ t : ℝ, (1+|t|)*‖mellin Phi (t*I)‖) := by
  obtain ⟨caps,w,C,hC,hw,h⟩ := literal_row_budgets hWeil hDI K hK js eps eta beta S Z
    heps heta hbeta hS hZ F0 F2 FM hf hc hF hcF hM hcM
  refine ⟨caps,w,C,hC,hw,?_⟩
  intro N d T Q D H M alpha betaShift sigma Phi hN hd hT hNT hdT hlog hfreq ha hz hb hMp hsM hs hPhi hsP
  exact h N d T Q D H M alpha betaShift _ Phi hN hd hT hNT hdT hlog hfreq ha hz hb hMp hsM
    (PRZZSourceWOuter.sourceW_continuous sigma hs) hPhi hsP

#print axioms literal_sourceW_rows
end XiPrime8845.PRZZRowIntegralBudget
