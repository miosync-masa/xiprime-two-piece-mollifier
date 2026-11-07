import PRZZLocalTailBudget

/-! Complete active freezing defects, not only the empty-h subfamily.
The literal row integral is bounded with its actual spatial power weight.
The N <= T^(4/7) restriction and the 6 eps + 2 eta loss remain explicit. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Set MeasureTheory Filter Finset
namespace XiPrime8845.PRZZFullFreezeBudget
open PRZZActualPoissonError PRZZActiveFreezeBudget PRZZEmptyMomentMass PRZZPrefactorMass
set_option maxHeartbeats 8000000
attribute [local instance] Classical.propDecidable

def fullMass (L J : ℕ) (F : ℝ → ℂ) (phi : ℝ → ℂ) (js : List ℕ) (N K : ℕ)
    (T M Q V eps _eH : ℝ) (G1 G2 : ℝ → ℂ) (alpha beta sigma : ℂ) : ℝ :=
  ∑ d ∈ Icc 1 N, ∑ j ∈ range (Nat.log 2 N+1),
    ∑ l ∈ range (Nat.log 2 N+1), ∑ k ∈ range K,
      ∑ z ∈ active N d j l (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k*M) Q eps) 2
        (PRZZMellinSeparation.scaledCutoff G1 Q) (PRZZMellinSeparation.scaledCutoff G2 V),
        ‖rowIntegral L J F ((2:ℝ)^k*M) T z alpha beta sigma
          (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) d
          (PRZZMellinSeparation.scaledCutoff G1 Q) (PRZZMellinSeparation.scaledCutoff G2 V) phi‖

theorem mass_bound (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3) (Z : ℝ) :
    ∃ E : ℝ, 0 < E ∧ ∀ (L J N K : ℕ) (js : List ℕ) (T M Q V eps eH eta : ℝ)
      (G1 G2 phi : ℝ → ℂ) (alpha beta sigma : ℂ),
      ‖(1/2:ℂ)+beta‖ ≤ Z → sigma ≠ 0 → Continuous phi → 0 < T → 0 < M → 0 < Q →
      0 ≤ eta → |alpha.re+beta.re| ≤ eta → Function.support G1 ⊆ Icc (1/2:ℝ) 3 → 8 ≤ T^(1-eps) →
      fullMass L J F phi js N K T M Q V eps eH G1 G2 alpha beta sigma ≤
        (E*(1+1/‖sigma‖^2)*(∫ t in Icc T (2*T), ‖phi t‖))*
          outerMoment js N K T M Q V eps eta G1 G2 beta alpha := by
  obtain ⟨E,hE,h⟩ := PRZZActualPoissonError.row_bound F hF hcF hsF Z
  refine ⟨E,hE,?_⟩
  intro L J N K js T M Q V eps eH eta G1 G2 phi alpha beta sigma
    hz hs hphi hT hM hQ heta hshift hs1 hheight
  unfold fullMass outerMoment
  rw [mul_sum]
  apply sum_le_sum; intro d hd
  rw [mul_sum]
  apply sum_le_sum; intro j hj
  rw [mul_sum]
  apply sum_le_sum; intro l hl
  rw [mul_sum]
  apply sum_le_sum; intro k hk
  unfold rowMoment
  calc
    _ ≤ ∑ z ∈ active N d j l (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k*M) Q eps) 2
        (PRZZMellinSeparation.scaledCutoff G1 Q) (PRZZMellinSeparation.scaledCutoff G2 V),
        E*(1+1/‖sigma‖^2)*(z.1.2:ℝ)^(1+eta)*(3*((2:ℝ)^k*M))^eta*
          sourceCost T ((2:ℝ)^k*M) eps j l*
          ‖PRZZAStar.prefactor (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
            (PRZZMellinSeparation.scaledCutoff G1 Q) (PRZZMellinSeparation.scaledCutoff G2 V)
            d beta alpha z/((z.1.1:ℂ)*(z.1.2:ℂ))‖*(∫ t in Icc T (2*T), ‖phi t‖) := by
      apply sum_le_sum; intro z ha
      exact h L J N d j l T ((2:ℝ)^k*M) Q eps eta z alpha beta sigma _ _ _ phi
        hz hs hphi (mem_Icc.mp hd).1 hT (by positivity) hQ heta hshift
        (PRZZFreezeScales.scaled_support G1 Q hQ hs1) hheight ha
    _ = _ := by
      simp only [mul_sum]
      apply sum_congr rfl; intro z hz
      ring

theorem scaled_bound
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (G1 G2 : ℝ → ℂ) (hG1 : Continuous G1) (hG2 : Continuous G2)
    (hcG1 : HasCompactSupport G1) (hcG2 : HasCompactSupport G2)
    (hsG1 : Function.support G1 ⊆ Icc (1/2:ℝ) 3) (hsG2 : Function.support G2 ⊆ Icc (1/2:ℝ) 3)
    (js : List ℕ) (S r eps eta delta : ℝ) (hS : 0 ≤ S) (hr : 0 < r)
    (heps : 0 ≤ eps) (heta : 0 < eta) (heta1 : eta ≤ 1) (hmargin : 6*eps+2*eta < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L J N K : ℕ) (T M Q V eH : ℝ) (A B : ℂ),
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      1 ≤ N → 1 ≤ T → 1 ≤ Real.log T → 2*S/eta ≤ Real.log T → (N:ℝ) ≤ T^(4/7:ℝ) →
      8 ≤ T^(1-eps) → 0 < M → 0 < Q → 0 < V → ∀ (phi : ℝ → ℂ) (P : ℝ),
      Continuous phi → 0 ≤ P → (∀ t ∈ Icc T (2*T), ‖phi t‖ ≤ P) →
      fullMass L J F phi js N K T M Q V eps eH G1 G2
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) ((A+B)/(Real.log T:ℂ)) ≤
          C*P*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨E,hE,hmass⟩ := mass_bound F hF hcF hsF (S+1)
  obtain ⟨D,hD,hbudget⟩ := PRZZEmptyMomentMass.absorbed G1 G2 hG1 hG2 hcG1 hcG2 hsG1 hsG2
    js S r eps eta delta hS hr heps heta.le heta1 hmargin
  refine ⟨E*D,by positivity,?_⟩
  intro L J N K T M Q V eH A B hA hB hsep hN hT hL hleta hscale hheight hM hQ hV phi P hphi hP hp
  have ht : 0 < T := by linarith
  have hl : 0 < Real.log T := by linarith
  have hlc : (Real.log T:ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  have hab : A+B ≠ 0 := norm_pos_iff.mp (hr.trans_le hsep)
  have hs : (A+B)/(Real.log T:ℂ) ≠ 0 := div_ne_zero hab hlc
  have hbn : ‖B/(Real.log T:ℂ)‖ ≤ S := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hl]
    exact (div_le_div_of_nonneg_right hB hl.le).trans (div_le_self hS hL)
  have hz : ‖(1/2:ℂ)+B/(Real.log T:ℂ)‖ ≤ S+1 := by
    have hh : ‖(1/2:ℂ)‖ = (1/2:ℝ) := by norm_num
    calc
      _ ≤ ‖(1/2:ℂ)‖+‖B/(Real.log T:ℂ)‖ := norm_add_le _ _
      _ ≤ (1/2:ℝ)+S := add_le_add hh.le hbn
      _ ≤ S+1 := by linarith
  have hstrip := scaled_strip A B S (Real.log T) eta hl heta hleta hA hB
  have hm := hmass L J N K js T M Q V eps eH eta G1 G2 phi _ _ _
    hz hs hphi ht hM hQ heta.le hstrip hsG1 hheight
  have hshift : 1+1/‖(A+B)/(Real.log T:ℂ)‖^2 ≤ 1+(Real.log T)^2/r^2 := by
    have he : 1/‖(A+B)/(Real.log T:ℂ)‖^2 = (Real.log T)^2/‖A+B‖^2 := by
      rw [norm_div,div_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
      field_simp
    rw [he]
    gcongr
  have hw : 0 ≤ outerMoment js N K T M Q V eps eta G1 G2
      (B/(Real.log T:ℂ)) (A/(Real.log T:ℂ)) := by
    unfold outerMoment rowMoment sourceCost PRZZFreezeScales.ratioCap
    positivity
  have hbound := hbudget N K T M Q V _ _ hN hT hL hscale hM hQ hV
    (PRZZFreezeErrorBudget.scaled_real_bound B S (Real.log T) hl hB)
    (PRZZFreezeErrorBudget.scaled_real_bound A S (Real.log T) hl hA)
  have hh := mul_le_mul hshift (phi_mass T P ht.le phi hp)
    (integral_nonneg (fun t => norm_nonneg _)) (by positivity)
  have hh' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh hE.le) hw
  have he := mul_le_mul_of_nonneg_left hbound (show 0 ≤ E*P by positivity)
  have hstep : fullMass L J F phi js N K T M Q V eps eH G1 G2
      (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) ((A+B)/(Real.log T:ℂ)) ≤
      (E*((1+(Real.log T)^2/r^2)*(P*T)))*
        outerMoment js N K T M Q V eps eta G1 G2 (B/(Real.log T:ℂ)) (A/(Real.log T:ℂ)) := by
    apply hm.trans
    convert hh' using 1 <;> ring
  apply hstep.trans
  convert he using 1 <;> ring


/-- The actual active row defect is the integral of the native freezing
component. No equality with an unspecified analytic error is assumed. -/
theorem active_freeze_identity (L J N d j l : ℕ) (F : ℝ → ℂ)
    (hF : ContDiff ℝ ∞ F) (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (T M Q eps : ℝ) (z : PRZZAStar.Index) (alpha beta : ℂ)
    (a : ℕ → ℂ) (F1 F2 phi : ℝ → ℂ)
    (hd : 0 < d) (hT : 0 < T) (hM : 0 < M) (hs : alpha+beta ≠ 0)
    (hs1 : Function.support F1 ⊆ Icc (Q/2) (3*Q)) (hheight : 8 ≤ T^(1-eps))
    (hz : z ∈ active N d j l (PRZZSourceCutoffs.deltaCutoff T M Q eps) 2 F1 F2) :
    rowIntegral L J F M T z alpha beta (alpha+beta) a d F1 F2 phi =
      ∫ t in Icc T (2*T), phi t*
        PRZZNativeComponents.row .freeze L J F F1 F2 M z alpha beta a d t := by
  rw [row_identity L J N d j l F hF hsF T M Q eps z alpha beta (alpha+beta) a F1 F2 phi
    hd hT hM hs hs1 hheight hz]
  have hsmall := active_small_gap N d j l T M Q eps F1 F2 hd hT hM hs1 hheight z hz
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [PRZZNativeComponents.row,if_pos hsmall]
  ring

theorem partition_bound (F G1 G2 : ℝ → ℂ)
    (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hG1 : Continuous G1) (hG2 : Continuous G2)
    (hcG1 : HasCompactSupport G1) (hcG2 : HasCompactSupport G2)
    (hsG1 : Function.support G1 ⊆ Icc (1/2:ℝ) 3)
    (hsG2 : Function.support G2 ⊆ Icc (1/2:ℝ) 3)
    (js : List ℕ) (S r eps eta delta : ℝ) (hS : 0 ≤ S) (hr : 0 < r)
    (heps : 0 ≤ eps) (heta : 0 < eta) (heta1 : eta ≤ 1) (hmargin : 6*eps+2*eta < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L J N K : ℕ) (T M eH : ℝ) (A B : ℂ) (phi : ℝ → ℂ) (P : ℝ),
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      1 ≤ N → 1 ≤ T → 1 ≤ Real.log T → 2*S/eta ≤ Real.log T → (N:ℝ) ≤ T^(4/7:ℝ) →
      8 ≤ T^(1-eps) → 0 < M → Continuous phi → 0 ≤ P →
      (∀ t ∈ Icc T (2*T), ‖phi t‖ ≤ P) →
      (∑ p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2),
        fullMass L J F phi js N K T M ((2:ℝ)^p.1) ((2:ℝ)^p.2) eps eH G1 G2
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) ((A+B)/(Real.log T:ℂ))) ≤
        C*P*T^delta*PRZZOptimalPowers.target N T := by
  let d0 := (6*eps+2*eta+delta)/2
  have hm : 6*eps+2*eta < d0 := by dsimp [d0]; linarith
  have hg : 0 < delta-d0 := by dsimp [d0]; linarith
  obtain ⟨C,hC,h⟩ := scaled_bound F hF hcF hsF G1 G2 hG1 hG2 hcG1 hcG2 hsG1 hsG2
    js S r eps eta d0 hS hr heps heta heta1 hm
  obtain ⟨D,hD,hgrid⟩ := PRZZLocalTailBudget.arithmetic_grid_absorbed (delta-d0) hg
  refine ⟨D*C,by positivity,?_⟩
  intro L J N K T M eH A B phi P hA hB hsep hN hT hlog hleta hscale hheight hM hphi hP hp
  have hT0 : 0 < T := by linarith
  have hNT : (N:ℝ) ≤ T := hscale.trans (by
    simpa using Real.rpow_le_rpow_of_exponent_le hT (by norm_num : (4/7:ℝ) ≤ 1))
  calc
    _ ≤ ∑ _p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2),
        C*P*T^d0*PRZZOptimalPowers.target N T := by
      apply sum_le_sum; intro p hp'
      exact h L J N K T M _ _ eH A B hA hB hsep hN hT hlog hleta hscale hheight hM
        (by positivity) (by positivity) phi P hphi hP hp
    _ = ((range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2)).card:ℝ)*
        (C*P*T^d0*PRZZOptimalPowers.target N T) := by simp only [sum_const,nsmul_eq_mul]
    _ ≤ (D*T^(delta-d0))*(C*P*T^d0*PRZZOptimalPowers.target N T) := by
      apply mul_le_mul_of_nonneg_right (hgrid N hN T hNT hlog)
      unfold PRZZOptimalPowers.target; positivity
    _ = _ := by
      rw [show delta = (delta-d0)+d0 by ring,Real.rpow_add hT0]
      ring

#print axioms active_freeze_identity
#print axioms mass_bound
#print axioms scaled_bound
#print axioms partition_bound
end XiPrime8845.PRZZFullFreezeBudget

