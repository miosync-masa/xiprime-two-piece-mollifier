import PRZZFullFreezeBudget
import PRZZCappedFreezeMoment
import PRZZClassZeroCorrection

/-! Actual all-active freezing row integrals with a common coefficient cap.
The analytic spatial power and all original gcd/dyadic/spatial sums are paid.
The physical profiles stay fixed; no class-uniform derivative assertion is made. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Set MeasureTheory Filter Finset
namespace XiPrime8845.PRZZCappedFreezeBudget
open PRZZActualPoissonError PRZZActiveFreezeBudget PRZZEmptyMomentMass PRZZPrefactorMass
set_option maxHeartbeats 9000000
attribute [local instance] Classical.propDecidable

def fullMass (L J : ℕ) (F : ℝ → ℂ) (phi : ℝ → ℂ) (c : ℕ → ℂ) (N K : ℕ)
    (T M Q V eps _eH : ℝ) (G1 G2 : ℝ → ℂ) (alpha beta sigma : ℂ) : ℝ :=
  ∑ d ∈ Icc 1 N, ∑ j ∈ range (Nat.log 2 N+1),
    ∑ l ∈ range (Nat.log 2 N+1), ∑ k ∈ range K,
      ∑ z ∈ active N d j l (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k*M) Q eps) 2
        (PRZZMellinSeparation.scaledCutoff G1 Q) (PRZZMellinSeparation.scaledCutoff G2 V),
        ‖rowIntegral L J F ((2:ℝ)^k*M) T z alpha beta sigma
          c d
          (PRZZMellinSeparation.scaledCutoff G1 Q) (PRZZMellinSeparation.scaledCutoff G2 V) phi‖

theorem mass_bound (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3) (Z : ℝ) :
    ∃ E : ℝ, 0 < E ∧ ∀ (L J N K : ℕ) (c : ℕ → ℂ) (T M Q V eps eH eta : ℝ)
      (G1 G2 phi : ℝ → ℂ) (alpha beta sigma : ℂ),
      ‖(1/2:ℂ)+beta‖ ≤ Z → sigma ≠ 0 → Continuous phi → 0 < T → 0 < M → 0 < Q →
      0 ≤ eta → |alpha.re+beta.re| ≤ eta → Function.support G1 ⊆ Icc (1/2:ℝ) 3 → 8 ≤ T^(1-eps) →
      fullMass L J F phi c N K T M Q V eps eH G1 G2 alpha beta sigma ≤
        (E*(1+1/‖sigma‖^2)*(∫ t in Icc T (2*T), ‖phi t‖))*
          PRZZCappedFreezeMoment.outerMoment c N K T M Q V eps eta G1 G2 beta alpha := by
  obtain ⟨E,hE,h⟩ := PRZZActualPoissonError.row_bound F hF hcF hsF Z
  refine ⟨E,hE,?_⟩
  intro L J N K c T M Q V eps eH eta G1 G2 phi alpha beta sigma
    hz hs hphi hT hM hQ heta hshift hs1 hheight
  unfold fullMass PRZZCappedFreezeMoment.outerMoment
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
          ‖PRZZAStar.prefactor c
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
    (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (S r eps eta delta : ℝ) (hS : 0 ≤ S) (hr : 0 < r)
    (heps : 0 ≤ eps) (heta : 0 < eta) (heta1 : eta ≤ 1) (hmargin : 6*eps+2*eta < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : ℕ → ℂ) (L J N K : ℕ) (T M Q V eH : ℝ) (A B : ℂ),
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ Hcap) → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      1 ≤ N → 1 ≤ T → 1 ≤ Real.log T → 2*S/eta ≤ Real.log T → (N:ℝ) ≤ T^(4/7:ℝ) →
      8 ≤ T^(1-eps) → 0 < M → 0 < Q → 0 < V → ∀ (phi : ℝ → ℂ) (P : ℝ),
      Continuous phi → 0 ≤ P → (∀ t ∈ Icc T (2*T), ‖phi t‖ ≤ P) →
      fullMass L J F phi c N K T M Q V eps eH G1 G2
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) ((A+B)/(Real.log T:ℂ)) ≤
          C*P*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨E,hE,hmass⟩ := mass_bound F hF hcF hsF (S+1)
  obtain ⟨D,hD,hbudget⟩ := PRZZCappedFreezeMoment.absorbed G1 G2 hG1 hG2 hcG1 hcG2 hsG1 hsG2
    Hcap hHcap S r eps eta delta hS hr heps heta.le heta1 hmargin
  refine ⟨E*D,by positivity,?_⟩
  intro c L J N K T M Q V eH A B hcoef hA hB hsep hN hT hL hleta hscale hheight hM hQ hV phi P hphi hP hp
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
  have hm := hmass L J N K c T M Q V eps eH eta G1 G2 phi _ _ _
    hz hs hphi ht hM hQ heta.le hstrip hsG1 hheight
  have hshift : 1+1/‖(A+B)/(Real.log T:ℂ)‖^2 ≤ 1+(Real.log T)^2/r^2 := by
    have he : 1/‖(A+B)/(Real.log T:ℂ)‖^2 = (Real.log T)^2/‖A+B‖^2 := by
      rw [norm_div,div_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
      field_simp
    rw [he]
    gcongr
  have hw : 0 ≤ PRZZCappedFreezeMoment.outerMoment c N K T M Q V eps eta G1 G2
      (B/(Real.log T:ℂ)) (A/(Real.log T:ℂ)) := by
    unfold PRZZCappedFreezeMoment.outerMoment rowMoment sourceCost PRZZFreezeScales.ratioCap
    positivity
  have hbound := hbudget c N K T M Q V _ _ hcoef hN hT hL hscale hM hQ hV
    (PRZZFreezeErrorBudget.scaled_real_bound B S (Real.log T) hl hB)
    (PRZZFreezeErrorBudget.scaled_real_bound A S (Real.log T) hl hA)
  have hh := mul_le_mul hshift (phi_mass T P ht.le phi hp)
    (integral_nonneg (fun t => norm_nonneg _)) (by positivity)
  have hh' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh hE.le) hw
  have he := mul_le_mul_of_nonneg_left hbound (show 0 ≤ E*P by positivity)
  have hstep : fullMass L J F phi c N K T M Q V eps eH G1 G2
      (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) ((A+B)/(Real.log T:ℂ)) ≤
      (E*((1+(Real.log T)^2/r^2)*(P*T)))*
        PRZZCappedFreezeMoment.outerMoment c N K T M Q V eps eta G1 G2 (B/(Real.log T:ℂ)) (A/(Real.log T:ℂ)) := by
    apply hm.trans
    convert hh' using 1; ring
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

def field (L J : ℕ) (F : ℝ → ℂ) (phi : ℝ → ℂ) (c : ℕ → ℂ) (N K : ℕ)
    (T M Q V eps _eH : ℝ) (G1 G2 : ℝ → ℂ) (alpha beta sigma : ℂ) : ℂ :=
  ∑ d ∈ Icc 1 N, ∑ j ∈ range (Nat.log 2 N+1),
    ∑ l ∈ range (Nat.log 2 N+1), ∑ k ∈ range K,
      ∑ z ∈ active N d j l (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k*M) Q eps) 2
        (PRZZMellinSeparation.scaledCutoff G1 Q) (PRZZMellinSeparation.scaledCutoff G2 V),
        rowIntegral L J F ((2:ℝ)^k*M) T z alpha beta sigma
          c d
          (PRZZMellinSeparation.scaledCutoff G1 Q) (PRZZMellinSeparation.scaledCutoff G2 V) phi


theorem norm_le_fullMass (L J N K : ℕ) (F phi : ℝ → ℂ) (c : ℕ → ℂ)
    (T M Q V eps eH : ℝ) (G1 G2 : ℝ → ℂ) (alpha beta sigma : ℂ) :
    ‖field L J F phi c N K T M Q V eps eH G1 G2 alpha beta sigma‖ ≤
      fullMass L J F phi c N K T M Q V eps eH G1 G2 alpha beta sigma := by
  unfold field fullMass
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro d hd
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro j hj
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro l hl
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro k hk
  exact norm_sum_le _ _

theorem mixed_scaled_bound
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (G1 G2 : ℝ → ℂ) (hG1 : Continuous G1) (hG2 : Continuous G2)
    (hcG1 : HasCompactSupport G1) (hcG2 : HasCompactSupport G2)
    (hsG1 : Function.support G1 ⊆ Icc (1/2:ℝ) 3) (hsG2 : Function.support G2 ⊆ Icc (1/2:ℝ) 3)
    (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (S r eps eta delta : ℝ) (hS : 0 ≤ S) (hr : 0 < r)
    (heps : 0 ≤ eps) (heta : 0 < eta) (heta1 : eta ≤ 1) (hmargin : 6*eps+2*eta < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c d : ℕ → ℂ) (L J N K : ℕ) (T M Q V eH : ℝ) (A B : ℂ),
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ Hcap) →
      (∀ n ∈ Finset.Icc 1 N, ‖d n‖ ≤ Hcap) → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      1 ≤ N → 1 ≤ T → 1 ≤ Real.log T → 2*S/eta ≤ Real.log T → (N:ℝ) ≤ T^(4/7:ℝ) →
      8 ≤ T^(1-eps) → 0 < M → 0 < Q → 0 < V → ∀ (phi : ℝ → ℂ) (P : ℝ),
      Continuous phi → 0 ≤ P → (∀ t ∈ Icc T (2*T), ‖phi t‖ ≤ P) →
      ‖PRZZMixedPoisson.lift (fun a => field L J F phi a N K T M Q V eps eH G1 G2
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) ((A+B)/(Real.log T:ℂ))) c d‖ ≤
          C*P*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := scaled_bound F hF hcF hsF G1 G2 hG1 hG2 hcG1 hcG2 hsG1 hsG2
    (2*Hcap) (by positivity) S r eps eta delta hS hr heps heta heta1 hmargin
  refine ⟨C,hC,?_⟩
  intro c d L J N K T M Q V eH A B hc hd hA hB hsep hN hT hL hleta hscale hheight hM hQ hV phi P hphi hP hp
  apply PRZZClassZeroCorrection.lift_bound
  intro z hz
  exact (norm_le_fullMass L J N K F phi _ T M Q V eps eH G1 G2 _ _ _).trans
    (h _ L J N K T M Q V eH A B
      (PRZZClassZeroCorrection.combine_cap N c d Hcap hHcap hc hd z hz)
      hA hB hsep hN hT hL hleta hscale hheight hM hQ hV phi P hphi hP hp)

theorem paired_mixed_bound
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (G1 G2 : ℝ → ℂ) (hG1 : Continuous G1) (hG2 : Continuous G2)
    (hcG1 : HasCompactSupport G1) (hcG2 : HasCompactSupport G2)
    (hsG1 : Function.support G1 ⊆ Icc (1/2:ℝ) 3) (hsG2 : Function.support G2 ⊆ Icc (1/2:ℝ) 3)
    (Hcap : ℝ) (hHcap : 0 ≤ Hcap) (S r eps eta delta : ℝ) (hS : 0 ≤ S) (hr : 0 < r)
    (heps : 0 ≤ eps) (heta : 0 < eta) (heta1 : eta ≤ 1) (hmargin : 6*eps+2*eta < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (c d : ℕ → ℂ) (L J N K : ℕ) (M Q V eH : ℝ) (A B : ℂ),
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ Hcap) →
      (∀ n ∈ Finset.Icc 1 N, ‖d n‖ ≤ Hcap) → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      1 ≤ N → 1 ≤ T → 1 ≤ Real.log T → 2*S/eta ≤ Real.log T → (N:ℝ) ≤ T^(4/7:ℝ) →
      8 ≤ T^(1-eps) → 0 < M → 0 < Q → 0 < V → ∀ (phi : ℝ → ℂ) (P : ℝ),
      Continuous phi → 0 ≤ P → (∀ t ∈ Icc T (2*T), ‖phi t‖ ≤ P) →
      ‖PRZZMixedPoisson.lift (fun a => field L J F phi a N K T M Q V eps eH G1 G2
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) ((A+B)/(Real.log T:ℂ))) c d+
        PRZZMixedPoisson.lift (fun a => field L J F
          (fun t => phi t*PRZZAFEDual.dualMultiplier (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t)
          a N K T M Q V eps eH G1 G2 ((-B)/(Real.log T:ℂ)) ((-A)/(Real.log T:ℂ))
            ((-B+-A)/(Real.log T:ℂ))) c d‖ ≤
          C*P*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := mixed_scaled_bound F hF hcF hsF G1 G2 hG1 hG2 hcG1 hcG2 hsG1 hsG2
    Hcap hHcap S r eps eta delta hS hr heps heta heta1 hmargin
  refine ⟨C*(1+Real.exp (2*S+7)),by positivity,?_⟩
  filter_upwards [PRZZDualError.multiplier_scaled_cap S hS,
    PRZZScaledReplacement.shifts_eventually S (1/4) (by norm_num)] with T hgamma hsmall
  intro c d L J N K M Q V eH A B hc hd hA hB hsep hN hT hL hleta hscale hheight hM hQ hV phi P hphi hP hp
  have hpcont : Continuous (fun t => phi t*PRZZAFEDual.dualMultiplier
      (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t) :=
    hphi.mul (PRZZDualSmooth.multiplier_contDiff _ _ (hsmall.2 A hA) (hsmall.2 B hB)).continuous
  have hcap (t : ℝ) (ht : t ∈ Icc T (2*T)) :
      ‖phi t*PRZZAFEDual.dualMultiplier (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t‖ ≤
        P*Real.exp (2*S+7) := by
    rw [norm_mul]
    exact mul_le_mul (hp t ht) (hgamma A B hA hB t ht) (norm_nonneg _) hP
  have hs' : r ≤ ‖-B+-A‖ := by
    simpa only [show -B+-A = -(A+B) by ring,norm_neg] using hsep
  have h1 := h c d L J N K T M Q V eH A B hc hd hA hB hsep hN hT hL hleta hscale hheight hM hQ hV phi P hphi hP hp
  have h2 := h c d L J N K T M Q V eH (-B) (-A) hc hd (by simpa using hB) (by simpa using hA) hs'
    hN hT hL hleta hscale hheight hM hQ hV _ (P*Real.exp (2*S+7)) hpcont (by positivity) hcap
  exact ((norm_add_le _ _).trans (add_le_add h1 h2)).trans_eq (by ring)

#print axioms paired_mixed_bound
#print axioms norm_le_fullMass
#print axioms mixed_scaled_bound
#print axioms mass_bound
#print axioms scaled_bound
#print axioms active_freeze_identity
end XiPrime8845.PRZZCappedFreezeBudget
