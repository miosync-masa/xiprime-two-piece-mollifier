import PRZZMixedReplacement

/-! The actual mixed zeta-to-W error integral: direct replacement, genuine
dual Gamma multiplier and noncentral residues share one sharp target.
Coefficients may depend on height after a common cap is fixed. This does
not estimate the later post-Poisson components or close the full moment. -/
noncomputable section
open Complex MeasureTheory Set Filter
open scoped BigOperators
namespace XiPrime8845.PRZZMixedDefect
set_option maxHeartbeats 10000000

theorem polynomial_bound (c : ℕ → ℂ) (N : ℕ) (H t : ℝ) (hH : 0 ≤ H)
    (hc : ∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ H) :
    ‖PRZZ.dirichletPolynomial c N (1/2+t*I)‖ ≤ 2*H*Real.sqrt N := by
  unfold PRZZ.dirichletPolynomial
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N, H*(1/Real.sqrt n) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [PRZZMeanSquare.summand _ _ (Finset.mem_Icc.mp hn).1,norm_mul,
        PRZZMeanSquare.phase_norm,mul_one,PRZZMeanSquare.normalized_norm _ _ (Finset.mem_Icc.mp hn).1]
      exact (div_le_div_of_nonneg_right (hc n hn) (Real.sqrt_nonneg _)).trans_eq (by ring)
    _ = H*(∑ n ∈ Finset.Icc 1 N, 1/Real.sqrt n) := (Finset.mul_sum ..).symm
    _ ≤ H*(2*Real.sqrt N) := mul_le_mul_of_nonneg_left (PRZZReplacementMass.reciprocal_sqrt_sum N) hH
    _ = _ := by ring

theorem weight_bound (c d : ℕ → ℂ) (N : ℕ) (H : ℝ) (hH : 0 ≤ H)
    (hc : ∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ H) (hd : ∀ n ∈ Finset.Icc 1 N, ‖d n‖ ≤ H)
    (phi : ℝ → ℂ) (t : ℝ) :
    ‖PRZZMollifiedTime.mollifierWeight phi c d N t‖ ≤ (4*(N:ℝ)*H^2)*‖phi t‖ := by
  rw [PRZZMollifiedTime.mollifierWeight,norm_mul,norm_mul,norm_star]
  have hh := mul_le_mul (polynomial_bound c N H t hH hc) (polynomial_bound d N H t hH hd)
    (norm_nonneg _) (by positivity)
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ N by positivity)
  have hp := mul_le_mul_of_nonneg_left hh (norm_nonneg (phi t))
  calc
    _ = ‖phi t‖*(‖PRZZ.dirichletPolynomial c N (1/2+t*I)‖*
        ‖PRZZ.dirichletPolynomial d N (1/2+t*I)‖) := by ring
    _ ≤ ‖phi t‖*(2*H*Real.sqrt N*(2*H*Real.sqrt N)) := hp
    _ = (4*(N:ℝ)*H^2)*‖phi t‖ := by
      calc
        _ = 4*H^2*‖phi t‖*(Real.sqrt N)^2 := by ring
        _ = _ := by rw [hs]; ring

theorem residue_target (S r H : ℝ) (hr : 0 < r) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ∀ (c d : ℕ → ℂ) (N : ℕ), 1 ≤ N → (N:ℝ) ≤ T →
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ H) → (∀ n ∈ Finset.Icc 1 N, ‖d n‖ ≤ H) →
      ∀ (phi : ℝ → ℂ) (P : ℝ), Continuous phi → 0 ≤ P →
      (∀ t ∈ Icc T (2*T), ‖phi t‖ ≤ P) →
      ‖∫ t in Icc T (2*T), PRZZMollifiedTime.mollifierWeight phi c d N t *
        PRZZContourAFE.noncentralSum (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t‖ ≤ C*P := by
  obtain ⟨C,hC,h⟩ := PRZZResidueTime.noncentral_bound
  refine ⟨C*(H^2+1),by positivity,?_⟩
  filter_upwards [PRZZScaledReplacement.shifts_eventually S (1/4) (by norm_num),
    PRZZResidueAbsorption.scalar_absorbed 0 r hr,eventually_ge_atTop (16*Real.pi+4)] with T hsmall hmass hT
  intro A B hA hB hsep c d N hN hNT hc hd phi P hphi hP hp
  let alpha := A/(Real.log T:ℂ)
  let beta := B/(Real.log T:ℂ)
  have hL : (Real.log T:ℂ) ≠ 0 := by exact_mod_cast (show Real.log T ≠ 0 by linarith [hsmall.1])
  have hs : alpha+beta ≠ 0 := by
    dsimp [alpha,beta]
    rw [← add_div]
    exact div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep)) hL
  have hi : IntegrableOn (fun t : ℝ => C*(4*(N:ℝ)*H^2)*(‖phi t‖*PRZZResidueTime.envelope (alpha+beta) t))
      (Icc T (2*T)) := by
    apply Continuous.integrableOn_Icc
    unfold PRZZResidueTime.envelope
    fun_prop
  have hbnd : ‖∫ t in Icc T (2*T), PRZZMollifiedTime.mollifierWeight phi c d N t*
      PRZZContourAFE.noncentralSum alpha beta t‖ ≤
      C*(4*(N:ℝ)*H^2)*(∫ t in Icc T (2*T), ‖phi t‖*PRZZResidueTime.envelope (alpha+beta) t) := by
    rw [← integral_const_mul]
    apply norm_integral_le_of_norm_le hi
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [norm_mul]
    have hh := mul_le_mul (weight_bound c d N H hH hc hd phi t)
      (h alpha beta (hsmall.2 A hA) (hsmall.2 B hB) hs t (by linarith [ht.1,Real.pi_pos]))
      (norm_nonneg _) (by positivity)
    exact hh.trans_eq (by ring)
  have he := PRZZResidueTime.envelope_integral (alpha+beta) T P hT hP phi hp
  have hm := hmass A B hsep N hN hNT
  simp only [pow_zero,mul_one] at hm
  have hh := hbnd.trans (mul_le_mul_of_nonneg_left he (by positivity))
  have hh' := mul_le_mul_of_nonneg_left hm (show 0 ≤ C*H^2*P by positivity)
  change _ ≤ C*(H^2+1)*P
  nlinarith

theorem dual_target (S r delta H : ℝ) (hS : 0 ≤ S) (hr : 0 < r) (hd : 0 < delta) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ∀ (c d : ℕ → ℂ) (N : ℕ), 1 ≤ N → (N:ℝ) ≤ T →
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ H) → (∀ n ∈ Finset.Icc 1 N, ‖d n‖ ≤ H) →
      ∀ (phi : ℝ → ℂ) (P : ℝ), Continuous phi → 0 ≤ P →
      (∀ t ∈ Icc T (2*T), ‖phi t‖ ≤ P) →
      ‖∫ t in Icc T (2*T), PRZZMollifiedTime.mollifierWeight phi c d N t *
        PRZZAFEDual.dualMultiplier (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t *
        PRZZReplacementIntegral.difference (-(B/(Real.log T:ℂ))) (-(A/(Real.log T:ℂ))) t‖ ≤
        C*P*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := PRZZMixedReplacement.scaled_target S r delta H hr hd hH
  refine ⟨C*Real.exp (2*S+7),by positivity,?_⟩
  filter_upwards [h,PRZZDualError.multiplier_scaled_cap S hS,
    PRZZScaledReplacement.shifts_eventually S (1/16) (by norm_num)] with T h hcap hsmall
  intro A B hA hB hsep c d N hN hNT hc hd' phi P hphi hP hp
  have ha := abs_le.mp ((Complex.abs_re_le_norm _).trans (hsmall.2 A hA))
  have hb := abs_le.mp ((Complex.abs_re_le_norm _).trans (hsmall.2 B hB))
  have hmul := PRZZMollifiedTime.dualMultiplier_continuous (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))
    (by linarith [ha.1]) (by linarith [ha.2]) (by linarith [hb.1]) (by linarith [hb.2])
  have hs : r ≤ ‖-B + -A‖ := by
    rw [show -B + -A = -(A+B) by ring,norm_neg]; exact hsep
  have hh := h (-B) (-A) (by simpa using hB) (by simpa using hA) hs c d N hN hNT hc hd'
    (fun t => phi t*PRZZAFEDual.dualMultiplier (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t)
    (P*Real.exp (2*S+7)) (hphi.mul hmul) (by positivity)
    (fun t ht => by rw [norm_mul]; exact mul_le_mul (hp t ht) (hcap A B hA hB t ht) (norm_nonneg _) hP)
  convert hh using 1
  · congr 1
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    simp only [neg_div,PRZZMollifiedTime.mollifierWeight]
    ring
  · ring

theorem defect_target (S r delta H : ℝ) (hS : 0 ≤ S) (hr : 0 < r) (hd : 0 < delta) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ∀ (c d : ℕ → ℂ) (N : ℕ), 1 ≤ N → (N:ℝ) ≤ T →
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ H) → (∀ n ∈ Finset.Icc 1 N, ‖d n‖ ≤ H) →
      ∀ (phi : ℝ → ℂ) (P : ℝ), Continuous phi → 0 ≤ P →
      (∀ t ∈ Icc T (2*T), ‖phi t‖ ≤ P) →
      ‖∫ t in Icc T (2*T), PRZZMollifiedTime.mollifierWeight phi c d N t *
        PRZZIntegratedDefect.defect (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t‖ ≤
        C*P*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := PRZZMixedReplacement.defect_bound S r delta H hr hd hH
  obtain ⟨R,hR,hres⟩ := residue_target S r H hr hH
  obtain ⟨D,hD,hdual⟩ := dual_target S r delta H hS hr hd hH
  refine ⟨C+R+D,by positivity,?_⟩
  filter_upwards [h,hres,hdual,eventually_ge_atTop (1:ℝ)] with T h hres hdual hT
  intro A B hA hB hsep c d N hN hNT hc hd' phi P hphi hP hp
  have hh := h A B hA hB hsep c d N hN hNT hc hd' phi P hphi hP hp
  dsimp only at hh
  have hr' := hres A B hA hB hsep c d N hN hNT hc hd' phi P hphi hP hp
  have hd'' := hdual A B hA hB hsep c d N hN hNT hc hd' phi P hphi hP hp
  have htau : 1 ≤ T^delta := Real.one_le_rpow hT hd.le
  have htar : 1 ≤ PRZZOptimalPowers.target N T := by
    have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
    have hn' := Real.one_le_rpow hn (by norm_num : (0:ℝ) ≤ 7/4)
    unfold PRZZOptimalPowers.target
    have hz : 0 ≤ T^(1/2:ℝ)*(N:ℝ)^(7/8:ℝ) := by positivity
    linarith
  have he := mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le htau htar)
    (show 0 ≤ R*P by positivity)
  nlinarith

#print axioms polynomial_bound
#print axioms weight_bound
#print axioms residue_target
#print axioms dual_target
#print axioms defect_target
end XiPrime8845.PRZZMixedDefect
