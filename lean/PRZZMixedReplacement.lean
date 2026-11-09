import PRZZScaledReplacement
import PRZZWitnessBasis
import PRZZIntegratedDefect

/-! The actual V-W replacement error with independent, height-varying
coefficient slots. Its mean-square cost is evaluated from common coefficient
caps before the sequences are selected. This is one AFE error, not the full
Poisson/contour residual or an assertion about the public witness input. -/
noncomputable section
open Complex MeasureTheory Set Filter
namespace XiPrime8845.PRZZMixedReplacement
open PRZZMeanSquare
set_option maxHeartbeats 8000000

theorem replacement_mean (s eps : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1/2)
    (he : 0 < eps) (he' : eps ≤ 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℂ,
    ‖a‖ ≤ 1/4 → ‖b‖ ≤ 1/4 → a+b ≠ 0 →
    s ≤ 1/2+a.re → s ≤ 1/2+b.re → ∀ T : ℝ,
    256*Real.pi ≤ T → 128 ≤ T → ∀ (c d : ℕ → ℂ) (N : ℕ)
      (phi : ℝ → ℂ) (P : ℝ), Continuous phi → 0 ≤ P →
      (∀ t ∈ Icc T (2*T), ‖phi t‖ ≤ P) →
    ‖∫ t in Icc T (2*T), PRZZMollifiedTime.mollifierWeight phi c d N t *
      PRZZReplacementIntegral.difference a b t‖ ≤
      C*(1+32/‖a+b‖^2)*T^(eps-s)*P*((mean c N T+mean d N T)/2) := by
  obtain ⟨C,hC,h⟩ := PRZZProductSummation.integrated_bound s eps hs hs' he he'
  refine ⟨C,hC,?_⟩
  intro a b ha hb hab hsa hsb T hT hT' c d N phi P hphi hP hp
  rw [PRZZProductTime.difference_integral a b ha hb hab T hT hT']
  apply (h a b ha hb hab hsa hsb T hT hT' _
    (PRZZMollifiedTime.mollifierWeight_continuous phi hphi c d N)).trans
  have hi : (∫ t in Icc T (2*T), ‖PRZZMollifiedTime.mollifierWeight phi c d N t‖) ≤
      P*((mean c N T+mean d N T)/2) := by
    have hic : IntegrableOn (fun t : ℝ => ‖PRZZ.dirichletPolynomial c N (1/2+t*I)‖^2)
        (Icc T (2*T)) := ((PRZZMollifiedTime.polynomial_continuous c N).norm.pow 2).integrableOn_Icc
    have hid : IntegrableOn (fun t : ℝ => ‖PRZZ.dirichletPolynomial d N (1/2+t*I)‖^2)
        (Icc T (2*T)) := ((PRZZMollifiedTime.polynomial_continuous d N).norm.pow 2).integrableOn_Icc
    have hbnd : (∫ t in Icc T (2*T), ‖PRZZMollifiedTime.mollifierWeight phi c d N t‖) ≤
        ∫ t in Icc T (2*T), P*((‖PRZZ.dirichletPolynomial c N (1/2+t*I)‖^2+
          ‖PRZZ.dirichletPolynomial d N (1/2+t*I)‖^2)/2) := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
        (((hic.add hid).div_const 2).const_mul P)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      simp only [PRZZMollifiedTime.mollifierWeight,norm_mul,norm_star,Pi.add_apply]
      have hc0 := norm_nonneg (PRZZ.dirichletPolynomial c N (1/2+t*I))
      have hd0 := norm_nonneg (PRZZ.dirichletPolynomial d N (1/2+t*I))
      have hprod := mul_le_mul_of_nonneg_right (hp t ht) (mul_nonneg hc0 hd0)
      have hsq := mul_nonneg hP (sq_nonneg
        (‖PRZZ.dirichletPolynomial c N (1/2+t*I)‖-‖PRZZ.dirichletPolynomial d N (1/2+t*I)‖))
      nlinarith
    apply hbnd.trans_eq
    rw [integral_const_mul,integral_div,integral_add hic hid]
    rfl
  exact (mul_le_mul_of_nonneg_left hi (by positivity)).trans_eq (by ring)

theorem bounded_target (s eps : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1/2)
    (he : 0 < eps) (he' : eps ≤ 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℂ,
    ‖a‖ ≤ 1/4 → ‖b‖ ≤ 1/4 → a+b ≠ 0 →
    s ≤ 1/2+a.re → s ≤ 1/2+b.re → ∀ T : ℝ,
    256*Real.pi ≤ T → 128 ≤ T → ∀ (c d : ℕ → ℂ) (N : ℕ) (H : ℝ),
    1 ≤ N → (N:ℝ) ≤ T → 0 ≤ H →
    (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ H) → (∀ n ∈ Finset.Icc 1 N, ‖d n‖ ≤ H) →
    ∀ (phi : ℝ → ℂ) (P : ℝ), Continuous phi → 0 ≤ P →
      (∀ t ∈ Icc T (2*T), ‖phi t‖ ≤ P) →
    ‖∫ t in Icc T (2*T), PRZZMollifiedTime.mollifierWeight phi c d N t *
      PRZZReplacementIntegral.difference a b t‖ ≤
      C*(1+32/‖a+b‖^2)*P*H^2*T^(eps-s+1/2)*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := replacement_mean s eps hs hs' he he'
  refine ⟨10*C,by positivity,?_⟩
  intro a b ha hb hab hsa hsb T hT hT' c d N H hN hNT hH hc hd phi P hphi hP hp
  have ht : 0 < T := by linarith
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hmass : (mean c N T+mean d N T)/2 ≤ H^2*(2*T*Real.sqrt N+8*(N:ℝ)^2) := by
    linarith [bounded_mean c N T H ht.le hH hc,bounded_mean d N T H ht.le hH hd]
  have hscale := (div_le_iff₀ (Real.sqrt_pos.mpr ht)).mp (mean_scale_target N T hn hNT)
  have heq : T^(eps-s)*Real.sqrt T = T^(eps-s+1/2) := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_add ht]
  apply (h a b ha hb hab hsa hsb T hT hT' c d N phi P hphi hP hp).trans
  apply (mul_le_mul_of_nonneg_left hmass (by positivity)).trans
  have hh := mul_le_mul_of_nonneg_left hscale
    (show 0 ≤ C*(1+32/‖a+b‖^2)*T^(eps-s)*P*H^2 by positivity)
  convert hh using 1 <;> (try rw [← heq]) <;> ring

theorem scaled_target (S r delta H : ℝ) (hr : 0 < r) (hd : 0 < delta) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ∀ (c d : ℕ → ℂ) (N : ℕ), 1 ≤ N → (N:ℝ) ≤ T →
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ H) → (∀ n ∈ Finset.Icc 1 N, ‖d n‖ ≤ H) →
      ∀ (phi : ℝ → ℂ) (P : ℝ), Continuous phi → 0 ≤ P →
      (∀ t ∈ Icc T (2*T), ‖phi t‖ ≤ P) →
      ‖∫ t in Icc T (2*T), PRZZMollifiedTime.mollifierWeight phi c d N t *
        PRZZReplacementIntegral.difference (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t‖ ≤
        C*P*T^delta*PRZZOptimalPowers.target N T := by
  let eta : ℝ := min (1/8) (delta/16)
  have he : 0 < eta := lt_min (by norm_num) (by positivity)
  have he8 : eta ≤ 1/8 := min_le_left _ _
  have hed : eta ≤ delta/16 := min_le_right _ _
  obtain ⟨C,hC,h⟩ := bounded_target (1/2-eta) eta (by linarith) (by linarith) he (by linarith)
  obtain ⟨D,hD,habs⟩ := PRZZScaledReplacement.singular_absorbed r (2*eta) delta hr (by linarith)
  refine ⟨C*(H^2+1)*D,by positivity,?_⟩
  filter_upwards [PRZZScaledReplacement.shifts_eventually S eta he,
    eventually_ge_atTop (256*Real.pi),eventually_ge_atTop (128:ℝ)] with T hsmall hT hT'
  intro A B hA hB hsep c d N hN hNT hc hd' phi P hphi hP hp
  have ha := hsmall.2 A hA
  have hb := hsmall.2 B hB
  have hla := (abs_le.mp ((Complex.abs_re_le_norm (A/(Real.log T:ℂ))).trans ha)).1
  have hlb := (abs_le.mp ((Complex.abs_re_le_norm (B/(Real.log T:ℂ))).trans hb)).1
  have hab : A+B ≠ 0 := norm_pos_iff.mp (hr.trans_le hsep)
  have hL : (Real.log T:ℂ) ≠ 0 := by exact_mod_cast (show Real.log T ≠ 0 by linarith [hsmall.1])
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]; exact div_ne_zero hab hL
  have hh := h _ _ (by linarith) (by linarith) hs (by linarith) (by linarith)
    T hT hT' c d N H hN hNT hH hc hd' phi P hphi hP hp
  have hexp : eta-(1/2-eta)+1/2 = 2*eta := by ring
  rw [hexp] at hh
  have htar : 0 ≤ PRZZOptimalPowers.target N T := by unfold PRZZOptimalPowers.target; positivity
  have hz := mul_le_mul_of_nonneg_left (habs T (by linarith) hsmall.1 A B hsep)
    (show 0 ≤ C*P*H^2*PRZZOptimalPowers.target N T by positivity)
  have hz' : C*(1+32/‖A/(Real.log T:ℂ)+B/(Real.log T:ℂ)‖^2)*P*H^2*T^(2*eta)*
      PRZZOptimalPowers.target N T ≤ (C*H^2*D)*P*T^delta*PRZZOptimalPowers.target N T := by
    calc
      _ = (C*P*H^2*PRZZOptimalPowers.target N T)*
          ((1+32/‖A/(Real.log T:ℂ)+B/(Real.log T:ℂ)‖^2)*T^(2*eta)) := by ring
      _ ≤ (C*P*H^2*PRZZOptimalPowers.target N T)*(D*T^delta) := hz
      _ = _ := by ring
  apply hh.trans (hz'.trans _)
  have ht : 0 ≤ C*P*D*T^delta*PRZZOptimalPowers.target N T := by positivity
  nlinarith

/-- One constant covers the full radius-two coefficient box in both slots;
the basis and coefficients may vary with height. No 49-pair bound is assumed. -/
theorem family_target (S r delta : ℝ) (hr : 0 < r) (hd : 0 < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ∀ theta : ℝ, 0 < theta → ∀ z w : Fin 7 → ℂ,
      (∀ i, ‖z i‖ ≤ 2) → (∀ i, ‖w i‖ ≤ 2) → ∀ N : ℕ, 1 ≤ N → (N:ℝ) ≤ T →
      ∀ (phi : ℝ → ℂ) (P : ℝ), Continuous phi → 0 ≤ P →
      (∀ t ∈ Icc T (2*T), ‖phi t‖ ≤ P) →
      ‖∫ t in Icc T (2*T), PRZZMollifiedTime.mollifierWeight phi
        (PRZZCoefficientPolarization.family (PRZZWitnessBasis.basis theta T) z)
        (PRZZCoefficientPolarization.family (PRZZWitnessBasis.basis theta T) w) N t *
        PRZZReplacementIntegral.difference (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t‖ ≤
        C*P*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := scaled_target S r delta 84 hr hd (by norm_num)
  refine ⟨C,hC,?_⟩
  filter_upwards [h,eventually_ge_atTop (2:ℝ)] with T h hT
  intro A B hA hB hsep theta htheta z w hz hw N hN hNT phi P hphi hP hp
  exact h A B hA hB hsep _ _ N hN hNT
    (fun n hn => PRZZWitnessBasis.family_coefficient_bound theta T htheta hT z hz n)
    (fun n hn => PRZZWitnessBasis.family_coefficient_bound theta T htheta hT w hw n)
    phi P hphi hP hp

/-- Substitute the evaluated mixed direct replacement into the original
zeta-to-W defect equality. The noncentral residue and dual Gamma-weighted
replacement are retained explicitly, not declared small by this theorem. -/
theorem defect_bound (S r delta H : ℝ) (hr : 0 < r) (hd : 0 < delta) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ∀ (c d : ℕ → ℂ) (N : ℕ), 1 ≤ N → (N:ℝ) ≤ T →
      (∀ n ∈ Finset.Icc 1 N, ‖c n‖ ≤ H) → (∀ n ∈ Finset.Icc 1 N, ‖d n‖ ≤ H) →
      ∀ (phi : ℝ → ℂ) (P : ℝ), Continuous phi → 0 ≤ P →
      (∀ t ∈ Icc T (2*T), ‖phi t‖ ≤ P) →
      let alpha := A/(Real.log T:ℂ)
      let beta := B/(Real.log T:ℂ)
      let w := PRZZMollifiedTime.mollifierWeight phi c d N
      ‖∫ t in Icc T (2*T), w t*PRZZIntegratedDefect.defect alpha beta t‖ ≤
        C*P*T^delta*PRZZOptimalPowers.target N T+
          ‖∫ t in Icc T (2*T), w t*PRZZContourAFE.noncentralSum alpha beta t‖+
          ‖∫ t in Icc T (2*T), w t*PRZZAFEDual.dualMultiplier alpha beta t*
            PRZZReplacementIntegral.difference (-beta) (-alpha) t‖ := by
  obtain ⟨C,hC,h⟩ := scaled_target S r delta H hr hd hH
  refine ⟨C,hC,?_⟩
  filter_upwards [h,PRZZScaledReplacement.shifts_eventually S (1/4) (by norm_num),
    eventually_ge_atTop (256*Real.pi),eventually_ge_atTop (128:ℝ)] with T h hsmall hT hT'
  intro A B hA hB hsep c d N hN hNT hc hd' phi P hphi hP hp
  have hL : (Real.log T:ℂ) ≠ 0 := by exact_mod_cast (show Real.log T ≠ 0 by linarith [hsmall.1])
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]
    exact div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep)) hL
  have he := PRZZIntegratedDefect.integral_eq _ _ (hsmall.2 A hA) (hsmall.2 B hB) hs T hT hT'
    _ (PRZZMollifiedTime.mollifierWeight_continuous phi hphi c d N)
  dsimp only
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_sub_le _ _).trans (add_le_add (h A B hA hB hsep c d N hN hNT hc hd' phi P hphi hP hp) le_rfl))
    le_rfl)

#print axioms defect_bound
#print axioms family_target
#print axioms replacement_mean
#print axioms bounded_target
#print axioms scaled_target
end XiPrime8845.PRZZMixedReplacement
