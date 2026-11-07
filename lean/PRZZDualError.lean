import PRZZResidueAbsorption
import PRZZDyadicArithmeticMass

/-! The actual dual Gamma multiplier and exact two-sided W bookkeeping.
The complex-power scale is retained in the multiplier bound. -/
noncomputable section
open Complex MeasureTheory Set Filter
namespace XiPrime8845.PRZZDualError
open PRZZAFEDual
set_option maxHeartbeats 3000000

theorem multiplier_ratio (a b : ℂ) (t : ℝ) :
    dualMultiplier a b t = PRZZAFEGamma.gammaRatio a b (-(a+b)) t := by
  rw [dualMultiplier_formula]
  unfold PRZZAFEGamma.gammaRatio leftArg rightArg
  simp only [neg_neg]
  congr 3 <;> ring

/-- Small actual shifts supply the strip conditions for both Gamma factors.
This estimates the genuine quotient, not an assumed dual coefficient. -/
theorem multiplier_bound (a b : ℂ) (T t : ℝ)
    (ha : ‖a‖ ≤ 1/16) (hb : ‖b‖ ≤ 1/16) (hT : 2 ≤ T) (ht : T ≤ t) :
    ‖dualMultiplier a b t‖ ≤
      ‖((t/(2*Real.pi):ℝ):ℂ)^(-(a+b))‖*Real.exp (7/T) := by
  have hs : ‖-(a+b)‖ ≤ 1/8 := by
    rw [norm_neg]; exact (norm_add_le _ _).trans (by linarith)
  have hi := (Complex.abs_im_le_norm (-(a+b))).trans hs
  have hre := (abs_le.mp ((Complex.abs_re_le_norm (-(a+b))).trans hs)).1
  obtain ⟨E,hE,he⟩ := PRZZGammaMain.ratio_main_error_strip T t a b (-(a+b))
    hT ht (by linarith) (by linarith) (by linarith) hre
  have hcost : 2*‖-(a+b)‖*(26+‖-(a+b)‖)/T ≤ 7/T := by
    apply div_le_div_of_nonneg_right _ (by linarith)
    nlinarith [norm_nonneg (-(a+b))]
  rw [multiplier_ratio,he,norm_mul,Complex.norm_exp]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact Real.exp_le_exp.mpr ((Complex.re_le_norm E).trans (hE.trans hcost))

/-- Exact AFE defect after replacing both Gamma series by their W series.
No error estimate or equality to a post-Poisson truncation is assumed. -/
theorem two_sided_defect (a b : ℂ) (t : ℝ)
    (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4) (hs : a+b ≠ 0) (ht : 1 ≤ t) :
    riemannZeta (leftArg a t)*riemannZeta (rightArg b t) -
      ((∑' p : ℕ × ℕ, PRZZL1Finite.directTerm a b (PRZZActualDirectSum.mainWeight a b)
        t (p.1+1) (p.2+1)) + dualMultiplier a b t*
        (∑' p : ℕ × ℕ, PRZZL1Finite.directTerm (-b) (-a)
          (PRZZActualDirectSum.mainWeight (-b) (-a)) t (p.1+1) (p.2+1))) =
      PRZZReplacementIntegral.difference a b t +
        dualMultiplier a b t*PRZZReplacementIntegral.difference (-b) (-a) t -
        PRZZContourAFE.noncentralSum a b t := by
  rw [PRZZSeriesAFE.series_afe a b t ha hb hs ht]
  unfold PRZZReplacementIntegral.difference
  ring

/-- A uniform multiplier cap on the logarithmic shift family. -/
theorem multiplier_scaled_cap (S : ℝ) (hS : 0 ≤ S) :
    ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ, ‖A‖ ≤ S → ‖B‖ ≤ S →
      ∀ t ∈ Icc T (2*T),
      ‖dualMultiplier (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t‖ ≤
        Real.exp (2*S+7) := by
  filter_upwards [PRZZScaledReplacement.shifts_eventually S (1/16) (by norm_num),
    eventually_ge_atTop (2*Real.pi),eventually_ge_atTop (2:ℝ)] with T hsmall hT hT2
  intro A B hA hB t ht
  have hL : 0 < Real.log T := by linarith [hsmall.1]
  have hq : 1 ≤ t/(2*Real.pi) := (le_div_iff₀ (by positivity)).mpr (by linarith [ht.1])
  have hqT : t/(2*Real.pi) ≤ T := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [Real.pi_gt_three,ht.2]
  have hlog0 := Real.log_nonneg hq
  have hlog := Real.log_le_log (by linarith : 0 < t/(2*Real.pi)) hqT
  have hab : ‖A/(Real.log T:ℂ)+B/(Real.log T:ℂ)‖ ≤ 2*S/Real.log T := by
    rw [← add_div,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
    apply div_le_div_of_nonneg_right _ hL.le
    exact (norm_add_le _ _).trans (by linarith)
  have hp : Real.log (t/(2*Real.pi)) *
      (-(A/(Real.log T:ℂ)+B/(Real.log T:ℂ))).re ≤ 2*S := by
    calc
      _ ≤ Real.log (t/(2*Real.pi))*‖A/(Real.log T:ℂ)+B/(Real.log T:ℂ)‖ := by
        apply mul_le_mul_of_nonneg_left _ hlog0
        simpa only [norm_neg] using Complex.re_le_norm (-(A/(Real.log T:ℂ)+B/(Real.log T:ℂ)))
      _ ≤ Real.log T*(2*S/Real.log T) := mul_le_mul hlog hab (norm_nonneg _) (by positivity)
      _ = 2*S := by field_simp
  have hh := multiplier_bound _ _ T t (hsmall.2 A hA) (hsmall.2 B hB) hT2 ht.1
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < t/(2*Real.pi)),
    Real.rpow_def_of_pos (by linarith : 0 < t/(2*Real.pi)),← Real.exp_add] at hh
  apply hh.trans
  apply Real.exp_le_exp.mpr
  have h7 : 7/T ≤ (7:ℝ) := (div_le_iff₀ (by linarith)).mpr (by linarith)
  linarith

/-- Complex-power dilation after its real Jacobian has cancelled.
The cap is uniform in the spatial arithmetic variable v <= T. -/
theorem dilation_cap (S T v : ℝ) (A B : ℂ) (hS : 0 ≤ S)
    (hT : 1 < T) (hv : 1 ≤ v) (hvT : v ≤ T)
    (hA : ‖A‖ ≤ S) (hB : ‖B‖ ≤ S) :
    ‖Complex.exp (((A+B)/(Real.log T:ℂ))*(Real.log v:ℂ))‖ ≤ Real.exp (2*S) := by
  have hL : 0 < Real.log T := Real.log_pos hT
  have hlv : 0 ≤ Real.log v := Real.log_nonneg hv
  have hlT : Real.log v ≤ Real.log T := Real.log_le_log (by linarith) hvT
  have hab : ‖(A+B)/(Real.log T:ℂ)‖ ≤ 2*S/Real.log T := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
    apply div_le_div_of_nonneg_right _ hL.le
    exact (norm_add_le _ _).trans (by linarith)
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  apply (Complex.re_le_norm _).trans
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hlv]
  calc
    _ ≤ (2*S/Real.log T)*Real.log T := mul_le_mul hab hlT hlv (by positivity)
    _ = _ := by field_simp

/-- The actual dual Gamma quotient and the post-Jacobian power factor
are jointly bounded, uniformly over the logarithmic shift family. -/
theorem multiplier_dilation_cap (S : ℝ) (hS : 0 ≤ S) :
    ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ, ‖A‖ ≤ S → ‖B‖ ≤ S →
      ∀ t ∈ Icc T (2*T), ∀ v : ℝ, 1 ≤ v → v ≤ T →
      ‖dualMultiplier (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t *
        Complex.exp (((A+B)/(Real.log T:ℂ))*(Real.log v:ℂ))‖ ≤
          Real.exp (4*S+7) := by
  filter_upwards [multiplier_scaled_cap S hS,eventually_ge_atTop (2:ℝ)] with T h hT
  intro A B hA hB t ht v hv hvT
  rw [norm_mul]
  exact (mul_le_mul (h A B hA hB t ht)
    (dilation_cap S T v A B hS (by linarith) hv hvT hA hB)
    (norm_nonneg _) (Real.exp_pos _).le).trans_eq (by rw [← Real.exp_add]; congr 1; ring)

/-- Insert the genuine Gamma/power factor and both scaled cutoffs into
the restricted reduced-pair mass. No analytic envelope or pair-cardinality
premise remains. Coefficients here are a(u),a(v), not a(d*u),a(d*v). -/
theorem dual_power_pair_mass (F G : ℝ → ℂ)
    (hF : Continuous F) (hG : Continuous G)
    (hsF : HasCompactSupport F) (hsG : HasCompactSupport G)
    (S : ℝ) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (A B : ℂ), ‖A‖ ≤ S → ‖B‖ ≤ S →
      ∀ (js : List ℕ) (N j l : ℕ) (Q R d t : ℝ) (s : Finset (ℕ × ℕ)),
      1 ≤ N → (N:ℝ) ≤ T → t ∈ Icc T (2*T) →
      s ⊆ (PRZZDyadic.cell N j) ×ˢ (PRZZDyadic.cell N l) →
      (∑ p ∈ s, ‖(((PRZZGCoefficient.coefficient js p.1:ℂ)*
        star (PRZZGCoefficient.coefficient js p.2:ℂ))*
        (F (Q⁻¹*(d*p.1))*G (R⁻¹*(d*p.2))*
          (dualMultiplier (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t *
            Complex.exp (((A+B)/(Real.log T:ℂ))*(Real.log (p.2:ℝ):ℂ))))) /
          ((p.1:ℂ)*(p.2:ℂ))‖) ≤ (Real.log N)^(2*PRZZGCoefficient.degree js)*C := by
  obtain ⟨CF,hCF⟩ := hsF.exists_bound_of_continuous hF
  obtain ⟨CG,hCG⟩ := hsG.exists_bound_of_continuous hG
  have hf0 : 0 ≤ CF := (norm_nonneg _).trans (hCF 0)
  have hg0 : 0 ≤ CG := (norm_nonneg _).trans (hCG 0)
  refine ⟨CF*CG*Real.exp (4*S+7),by positivity,?_⟩
  filter_upwards [multiplier_dilation_cap S hS] with T hcap
  intro A B hA hB js N j l Q R d t s hN hNT ht hs
  apply PRZZDyadicArithmeticMass.weighted_pair_mass js N j l hN s hs _ _ (by positivity)
  intro p hp
  have hm := (PRZZDyadic.mem_cell N l p.2).mp (Finset.mem_product.mp (hs hp)).2
  have hm' := Finset.mem_Icc.mp hm.1
  have hv : (1:ℝ) ≤ p.2 := by exact_mod_cast hm'.1
  have hvT : (p.2:ℝ) ≤ T := (by exact_mod_cast hm'.2 : (p.2:ℝ) ≤ N).trans hNT
  rw [norm_mul,norm_mul]
  exact mul_le_mul (mul_le_mul (hCF _) (hCG _) (norm_nonneg _) hf0)
    (hcap A B hA hB t ht p.2 hv hvT) (norm_nonneg _) (mul_nonneg hf0 hg0)

/-- The reflected replacement theorem is applied to the actual continuous
time weight phi times the Gamma multiplier, with its cap supplied above. -/
theorem dual_scaled_target (js : List ℕ) (S r delta : ℝ)
    (hS : 0 ≤ S) (hr : 0 < r) (hd : 0 < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ → ∀ N : ℕ, 1 ≤ N → (N:ℝ) ≤ T →
      ∀ (phi : ℝ → ℂ) (P : ℝ), Continuous phi → 0 ≤ P →
      (∀ t ∈ Icc T (2*T), ‖phi t‖ ≤ P) →
      ‖∫ t in Icc T (2*T), PRZZMollifiedTime.mollifierWeight phi
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) N t *
        dualMultiplier (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t *
        PRZZReplacementIntegral.difference (-(B/(Real.log T:ℂ))) (-(A/(Real.log T:ℂ))) t‖ ≤
          C*P*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := PRZZScaledReplacement.scaled_target js S r delta hr hd
  refine ⟨C*Real.exp (2*S+7),by positivity,?_⟩
  filter_upwards [h,multiplier_scaled_cap S hS,
    PRZZScaledReplacement.shifts_eventually S (1/16) (by norm_num)] with T h hcap hsmall
  intro A B hA hB hsep N hN hNT phi P hphi hP hp
  have ha := abs_le.mp ((Complex.abs_re_le_norm _).trans (hsmall.2 A hA))
  have hb := abs_le.mp ((Complex.abs_re_le_norm _).trans (hsmall.2 B hB))
  have hc := PRZZMollifiedTime.dualMultiplier_continuous (A/(Real.log T:ℂ))
    (B/(Real.log T:ℂ)) (by linarith [ha.1]) (by linarith [ha.2])
    (by linarith [hb.1]) (by linarith [hb.2])
  have hs : r ≤ ‖-B + -A‖ := by
    rw [show -B + -A = -(A+B) by ring,norm_neg]; exact hsep
  have hh := h (-B) (-A) (by simpa using hB) (by simpa using hA) hs N hN hNT
    (fun t => phi t*dualMultiplier (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t)
    (P*Real.exp (2*S+7)) (hphi.mul hc) (by positivity)
    (fun t ht => by rw [norm_mul]; exact mul_le_mul (hp t ht) (hcap A B hA hB t ht) (norm_nonneg _) hP)
  convert hh using 1
  · congr 1
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    simp only [neg_div,PRZZMollifiedTime.mollifierWeight]
    ring
  · ring

/-- Both replacement integrals and the full noncentral residue integral
share one sharp target. Phase expansion and Fourier tails are separate. -/
theorem replacement_residue_target (js : List ℕ) (S r delta : ℝ)
    (hS : 0 ≤ S) (hr : 0 < r) (hd : 0 < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ → ∀ N : ℕ, 1 ≤ N → (N:ℝ) ≤ T →
      ∀ (phi : ℝ → ℂ) (P : ℝ), Continuous phi → 0 ≤ P →
      (∀ t ∈ Icc T (2*T), ‖phi t‖ ≤ P) →
      let a := A/(Real.log T:ℂ)
      let b := B/(Real.log T:ℂ)
      let w := PRZZMollifiedTime.mollifierWeight phi
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) N
      ‖((∫ t in Icc T (2*T), w t*PRZZReplacementIntegral.difference a b t) -
        (∫ t in Icc T (2*T), w t*PRZZContourAFE.noncentralSum a b t)) +
        (∫ t in Icc T (2*T), w t*dualMultiplier a b t*
          PRZZReplacementIntegral.difference (-b) (-a) t)‖ ≤
        C*P*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,hc⟩ := PRZZResidueAbsorption.combined_target js S r delta hr hd
  obtain ⟨D,hD,hd'⟩ := dual_scaled_target js S r delta hS hr hd
  refine ⟨C+D,by positivity,?_⟩
  filter_upwards [hc,hd'] with T hc hd'
  intro A B hA hB hsep N hN hNT phi P hphi hP hp
  apply (norm_add_le _ _).trans
  exact (add_le_add (hc A B hA hB hsep N hN hNT phi P hphi hP hp)
    (hd' A B hA hB hsep N hN hNT phi P hphi hP hp)).trans_eq (by ring)

/-- Original d-dilated convolution coefficients with the actual Gamma,
power and cutoff factors. All original length masks are retained. -/
theorem dual_dilated_pair_mass (F G : ℝ → ℂ)
    (hF : Continuous F) (hG : Continuous G)
    (hsF : HasCompactSupport F) (hsG : HasCompactSupport G)
    (S : ℝ) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (A B : ℂ), ‖A‖ ≤ S → ‖B‖ ≤ S →
      ∀ (js : List ℕ) (N d j l : ℕ) (Q R t : ℝ) (s : Finset (ℕ × ℕ)),
      1 ≤ N → 1 ≤ d → (N:ℝ) ≤ T → t ∈ Icc T (2*T) →
      s ⊆ (PRZZDyadic.cell N j) ×ˢ (PRZZDyadic.cell N l) →
      (∀ p ∈ s, d*p.1 ≤ N ∧ d*p.2 ≤ N) →
      (∑ p ∈ s, ‖(((PRZZGCoefficient.coefficient js (d*p.1):ℂ)*
        star (PRZZGCoefficient.coefficient js (d*p.2):ℂ))*
        (F (Q⁻¹*((d:ℝ)*p.1))*G (R⁻¹*((d:ℝ)*p.2))*
          (dualMultiplier (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t *
            Complex.exp (((A+B)/(Real.log T:ℂ))*(Real.log (p.2:ℝ):ℂ))))) /
          ((p.1:ℂ)*(p.2:ℂ))‖) ≤ (Real.log N)^(2*PRZZGCoefficient.degree js)*C := by
  obtain ⟨CF,hCF⟩ := hsF.exists_bound_of_continuous hF
  obtain ⟨CG,hCG⟩ := hsG.exists_bound_of_continuous hG
  have hf0 : 0 ≤ CF := (norm_nonneg _).trans (hCF 0)
  have hg0 : 0 ≤ CG := (norm_nonneg _).trans (hCG 0)
  refine ⟨CF*CG*Real.exp (4*S+7),by positivity,?_⟩
  filter_upwards [multiplier_dilation_cap S hS] with T hcap
  intro A B hA hB js N d j l Q R t s hN hd hNT ht hs hlen
  apply PRZZDyadicArithmeticMass.dilated_weighted_pair_mass js N d j l hN hd s hs hlen _ _ (by positivity)
  intro p hp
  have hm := (PRZZDyadic.mem_cell N l p.2).mp (Finset.mem_product.mp (hs hp)).2
  have hm' := Finset.mem_Icc.mp hm.1
  have hv : (1:ℝ) ≤ p.2 := by exact_mod_cast hm'.1
  have hvT : (p.2:ℝ) ≤ T := (by exact_mod_cast hm'.2 : (p.2:ℝ) ≤ N).trans hNT
  rw [norm_mul,norm_mul]
  exact mul_le_mul (mul_le_mul (hCF _) (hCG _) (norm_nonneg _) hf0)
    (hcap A B hA hB t ht p.2 hv hvT) (norm_nonneg _) (mul_nonneg hf0 hg0)

#print axioms dual_dilated_pair_mass
#print axioms replacement_residue_target
#print axioms dilation_cap
#print axioms multiplier_dilation_cap
#print axioms dual_power_pair_mass
#print axioms multiplier_scaled_cap
#print axioms dual_scaled_target
#print axioms multiplier_ratio
#print axioms multiplier_bound
#print axioms two_sided_defect
end XiPrime8845.PRZZDualError
