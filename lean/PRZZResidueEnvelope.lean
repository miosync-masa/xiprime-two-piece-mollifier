import PRZZCompletedStrip
import PRZZNoncentralResidues
import PRZZGammaUniform

/-! Combining the actual residue factors. All shift singularities remain
explicit; no contour displacement or Poisson identification is asserted. -/
noncomputable section
open Complex Set
namespace XiPrime8845.PRZZResidueEnvelope
open PRZZAFEDual PRZZNoncentralResidues PRZZDyadicEnvelope
set_option maxHeartbeats 3000000

theorem inverse_gammaR_uniform : ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
    1/4 ≤ z.re → z.re ≤ 3/4 →
    ‖(Gammaℝ z)⁻¹‖ ≤ C*Real.exp (Real.pi*|z.im|) := by
  obtain ⟨C,hC,h⟩ := PRZZGammaUniform.real_gamma_cap
  refine ⟨C,hC,?_⟩
  intro z hl hu
  have hg := PRZZGammaFar.gamma_inv_bound (z/2) (by simp; linarith) (by simp; linarith)
  have hc := h (1-(z/2).re) ⟨by simp; linarith,by simp; linarith⟩
  have hp : ‖((Real.pi:ℂ)^(-z/2))⁻¹‖ ≤ Real.pi := by
    rw [norm_inv,norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have he : (-z/2).re = -(z.re/2) := by simp; ring
    rw [he,Real.rpow_neg Real.pi_pos.le,inv_inv]
    simpa using Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three] : 1 ≤ Real.pi)
      (show z.re/2 ≤ 1 by linarith)
  have he : Real.exp (Real.pi*|(z/2).im|) ≤ Real.exp (Real.pi*|z.im|) := by
    apply Real.exp_le_exp.mpr
    simp only [div_ofNat_im,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    nlinarith [abs_nonneg z.im,Real.pi_pos]
  rw [Gammaℝ_def,mul_inv,norm_mul]
  apply (mul_le_mul hp hg (norm_nonneg _) Real.pi_pos.le).trans
  calc
    _ ≤ Real.pi*(C*Real.exp (Real.pi*|z.im|)/Real.pi) := by gcongr
    _ = _ := by field_simp

theorem inverse_pair_uniform : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℂ,
    ‖a‖ ≤ 1/4 → ‖b‖ ≤ 1/4 → ∀ t : ℝ, 0 ≤ t →
    ‖(gammaPair a b t)⁻¹‖ ≤ C*Real.exp (2*Real.pi*t) := by
  obtain ⟨C,hC,h⟩ := inverse_gammaR_uniform
  refine ⟨C*C*Real.exp (Real.pi/2),by positivity,?_⟩
  intro a b ha hb t ht
  have har := abs_le.mp ((abs_re_le_norm a).trans ha)
  have hbr := abs_le.mp ((abs_re_le_norm b).trans hb)
  have hai := (abs_im_le_norm a).trans ha
  have hbi := (abs_im_le_norm b).trans hb
  have h1 := h (leftArg a t) (by simp [leftArg]; linarith) (by simp [leftArg]; linarith)
  have h2 := h (rightArg b t) (by simp [rightArg]; linarith) (by simp [rightArg]; linarith)
  have hi1 : |(leftArg a t).im| ≤ t+1/4 := by
    simp only [leftArg,add_im,div_ofNat_im,one_im,zero_div,mul_im,ofReal_re,I_im,
      ofReal_im,I_re,mul_one,mul_zero,add_zero,zero_add]
    have hh := abs_add_le a.im t
    rw [abs_of_nonneg ht] at hh
    linarith
  have hi2 : |(rightArg b t).im| ≤ t+1/4 := by
    simp only [rightArg,sub_im,add_im,div_ofNat_im,one_im,zero_div,mul_im,ofReal_re,I_im,
      ofReal_im,I_re,mul_one,mul_zero,add_zero,zero_add]
    have hh := abs_add_le b.im (-t)
    rw [abs_neg,abs_of_nonneg ht] at hh
    rw [← sub_eq_add_neg] at hh
    linarith
  rw [gammaPair,mul_inv,norm_mul]
  apply (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)).trans
  calc
    _ ≤ (C*Real.exp (Real.pi*(t+1/4)))*(C*Real.exp (Real.pi*(t+1/4))) := by gcongr
    _ = _ := by
      have he : Real.exp (Real.pi*(t+1/4))*Real.exp (Real.pi*(t+1/4)) =
          Real.exp (Real.pi/2)*Real.exp (2*Real.pi*t) := by
        rw [← Real.exp_add,← Real.exp_add]
        congr 1
        ring
      calc
        _ = C*C*(Real.exp (Real.pi*(t+1/4))*Real.exp (Real.pi*(t+1/4))) := by ring
        _ = _ := by rw [he]; ring

/-- Composition with all analytic estimates supplied; the remaining
premises describe the pole location and regular-factor argument only. -/
theorem residue_envelope : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℂ,
    ‖a‖ ≤ 1/4 → ‖b‖ ≤ 1/4 → a+b ≠ 0 → ∀ t : ℝ, 1 ≤ t → ∀ p u : ℂ,
    |p.re| ≤ 1 → t-1/4 ≤ |p.im| → 1/4 ≤ ‖p‖ → ‖p‖ ≤ t+2 →
    -9 ≤ u.re → u.re ≤ 10 → 1 ≤ |u.im| → ‖u‖ ≤ 2*t+3 →
    ‖weight (a+b) (gammaPair a b t) p * completedRiemannZeta u‖ ≤
      C*(1+4*(t+2)^2/‖a+b‖^2)*(228+96*t)*
        Real.exp (1-t^2/2+2*Real.pi*t) := by
  obtain ⟨C,hC,h⟩ := inverse_pair_uniform
  refine ⟨4*C,by positivity,?_⟩
  intro a b ha hb hs t ht p u hpr hpi hpn hpN hul huh hui huN
  have hg := h a b ha hb t (by linarith)
  have hz := PRZZCompletedStrip.strip_bound u hul huh hui
  have hz' : ‖completedRiemannZeta u‖ ≤ 228+96*t := by linarith
  have hp0 : 0 < ‖p‖ := by linarith
  have hip : ‖p⁻¹‖ ≤ 4 := by
    rw [norm_inv]
    have hh := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1/4) hpn
    simpa [one_div] using hh
  have he : ‖exp (p^2)‖ ≤ Real.exp (1-t^2/2) := by
    rw [norm_exp]
    apply Real.exp_le_exp.mpr
    have hre := abs_le.mp hpr
    have hsq : t^2/2 ≤ p.im^2 := by nlinarith [sq_abs p.im,sq_nonneg (t-1)]
    simp only [pow_two,mul_re]
    nlinarith [sq_nonneg p.re]
  have hn := annihilator_bound (a+b) p 1 ‖a+b‖ (by norm_num) (norm_pos_iff.mpr hs) (by simp)
  have hn' : ‖annihilator (a+b) p‖ ≤ 1+4*(t+2)^2/‖a+b‖^2 := by
    apply hn.trans
    rw [div_pow,one_pow]
    simp only [mul_one_div]
    gcongr
  have hw : weight (a+b) (gammaPair a b t) p * completedRiemannZeta u =
      exp (p^2)*annihilator (a+b) p*(gammaPair a b t)⁻¹*p⁻¹*completedRiemannZeta u := by
    unfold weight; ring
  rw [hw]
  simp only [norm_mul]
  calc
    _ ≤ Real.exp (1-t^2/2)*(1+4*(t+2)^2/‖a+b‖^2)*
        (C*Real.exp (2*Real.pi*t))*4*(228+96*t) := by
      gcongr
    _ = _ := by rw [show 1-t^2/2+2*Real.pi*t = (1-t^2/2)+(2*Real.pi*t) by ring,Real.exp_add]; ring

/-- Both actual left-factor residues, including Gamma denominator,
annihilator, Gaussian and the remaining completed-zeta factor. -/
theorem actual_left_residues : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℂ,
    ‖a‖ ≤ 1/4 → ‖b‖ ≤ 1/4 → a+b ≠ 0 → ∀ t : ℝ, 1 ≤ t → ∀ p : ℂ,
    (p = -leftArg a t ∨ p = 1-leftArg a t) →
    ‖weight (a+b) (gammaPair a b t) p * completedRiemannZeta (rightArg b t+p)‖ ≤
      C*(1+4*(t+2)^2/‖a+b‖^2)*(228+96*t)*Real.exp (1-t^2/2+2*Real.pi*t) := by
  obtain ⟨C,hC,h⟩ := residue_envelope
  refine ⟨C,hC,?_⟩
  intro a b ha hb hs t ht p hp
  have har := abs_le.mp ((abs_re_le_norm a).trans ha)
  have hbr := abs_le.mp ((abs_re_le_norm b).trans hb)
  have hai := abs_le.mp ((abs_im_le_norm a).trans ha)
  have hbi := abs_le.mp ((abs_im_le_norm b).trans hb)
  have hz : ‖leftArg a t‖ ≤ t+1 := by
    have hh := (norm_add_le ((1/2:ℂ)+a) ((t:ℂ)*I)).trans
      (add_le_add (norm_add_le (1/2:ℂ) a) le_rfl)
    simp [leftArg,abs_of_nonneg (by linarith : 0 ≤ t)] at *
    linarith
  have hw : ‖rightArg b t‖ ≤ t+1 := by
    have hh := (norm_sub_le ((1/2:ℂ)+b) ((t:ℂ)*I)).trans
      (add_le_add (norm_add_le (1/2:ℂ) b) le_rfl)
    simp [rightArg,abs_of_nonneg (by linarith : 0 ≤ t)] at *
    linarith
  have hpRe : |p.re| ≤ 1 ∧ 1/4 ≤ |p.re| := by
    rcases hp with rfl | rfl <;> simp only [leftArg,neg_re,sub_re,add_re,
      div_ofNat_re,one_re,mul_re,ofReal_re,I_re,ofReal_im,I_im,mul_zero,zero_mul,sub_self,add_zero]
    · rw [abs_neg,abs_of_nonneg (by linarith : 0 ≤ 1/2+a.re)]; constructor <;> linarith
    · rw [abs_of_nonneg (by linarith : 0 ≤ 1-(1/2+a.re))]; constructor <;> linarith
  have hpIm : p.im = -(a.im+t) := by
    rcases hp with rfl | rfl <;> simp [leftArg]
  have hpN : ‖p‖ ≤ t+2 := by
    rcases hp with rfl | rfl
    · simpa only [norm_neg] using hz.trans (by linarith : t+1 ≤ t+2)
    · have hh := norm_sub_le (1:ℂ) (leftArg a t)
      norm_num only [norm_one] at hh
      linarith
  refine h a b ha hb hs t ht p (rightArg b t+p) hpRe.1 ?_
    (hpRe.2.trans (abs_re_le_norm p)) hpN ?_ ?_ ?_ ?_
  · rw [hpIm,abs_neg]
    have hh := le_abs_self (a.im+t)
    linarith
  · rcases hp with rfl | rfl <;> simp [leftArg,rightArg] <;> linarith
  · rcases hp with rfl | rfl <;> simp [leftArg,rightArg] <;> linarith
  · simp only [add_im,hpIm,rightArg,sub_im,add_im,div_ofNat_im,one_im,zero_div,
      mul_im,ofReal_re,I_im,ofReal_im,I_re,mul_one,mul_zero,add_zero,zero_add]
    have hh := neg_le_abs (b.im-t+-(a.im+t))
    linarith
  · exact (norm_add_le _ _).trans (by linarith)

/-- The two right-factor poles have the opposite imaginary direction.
All geometric premises of the common analytic envelope are supplied. -/
theorem actual_right_residues : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℂ,
    ‖a‖ ≤ 1/4 → ‖b‖ ≤ 1/4 → a+b ≠ 0 → ∀ t : ℝ, 1 ≤ t → ∀ p : ℂ,
    (p = -rightArg b t ∨ p = 1-rightArg b t) →
    ‖weight (a+b) (gammaPair a b t) p * completedRiemannZeta (leftArg a t+p)‖ ≤
      C*(1+4*(t+2)^2/‖a+b‖^2)*(228+96*t)*Real.exp (1-t^2/2+2*Real.pi*t) := by
  obtain ⟨C,hC,h⟩ := residue_envelope
  refine ⟨C,hC,?_⟩
  intro a b ha hb hs t ht p hp
  have har := abs_le.mp ((abs_re_le_norm a).trans ha)
  have hbr := abs_le.mp ((abs_re_le_norm b).trans hb)
  have hai := abs_le.mp ((abs_im_le_norm a).trans ha)
  have hbi := abs_le.mp ((abs_im_le_norm b).trans hb)
  have hz : ‖rightArg b t‖ ≤ t+1 := by
    have hh := (norm_sub_le ((1/2:ℂ)+b) ((t:ℂ)*I)).trans
      (add_le_add (norm_add_le (1/2:ℂ) b) le_rfl)
    simp [rightArg,abs_of_nonneg (by linarith : 0 ≤ t)] at *
    linarith
  have hw : ‖leftArg a t‖ ≤ t+1 := by
    have hh := (norm_add_le ((1/2:ℂ)+a) ((t:ℂ)*I)).trans
      (add_le_add (norm_add_le (1/2:ℂ) a) le_rfl)
    simp [leftArg,abs_of_nonneg (by linarith : 0 ≤ t)] at *
    linarith
  have hpRe : |p.re| ≤ 1 ∧ 1/4 ≤ |p.re| := by
    rcases hp with rfl | rfl <;> simp only [rightArg,neg_re,sub_re,add_re,
      div_ofNat_re,one_re,mul_re,ofReal_re,I_re,ofReal_im,I_im,mul_zero,zero_mul,sub_self,sub_zero]
    · rw [abs_neg,abs_of_nonneg (by linarith : 0 ≤ 1/2+b.re)]; constructor <;> linarith
    · rw [abs_of_nonneg (by linarith : 0 ≤ 1-(1/2+b.re))]; constructor <;> linarith
  have hpIm : p.im = -(b.im-t) := by
    rcases hp with rfl | rfl <;> simp [rightArg]
  have hpN : ‖p‖ ≤ t+2 := by
    rcases hp with rfl | rfl
    · simpa only [norm_neg] using hz.trans (by linarith : t+1 ≤ t+2)
    · have hh := norm_sub_le (1:ℂ) (rightArg b t)
      norm_num only [norm_one] at hh
      linarith
  refine h a b ha hb hs t ht p (leftArg a t+p) hpRe.1 ?_
    (hpRe.2.trans (abs_re_le_norm p)) hpN ?_ ?_ ?_ ?_
  · rw [hpIm,abs_neg]
    have hh := neg_le_abs (b.im-t)
    linarith
  · rcases hp with rfl | rfl <;> simp [leftArg,rightArg] <;> linarith
  · rcases hp with rfl | rfl <;> simp [leftArg,rightArg] <;> linarith
  · simp only [add_im,hpIm,leftArg,add_im,div_ofNat_im,one_im,zero_div,
      mul_im,ofReal_re,I_im,ofReal_im,I_re,mul_one,mul_zero,add_zero,zero_add]
    have hh := le_abs_self (a.im+t+-(b.im-t))
    linarith
  · exact (norm_add_le _ _).trans (by linarith)

#print axioms actual_right_residues
#print axioms actual_left_residues
#print axioms residue_envelope
#print axioms inverse_gammaR_uniform
#print axioms inverse_pair_uniform
end XiPrime8845.PRZZResidueEnvelope
