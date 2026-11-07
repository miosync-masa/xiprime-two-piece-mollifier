import PRZZDifferenceRegular
import PRZZGammaUniform
import PRZZHorizontalDecay

/-! Gaussian tails of the actual regularized V-W kernel on [-1/8,2].
Constants may depend on the fixed time, shifts and positive scales. This
is a contour-limit estimate, not a height-uniform comparison estimate. -/
noncomputable section
open Complex Set Filter Topology MeasureTheory
namespace XiPrime8845.PRZZDifferenceDecay
open PRZZDifferenceRegular PRZZAFEGamma PRZZDyadicEnvelope
set_option maxHeartbeats 3000000

theorem power_bound (y : ℝ) (hy : 0 < y) (s : ℂ) (hs : |s.re| ≤ 2) :
    ‖(y:ℂ)^s‖ ≤ Real.exp (2*|Real.log y|) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hy,Real.rpow_def_of_pos hy]
  apply Real.exp_le_exp.mpr
  calc
    Real.log y*s.re ≤ |Real.log y*s.re| := le_abs_self _
    _ = |Real.log y| * |s.re| := abs_mul _ _
    _ ≤ |Real.log y| * 2 := mul_le_mul_of_nonneg_left hs (abs_nonneg _)
    _ = _ := by ring

theorem gamma_cap : ∃ C : ℝ, 0 < C ∧ ∀ r ∈ Icc (1/16:ℝ) 2, Real.Gamma r ≤ C := by
  have hc : ContinuousOn (fun r : ℝ => Gamma (r:ℂ)) (Icc (1/16:ℝ) 2) := by
    intro r hr
    exact ((PRZZGammaPath.gamma_analytic (r:ℂ) (by simpa using
      (show 0 < r by linarith [hr.1]))).continuousAt.comp
        (x := r) Complex.continuous_ofReal.continuousAt).continuousWithinAt
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max C 0+1,by positivity,?_⟩
  intro r hr
  have he : Real.Gamma r ≤ ‖Gamma (r:ℂ)‖ := Complex.re_le_norm _
  exact he.trans ((hC r hr).trans (by linarith [le_max_left C 0]))

theorem ratio_strip_bound (a b : ℂ) (t : ℝ) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re ∈ Icc (-1/8:ℝ) 2 →
      ‖gammaRatio a b s t‖ ≤ C := by
  obtain ⟨G,hG,hcap⟩ := gamma_cap
  let D := ‖Gamma ((1/2+a+(t:ℂ)*I)/2)*Gamma ((1/2+b-(t:ℂ)*I)/2)‖
  let P := Real.exp (2*|Real.log Real.pi|)
  refine ⟨P*G*G/D+1,by dsimp [P,D]; positivity,?_⟩
  intro s hs
  have ar := abs_le.mp ((abs_re_le_norm a).trans ha)
  have br := abs_le.mp ((abs_re_le_norm b).trans hb)
  have hA : ((1/2+a+s+(t:ℂ)*I)/2).re ∈ Icc (1/16:ℝ) 2 := by
    simp only [div_ofNat_re,add_re,mul_re,ofReal_re,ofReal_im,I_re,I_im,
      mul_zero,zero_mul,sub_self,add_zero]
    norm_num; constructor <;> linarith [hs.1,hs.2]
  have hB : ((1/2+b+s-(t:ℂ)*I)/2).re ∈ Icc (1/16:ℝ) 2 := by
    simp only [div_ofNat_re,add_re,sub_re,mul_re,ofReal_re,ofReal_im,I_re,I_im,
      mul_zero,zero_mul,sub_self,sub_zero]
    norm_num; constructor <;> linarith [hs.1,hs.2]
  have hga := (PRZZGammaFar.gamma_norm_le _ (by linarith [hA.1])).trans (hcap _ hA)
  have hgb := (PRZZGammaFar.gamma_norm_le _ (by linarith [hB.1])).trans (hcap _ hB)
  have hpi := power_bound Real.pi Real.pi_pos (-s) (by
    simpa using (abs_le.mpr (show -2 ≤ s.re ∧ s.re ≤ 2 by constructor <;> linarith [hs.1,hs.2])))
  unfold gammaRatio
  rw [norm_div,norm_mul,norm_mul]
  change _ ≤ P*G*G/D+1
  have hh : ‖(Real.pi:ℂ)^(-s)‖*(‖Gamma ((1/2+a+s+(t:ℂ)*I)/2)‖*
      ‖Gamma ((1/2+b+s-(t:ℂ)*I)/2)‖)/D ≤ P*G*G/D := by
    dsimp [P]
    calc
      _ ≤ Real.exp (2*|Real.log Real.pi|)*(G*G)/D := by gcongr
      _ = _ := by ring
  linarith

theorem tail_bound (a b : ℂ) (x t q : ℝ)
    (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4) (hsigma : a+b ≠ 0)
    (hx : 0 < x) (hq : 0 < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, s.re ∈ Icc (-1/8:ℝ) 2 → 1 ≤ |s.im| →
      ‖regular a b x t q s‖ ≤ C*(|s.im|+1)^4*Real.exp (-|s.im|^2) := by
  obtain ⟨G,hG,hgamma⟩ := ratio_strip_bound a b t ha hb
  let P := Real.exp (2*|Real.log x|)
  let Q := Real.exp (2*|Real.log q|)
  let C := P*Real.exp 4*(1+16/‖a+b‖^2)*(G+Q)
  refine ⟨C,by dsimp [C,P,Q]; positivity,?_⟩
  intro s hs hv
  have hsr : |s.re| ≤ 2 := abs_le.mpr ⟨by linarith [hs.1],hs.2⟩
  have hsn : ‖s‖ ≤ 2*(|s.im|+1) := by
    have := norm_le_abs_re_add_abs_im s
    linarith [abs_nonneg s.im]
  have hn0 : s ≠ 0 := by intro he; norm_num [he] at hv
  have hinv : ‖s⁻¹‖ ≤ 1 := by
    rw [norm_inv]; exact inv_le_one_of_one_le₀ (hv.trans (abs_im_le_norm s))
  have hpow : (1:ℝ) ≤ (|s.im|+1)^2 := by nlinarith [abs_nonneg s.im]
  have han := annihilator_bound (a+b) s 1 ‖a+b‖
    (by norm_num) (norm_pos_iff.mpr hsigma) (by simp)
  have han' : ‖annihilator (a+b) s‖ ≤ (1+16/‖a+b‖^2)*(|s.im|+1)^2 := by
    apply han.trans
    rw [div_pow,one_pow]
    simp only [mul_one_div]
    calc
      _ ≤ 1+4*(2*(|s.im|+1))^2/‖a+b‖^2 := by gcongr
      _ ≤ _ := by
        calc
          _ = 1+(16/‖a+b‖^2)*(|s.im|+1)^2 := by ring
          _ ≤ (|s.im|+1)^2+(16/‖a+b‖^2)*(|s.im|+1)^2 := add_le_add hpow le_rfl
          _ = _ := by ring
  have he : ‖exp (s^2)‖ ≤ Real.exp 4*Real.exp (-|s.im|^2) := by
    rw [norm_exp,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    simp only [pow_two,mul_re]
    have hh := abs_le.mp hsr
    nlinarith [sq_abs s.im]
  have hnum : ‖numerator a b t q s‖ ≤ G+Q :=
    (norm_sub_le _ _).trans (add_le_add (hgamma s hs) (power_bound q hq s hsr))
  have hp := power_bound x hx (-s) (by simpa using hsr)
  have ar := (abs_le.mp ((abs_re_le_norm a).trans ha)).1
  have br := (abs_le.mp ((abs_re_le_norm b).trans hb)).1
  rw [regular_eq a b s x t q (by linarith) (by linarith) hn0,div_eq_mul_inv]
  simp only [norm_mul]
  calc
    _ ≤ P*(Real.exp 4*Real.exp (-|s.im|^2))*
        ((1+16/‖a+b‖^2)*(|s.im|+1)^2)*1*(G+Q) := by gcongr
    _ = C*(|s.im|+1)^2*Real.exp (-|s.im|^2) := by dsimp [C]; ring
    _ ≤ _ := by gcongr <;> norm_num

#print axioms power_bound
#print axioms gamma_cap
#print axioms ratio_strip_bound
#print axioms tail_bound
end XiPrime8845.PRZZDifferenceDecay
