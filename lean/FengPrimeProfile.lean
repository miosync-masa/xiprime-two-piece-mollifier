import FengOutsideProfile
import Zeta23.XiPrime.Coeff.PrimeSums

/-! Uniform Mertens transfer for the actual finite prime-power measure.
The inner coprime Mobius sum has already been replaced by its main profile
in this module; that replacement is a separate arithmetic obligation. -/
noncomputable section
open scoped BigOperators
open Finset Filter Topology MeasureTheory
namespace XiPrime8845.FengPrimeProfile
open Zeta23.XiPrime WeightDerivatives
set_option maxHeartbeats 1000000

theorem complex_mertens_bound (y M D : ℝ) (hy : 0 ≤ y)
    (f f' : ℝ → ℂ) (hf : ∀ t, HasDerivAt f (f' t) t) (hc : Continuous f')
    (hM : ‖f y‖ ≤ M) (hD : ∀ t ∈ Set.Icc 0 y, ‖f' t‖ ≤ D) :
    ‖(∑ n ∈ Ioc 0 ⌊Real.exp y⌋₊, (ArithmeticFunction.vonMangoldt n / n : ℝ) •
      f (Real.log n)) - ∫ t in 0..y, f t‖ ≤ 2*KM*(M+y*D) := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun t => (hf t).continuousAt)
  have hproj (c : ℂ →L[ℝ] ℝ) (hb : ∀ z, |c z| ≤ ‖z‖) :
      |c ((∑ n ∈ Ioc 0 ⌊Real.exp y⌋₊, (ArithmeticFunction.vonMangoldt n / n : ℝ) •
        f (Real.log n)) - ∫ t in 0..y, f t)| ≤ KM*(M+y*D) := by
    have hd (t : ℝ) : HasDerivAt (fun t => c (f t)) (c (f' t)) t :=
      c.hasFDerivAt.comp_hasDerivAt t (hf t)
    have hh := mertens_step hy (fun t _ => hd t) (c.continuous.comp hc).continuousOn
    have hi : (∫ t in 0..y, |c (f' t)|) ≤ y*D := by
      calc
        _ ≤ ∫ t in 0..y, D := intervalIntegral.integral_mono_on hy
          ((c.continuous.comp hc).abs.intervalIntegrable _ _) intervalIntegrable_const
          (fun t ht => (hb _).trans (hD t ht))
        _ = _ := by simp
    have he := c.intervalIntegral_comp_comm (μ:=volume) (hfc.intervalIntegrable 0 y)
    simp only [map_sub, map_sum, map_smul, smul_eq_mul, ← he]
    exact hh.trans (mul_le_mul_of_nonneg_left (add_le_add ((hb _).trans hM) hi) KM_nonneg)
  have hr := hproj Complex.reCLM Complex.abs_re_le_norm
  have hi := hproj Complex.imCLM Complex.abs_im_le_norm
  simp only [Complex.reCLM_apply] at hr
  simp only [Complex.imCLM_apply] at hi
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (by linarith)

def primeTransform (L u : ℝ) (H : ℝ → ℂ) : ℂ :=
  (∑ n ∈ Ioc 0 ⌊Real.exp (L*u)⌋₊,
    (ArithmeticFunction.vonMangoldt n / n * Real.log n : ℝ) • H (Real.log n/L))/(L:ℂ)^2

theorem primeTransform_bound (L u U M D : ℝ) (hL : 0 < L) (hu : u ∈ Set.Icc 0 U)
    (hM : 0 ≤ M) (hD : 0 ≤ D) (H H' : ℝ → ℂ)
    (hd : ∀ t, HasDerivAt H (H' t) t) (hc : Continuous H')
    (hb : ∀ t ∈ Set.Icc 0 u, ‖H t‖ ≤ M)
    (hb' : ∀ t ∈ Set.Icc 0 u, ‖H' t‖ ≤ D) :
    ‖primeTransform L u H - ∫ t in 0..u, (t:ℂ)*H t‖ ≤
      (2*KM*(2*U*M+U^2*D))/L := by
  let f := fun t : ℝ => (t:ℂ)*H (t/L)
  let f' := fun t : ℝ => H (t/L)+(t:ℂ)*(H' (t/L)/(L:ℂ))
  have ht (t : ℝ) (ht : t ∈ Set.Icc 0 (L*u)) : t/L ∈ Set.Icc 0 u :=
    ⟨div_nonneg ht.1 hL.le, (div_le_iff₀ hL).mpr (by nlinarith [ht.2])⟩
  have hf (t : ℝ) : HasDerivAt f (f' t) t := by
    convert! (Complex.hasDerivAt_ofReal t).mul ((hd (t/L)).scomp t
      ((hasDerivAt_id t).div_const L)) using 1
    simp [f',Complex.real_smul,div_eq_mul_inv,mul_comm]
  have hfc : Continuous f' := by
    have hH : Continuous H := continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)
    dsimp [f']; fun_prop
  have hfy : ‖f (L*u)‖ ≤ L*U*M := by
    simp only [f,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg hu.1,abs_of_pos hL,mul_div_cancel_left₀ _ hL.ne']
    exact mul_le_mul (mul_le_mul_of_nonneg_left hu.2 hL.le) (hb u ⟨hu.1,le_rfl⟩)
      (norm_nonneg _) (mul_nonneg hL.le (hu.1.trans hu.2))
  have hfd : ∀ t ∈ Set.Icc 0 (L*u), ‖f' t‖ ≤ M+U*D := by
    intro t hti
    apply (norm_add_le _ _).trans
    rw [norm_mul,norm_div,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,
      Real.norm_eq_abs,abs_of_nonneg hti.1,abs_of_pos hL]
    apply add_le_add (hb _ (ht t hti))
    rw [← mul_div_assoc,mul_div_right_comm]
    exact mul_le_mul ((ht t hti).2.trans hu.2) (hb' _ (ht t hti)) (norm_nonneg _)
      (hu.1.trans hu.2)
  have hh := complex_mertens_bound (L*u) (L*U*M) (M+U*D)
    (mul_nonneg hL.le hu.1) f f' hf hfc hfy hfd
  have hi : (∫ t in 0..(L*u), f t)/(L:ℂ)^2 = ∫ t in 0..u, (t:ℂ)*H t := by
    have hh := intervalIntegral.integral_comp_mul_left f hL.ne' (a:=0) (b:=u)
    simp only [mul_zero,Complex.real_smul,Complex.ofReal_inv] at hh
    have he : (fun t : ℝ => f (L*t)) = fun t : ℝ => (L:ℂ)*((t:ℂ)*H t) := by
      funext t; simp [f,hL.ne',Complex.ofReal_mul,mul_assoc]
    rw [he,intervalIntegral.integral_const_mul] at hh
    have hLc : (L:ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    apply (div_eq_iff (pow_ne_zero 2 hLc)).mpr
    have := congrArg (fun z : ℂ => (L:ℂ)*z) hh
    simp only [← mul_assoc,mul_inv_cancel₀ hLc,one_mul] at this
    linear_combination -this
  have he : (∑ n ∈ Ioc 0 ⌊Real.exp (L*u)⌋₊,
      (ArithmeticFunction.vonMangoldt n / n : ℝ) • f (Real.log n))/(L:ℂ)^2 =
      primeTransform L u H := by
    unfold primeTransform
    congr 1; apply sum_congr rfl; intros
    simp [f,Complex.real_smul,Complex.ofReal_mul,mul_assoc]
  rw [← hi,← he,← sub_div,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
  apply (div_le_div_of_nonneg_right hh (sq_nonneg L)).trans
  apply (div_le_iff₀ (sq_pos_of_pos hL)).mpr
  have hU : 0 ≤ U := hu.1.trans hu.2
  have huM := mul_le_mul_of_nonneg_right hu.2 (show 0 ≤ M+U*D by positivity)
  have hKM := KM_nonneg
  have hLu := mul_le_mul_of_nonneg_left huM (show 0 ≤ 2*KM*L by positivity)
  field_simp
  nlinarith

theorem profile_identity (A : ℂ) (u θ t : ℝ) (G : Polynomial ℂ) :
    -first A u θ G t = Complex.exp (-A*t)*BetaKernel.D 1 A θ (u-t) G := by
  simp only [first,ShiftWeights.weight,BetaKernel.D,↓reduceIte]
  ring

def profileTransform (L u θ : ℝ) (G : Polynomial ℂ) (A : ℂ) : ℂ :=
  primeTransform L u (fun t => -first A u θ G t)

def errorCap (G : Polynomial ℂ) (θ C U : ℝ) : ℝ :=
  2*KM*(2*U*firstCap G θ C U+U^2*secondCap G θ C U)

/-- An explicit O(1/L) bound, including u=0 and all higher prime powers. -/
theorem profileTransform_bound (L u θ C U : ℝ) (G : Polynomial ℂ) (A : ℂ)
    (hL : 0 < L) (hθ : 0 < θ) (hC : 0 ≤ C) (hu : u ∈ Set.Icc 0 U) (hA : ‖A‖ ≤ C) :
    ‖profileTransform L u θ G A-FengOutsideProfile.convolution A u θ G‖ ≤ errorCap G θ C U/L := by
  have hU : 0 ≤ U := hu.1.trans hu.2
  have h := primeTransform_bound L u U (firstCap G θ C U) (secondCap G θ C U) hL hu
    (firstCap_nonneg G θ C U hθ hC hU) (secondCap_nonneg G θ C U hθ hC hU)
    (fun t => -first A u θ G t) (fun t => -second A u θ G t)
    (fun t => (first_hasDerivAt A u θ t G).neg) (second_continuous A u θ G).neg
    (fun t ht => by simpa only [norm_neg] using first_bound A u θ t C U G hθ hA hu.2 ht)
    (fun t ht => by simpa only [norm_neg] using second_bound A u θ t C U G hθ hA hu.2 ht)
  simpa only [profileTransform,errorCap,profile_identity,FengOutsideProfile.convolution,mul_assoc] using h

theorem profileTransform_uniform (G : Polynomial ℂ) (hG : G.eval 0 = 0)
    (θ C U : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) :
    TendstoUniformlyOn (fun L (p : ℂ × ℝ) => profileTransform L p.2 θ G p.1)
      (fun p => BetaKernel.D (-1) p.1 θ p.2 G) atTop
      {p | ‖p.1‖ ≤ C ∧ p.2 ∈ Set.Icc 0 U} := by
  have hlim : Tendsto (fun L : ℝ => errorCap G θ C U/L) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using tendsto_inv_atTop_zero.const_mul (errorCap G θ C U)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [eventually_gt_atTop (0:ℝ),hlim.eventually (gt_mem_nhds heps)] with L hL he
  intro p hp
  rw [dist_comm,dist_eq_norm,← FengOutsideProfile.convolution_inverse p.1 p.2 θ G hG]
  exact (profileTransform_bound L p.2 θ C U G p.1 hL hθ hC hp.2 hp.1).trans_lt he

#print axioms complex_mertens_bound
#print axioms primeTransform_bound
#print axioms profileTransform_bound
#print axioms profileTransform_uniform
end XiPrime8845.FengPrimeProfile
