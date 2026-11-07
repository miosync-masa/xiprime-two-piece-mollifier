import PRZZCosineImproper
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! A fixed, integrable near/tail envelope supplies truncation-uniform
cosine Mellin bounds. Constants precede the complex parameter and R.
No actual zero-mode Mellin exchange is assumed. -/
noncomputable section
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZCosineDominated
open PRZZGammaLaplace PRZZCosineImproper
set_option maxHeartbeats 5000000

def nearMass : ℝ := ∫ x in (0:ℝ)..1, x^(-5/8:ℝ)
def tailMass : ℝ := ∫ x in Ioi (1:ℝ), x^(-11/8:ℝ)
def constant : ℝ := nearMass+2+tailMass

theorem masses_nonneg : 0 ≤ nearMass ∧ 0 ≤ tailMass := by
  constructor
  · exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx => Real.rpow_nonneg hx.1 _)
  · apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact Real.rpow_nonneg (lt_trans zero_lt_one hx).le _

theorem near_bound (z c : ℂ) (hz : 3/8 ≤ z.re) (hc : 0 ≤ c.re) :
    ‖∫ x in (0:ℝ)..1, kernel z c x‖ ≤ nearMass := by
  apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
  · apply Filter.Eventually.of_forall
    intro x hx
    exact (tail_norm z c hc x hx.1).trans
      (Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2 (by linarith))
  · exact intervalIntegral.intervalIntegrable_rpow' (by norm_num)

theorem derivative_bound (z c : ℂ) (hz : z.re ≤ 5/8) (hc : 0 ≤ c.re)
    (R : ℝ) (hR : 1 ≤ R) :
    ‖∫ x in (1:ℝ)..R, kernel (z-1) c x‖ ≤ tailMass := by
  have hi := integrableOn_Ioi_rpow_of_lt (a := (-11/8:ℝ)) (by norm_num) zero_lt_one
  have hb : ‖∫ x in (1:ℝ)..R, kernel (z-1) c x‖ ≤
      ∫ x in (1:ℝ)..R, x^(-11/8:ℝ) := by
    apply intervalIntegral.norm_integral_le_of_norm_le hR
    · apply Filter.Eventually.of_forall
      intro x hx
      apply (tail_norm (z-1) c hc x (lt_trans zero_lt_one hx.1)).trans
      apply Real.rpow_le_rpow_of_exponent_le hx.1.le
      simp only [sub_re,one_re]
      linarith
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mpr
        (hi.mono_set Ioc_subset_Ioi_self)
  apply hb.trans
  rw [intervalIntegral.integral_of_le hR]
  apply setIntegral_mono_set hi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact Real.rpow_nonneg (lt_trans zero_lt_one hx).le _
  · exact Filter.Eventually.of_forall (fun x hx => hx.1)

theorem kernel_uniform (z c : ℂ) (hz : 3/8 ≤ z.re) (hz1 : z.re ≤ 5/8)
    (hc : 0 ≤ c.re) (hn : 1 ≤ ‖c‖) (R : ℝ) (hR : 1 ≤ R) :
    ‖∫ x in (0:ℝ)..R, kernel z c x‖ ≤ constant*(1+‖z‖) := by
  have hz0 : 0 < z.re := by linarith
  have hzlt : z.re < 1 := by linarith
  have hc0 : c ≠ 0 := norm_pos_iff.mp (by linarith)
  have hnear := near_bound z c hz hc
  have hder := derivative_bound z c hz1 hc R hR
  have h1 : ‖kernel z c 1‖ ≤ 1 := by simpa using tail_norm z c hc 1 zero_lt_one
  have h2 : ‖kernel z c R‖ ≤ 1 := (tail_norm z c hc R (by linarith)).trans
    (Real.rpow_le_one_of_one_le_of_nonpos hR (by linarith))
  have ht : ‖∫ x in (1:ℝ)..R, kernel z c x‖ ≤ 2+(‖z‖+1)*tailMass := by
    rw [finite_tail z c hzlt hc0 R hR,norm_div]
    apply (div_le_self (norm_nonneg _) hn).trans
    apply (norm_add_le _ _).trans
    have hm : ‖z-1‖ ≤ ‖z‖+1 := by simpa using norm_sub_le z 1
    have hh := mul_le_mul hm hder (norm_nonneg _) (by positivity : 0 ≤ ‖z‖+1)
    rw [norm_mul]
    linarith [(norm_sub_le (kernel z c 1) (kernel z c R)).trans (add_le_add h1 h2)]
  have hi := local_integrable z c hz0 hc 1 (by norm_num)
  have hj : IntervalIntegrable (kernel z c) volume 1 R := by
    apply ContinuousOn.intervalIntegrable
    apply (kernel_continuous z c).mono
    rw [uIcc_of_le hR]; intro x hx
    exact lt_of_lt_of_le zero_lt_one hx.1
  rw [← intervalIntegral.integral_add_adjacent_intervals hi hj]
  apply (norm_add_le _ _).trans
  apply (add_le_add hnear ht).trans
  dsimp [constant]
  nlinarith [norm_nonneg z,mul_nonneg masses_nonneg.1 (norm_nonneg z)]

theorem cosine_uniform : 0 < constant ∧ ∀ z : ℂ,
    3/8 ≤ z.re → z.re ≤ 5/8 → ∀ R : ℝ, 1 ≤ R →
    ‖∫ x in (0:ℝ)..R, (x:ℂ)^(z-1)*Complex.cos (x:ℂ)‖ ≤ constant*(1+‖z‖) := by
  refine ⟨by dsimp [constant]; linarith [masses_nonneg.1,masses_nonneg.2],?_⟩
  intro z hz hz1 R hR
  have hp := kernel_uniform z (-I) hz hz1 (by simp) (by simp) R hR
  have hm := kernel_uniform z I hz hz1 (by simp) (by simp) R hR
  have hz0 : 0 < z.re := by linarith
  have hi := local_integrable z (-I) hz0 (by simp) R (by linarith)
  have hj := local_integrable z I hz0 (by simp) R (by linarith)
  have he : (∫ x in (0:ℝ)..R, (x:ℂ)^(z-1)*Complex.cos (x:ℂ)) =
      ((∫ x in (0:ℝ)..R, kernel z (-I) x)+(∫ x in (0:ℝ)..R, kernel z I x))/2 := by
    rw [← intervalIntegral.integral_add hi hj,← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro x hx
    simpa only [PRZZCosineAbel.integrand,ofReal_zero,neg_zero,zero_mul,
      Complex.exp_zero,mul_one,zero_sub,zero_add] using PRZZCosineAbel.exponential_pair z 0 x
  rw [he,norm_div]
  norm_num only [Complex.norm_ofNat]
  have hh := norm_add_le (∫ x in (0:ℝ)..R, kernel z (-I) x) (∫ x in (0:ℝ)..R, kernel z I x)
  linarith

theorem source_uniform : ∃ C : ℝ, 0 < C ∧ ∀ (sigma : ℂ) (tau R : ℝ),
    ‖sigma‖ ≤ 1/8 → 1 ≤ R →
    let s : ℂ := (5/4:ℝ)+(tau:ℂ)*I
    let z : ℂ := 2*s+sigma
    ‖(z-1)*(z-2)*(∫ x in (0:ℝ)..R, (x:ℂ)^(z-3)*Complex.cos (x:ℂ))‖ ≤
      C*(1+|tau|)^3 := by
  refine ⟨27*constant,by nlinarith [cosine_uniform.1],?_⟩
  intro sigma tau R hs hR
  dsimp only
  let z : ℂ := 2*((5/4:ℝ)+(tau:ℂ)*I)+sigma
  let w : ℂ := z-2
  have hb := abs_le.mp ((Complex.abs_re_le_norm sigma).trans hs)
  have hwlo : 3/8 ≤ w.re := by dsimp [w,z]; norm_num; linarith
  have hwhi : w.re ≤ 5/8 := by dsimp [w,z]; norm_num; linarith
  have he : w = (1/2:ℂ)+2*(tau:ℂ)*I+sigma := by dsimp [w,z]; push_cast; ring
  have ht : ‖w‖ ≤ 1+2*|tau| := by
    rw [he]
    have hh := (norm_add_le ((1/2:ℂ)+2*(tau:ℂ)*I) sigma).trans
      (add_le_add (norm_add_le (1/2:ℂ) (2*(tau:ℂ)*I)) (le_refl ‖sigma‖))
    norm_num [norm_mul,Complex.norm_real,Real.norm_eq_abs] at hh
    linarith
  have hzw : ‖z-1‖ ≤ 1+‖w‖ := by
    rw [show z-1 = 1+w by dsimp [w]; ring]
    simpa using norm_add_le (1:ℂ) w
  have hh := cosine_uniform.2 w hwlo hwhi R hR
  rw [show w-1 = z-3 by dsimp [w]; ring] at hh
  have hn : 0 ≤ constant := cosine_uniform.1.le
  change ‖(z-1)*(z-2)*_‖ ≤ _
  calc
    _ = ‖z-1‖*‖w‖*‖∫ x in (0:ℝ)..R, (x:ℂ)^(z-3)*Complex.cos (x:ℂ)‖ := by rw [norm_mul,norm_mul]
    _ ≤ (1+‖w‖)*(1+‖w‖)*(constant*(1+‖w‖)) := by gcongr; linarith [norm_nonneg w]
    _ = constant*(1+‖w‖)^3 := by ring
    _ ≤ constant*(3*(1+|tau|))^3 := by gcongr; linarith [abs_nonneg tau]
    _ = _ := by ring

theorem gaussian_majorant_integrable :
    Integrable (fun tau : ℝ => (1+|tau|)^3*Real.exp (-tau^2)) := by
  have h (n : ℕ) : Integrable (fun t : ℝ => |t|^n*Real.exp (-t^2)) := by
    have hh := integrable_rpow_mul_exp_neg_mul_sq (b := (1:ℝ)) (s := (n:ℝ))
      (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) n])
    simpa only [Real.rpow_natCast,one_mul,neg_mul,norm_mul,Real.norm_eq_abs,
      abs_pow,Real.abs_exp] using hh.norm
  have h0 := h 0
  have h1 := (h 1).const_mul 3
  have h2 := (h 2).const_mul 3
  have h3 := h 3
  have he : (fun t : ℝ => (1+|t|)^3*Real.exp (-t^2)) =
      (fun t : ℝ => ((|t|^0*Real.exp (-t^2)+3*(|t|^1*Real.exp (-t^2)))+
        3*(|t|^2*Real.exp (-t^2)))+|t|^3*Real.exp (-t^2)) := by funext t; ring
  rw [he]
  exact ((h0.add h1).add h2).add h3

/-- The actual vertical Gaussian supplies a single integrable majorant
for all truncations and all shifts in the fixed disc. The remaining
annihilator and scale factors are not silently included. -/
theorem gaussian_source_uniform : ∃ C : ℝ, 0 < C ∧
    Integrable (fun tau : ℝ => C*((1+|tau|)^3*Real.exp (-tau^2))) ∧
    ∀ (sigma : ℂ) (tau R : ℝ), ‖sigma‖ ≤ 1/8 → 1 ≤ R →
    let s : ℂ := (5/4:ℝ)+(tau:ℂ)*I
    let z : ℂ := 2*s+sigma
    ‖Complex.exp (s^2)*((z-1)*(z-2)*
      (∫ x in (0:ℝ)..R, (x:ℂ)^(z-3)*Complex.cos (x:ℂ)))‖ ≤
        C*((1+|tau|)^3*Real.exp (-tau^2)) := by
  obtain ⟨C,hC,h⟩ := source_uniform
  refine ⟨Real.exp (25/16)*C,by positivity,
    gaussian_majorant_integrable.const_mul _,?_⟩
  intro sigma tau R hs hR
  dsimp only
  have hh := h sigma tau R hs hR
  dsimp only at hh
  have he : ‖Complex.exp (((5/4:ℝ)+(tau:ℂ)*I)^2)‖ =
      Real.exp (25/16)*Real.exp (-tau^2) := by
    rw [Complex.norm_exp]
    have hr : ((((5/4:ℝ):ℂ)+(tau:ℂ)*I)^2).re = (25/16:ℝ)-tau^2 := by
      simp [pow_two,mul_re]; ring
    rw [hr,sub_eq_add_neg,Real.exp_add]
  rw [norm_mul,he]
  exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by ring)

#print axioms gaussian_source_uniform
#print axioms source_uniform
#print axioms gaussian_majorant_integrable
#print axioms masses_nonneg
#print axioms near_bound
#print axioms derivative_bound
#print axioms kernel_uniform
#print axioms cosine_uniform
end XiPrime8845.PRZZCosineDominated
