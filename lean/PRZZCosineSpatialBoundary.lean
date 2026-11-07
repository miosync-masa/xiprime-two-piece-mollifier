import PRZZCosineSpatialJets
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Actual reciprocal sourceW boundary bounds. Positive decay rates
are chosen differently at the two endpoints; no estimate uniform across
sigma=0 or all positive X is asserted. -/
noncomputable section
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZCosineSpatialBoundary
open PRZZDyadicEnvelope PRZZSourceWDerivatives PRZZCosineSpatialJets
set_option maxHeartbeats 5000000

theorem source_caps (sigma : ℂ) (hs : sigma ≠ 0) (a : ℝ) (ha : 0 < a) :
    ∃ B : ℝ, 0 < B ∧ ∀ u : ℝ, 0 < u →
      ‖sourceW sigma u‖ ≤ B*u^(-a) ∧
      u*‖jet sigma 0 u‖ ≤ B*u^(-a) ∧
      u^2*‖jet sigma 1 u‖ ≤ B*u^(-a) := by
  obtain ⟨C0,D0,hC0,hD0,h0⟩ := source_all_decay 0 a ha
  obtain ⟨C1,D1,hC1,hD1,h1⟩ := source_all_decay 1 a ha
  obtain ⟨C2,D2,hC2,hD2,h2⟩ := source_all_decay 2 a ha
  let B0 := C0+D0/‖sigma‖^2
  let B1 := C1+D1/‖sigma‖^2
  let B2 := C2+D2/‖sigma‖^2
  have hb0 : 0 ≤ B0 := by dsimp [B0]; positivity
  have hb1 : 0 ≤ B1 := by dsimp [B1]; positivity
  have hb2 : 0 ≤ B2 := by dsimp [B2]; positivity
  refine ⟨B0+B1+B2+1,by positivity,?_⟩
  intro u hu
  have h0' := h0 sigma hs u hu
  have h1' := h1 sigma hs u hu
  have h2' := h2 sigma hs u hu
  simp only [iteratedDeriv_zero,pow_zero,div_one] at h0'
  rw [source_iterated sigma hs 0 u hu] at h1'
  rw [show (2:ℕ) = 1+1 by rfl,source_iterated sigma hs 1 u hu] at h2'
  simp only [pow_one] at h1'
  have hh1 : u*‖jet sigma 0 u‖ ≤ B1*u^(-a) := by
    have hh := (le_div_iff₀ hu).mp h1'
    dsimp [B1]; nlinarith only [hh]
  have hh2 : u^2*‖jet sigma 1 u‖ ≤ B2*u^(-a) := by
    have hh := (le_div_iff₀ (sq_pos_of_pos hu)).mp h2'
    dsimp [B2]; nlinarith only [hh]
  refine ⟨h0'.trans ?_,hh1.trans ?_,hh2.trans ?_⟩ <;>
    (apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hu.le _)
     dsimp only [B0,B1,B2] at *
     linarith)

theorem power_norm (p : ℂ) (y : ℝ) (hy : 0 < y) :
    ‖power p y‖ = y^p.re := by
  rw [power,Complex.norm_exp,Real.rpow_def_of_pos hy]
  congr 1
  simp
  ring

theorem reciprocal_scale (X y a : ℝ) (hX : 0 < X) (hy : 0 < y) :
    (arg X y)^(-a) = X^(-a)*y^(2*a) := by
  rw [PRZZCosineSpatialJets.arg,Real.div_rpow hX.le (sq_nonneg y),← Real.rpow_natCast y 2,
    ← Real.rpow_mul hy.le]
  norm_num only [Nat.cast_ofNat]
  rw [show (2:ℝ)*(-a) = -(2*a) by ring,Real.rpow_neg hy.le,div_inv_eq_mul]

theorem normalized_power (p : ℂ) (X y a : ℝ) (n : ℕ)
    (hX : 0 < X) (hy : 0 < y) :
    (y^p.re/y^n)*(arg X y)^(-a) = X^(-a)*y^(p.re+2*a-n) := by
  rw [reciprocal_scale X y a hX hy,Real.rpow_sub hy,Real.rpow_add hy,Real.rpow_natCast]
  ring

theorem bounds (p sigma : ℂ) (hs : sigma ≠ 0) (X a : ℝ) (hX : 0 < X) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 0 < y →
      ‖primitive p sigma X y‖ ≤ C*y^(p.re+2*a) ∧
      ‖first p sigma X y‖ ≤ C*(‖p‖+2)*y^(p.re+2*a-1) ∧
      ‖second p sigma X y‖ ≤ C*(‖p*(p-1)‖+‖6-4*p‖+4)*y^(p.re+2*a-2) := by
  obtain ⟨B,hB,hb⟩ := source_caps sigma hs a ha
  refine ⟨B*X^(-a),by positivity,?_⟩
  intro y hy
  have hu : 0 < arg X y := by unfold PRZZCosineSpatialJets.arg; positivity
  obtain ⟨hw,hj,hj'⟩ := hb (arg X y) hu
  have hb1 : ‖p*sourceW sigma (arg X y)-2*(arg X y:ℂ)*jet sigma 0 (arg X y)‖ ≤
      (‖p‖+2)*(B*(arg X y)^(-a)) := by
    apply (norm_sub_le _ _).trans
    simp only [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hu]
    have hh := mul_le_mul_of_nonneg_left hw (norm_nonneg p)
    nlinarith only [hh,hj]
  have hb2 : ‖p*(p-1)*sourceW sigma (arg X y)+
      (6-4*p)*(arg X y:ℂ)*jet sigma 0 (arg X y)+4*(arg X y:ℂ)^2*jet sigma 1 (arg X y)‖ ≤
      (‖p*(p-1)‖+‖6-4*p‖+4)*(B*(arg X y)^(-a)) := by
    apply ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
    simp only [norm_mul,norm_pow,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hu]
    have h0 := mul_le_mul_of_nonneg_left hw (norm_nonneg (p*(p-1)))
    have h1 := mul_le_mul_of_nonneg_left hj (norm_nonneg (6-4*p))
    rw [norm_mul] at h0
    nlinarith only [h0,h1,hj']
  refine ⟨?_,?_,?_⟩
  · rw [primitive,norm_mul,power_norm p y hy]
    apply (mul_le_mul_of_nonneg_left hw (Real.rpow_nonneg hy.le _)).trans_eq
    have he := normalized_power p X y a 0 hX hy
    simp only [pow_zero,div_one,Nat.cast_zero,sub_zero] at he
    nlinarith only [congrArg (fun z : ℝ => B*z) he]
  · rw [first,norm_mul,norm_div,power_norm p y hy,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hy]
    apply (mul_le_mul_of_nonneg_left hb1 (by positivity)).trans_eq
    have he := normalized_power p X y a 1 hX hy
    simp only [pow_one,Nat.cast_one] at he
    calc
      _ = (B*(‖p‖+2))*((y^p.re/y)*(arg X y)^(-a)) := by ring
      _ = _ := by rw [he]; ring
  · rw [second,norm_mul,norm_div,power_norm p y hy,norm_pow,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos hy]
    apply (mul_le_mul_of_nonneg_left hb2 (by positivity)).trans_eq
    have he := normalized_power p X y a 2 hX hy
    norm_num only [Nat.cast_ofNat] at he
    calc
      _ = (B*(‖p*(p-1)‖+‖6-4*p‖+4))*((y^p.re/y^2)*(arg X y)^(-a)) := by ring
      _ = _ := by rw [he]; ring

/-- Small decay rate at infinity; p=sigma-1 for the actual zero field. -/
theorem endpoint_infinity (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (X : ℝ) (hX : 0 < X) :
    Tendsto (primitive (sigma-1) sigma X) atTop (𝓝 0) ∧
      Tendsto (first (sigma-1) sigma X) atTop (𝓝 0) := by
  obtain ⟨C,hC,hb⟩ := bounds (sigma-1) sigma hs X (1/8) hX (by norm_num)
  have hr := (abs_le.mp ((abs_re_le_norm sigma).trans hn)).2
  have he0 : (sigma-1).re+2*(1/8:ℝ) < 0 := by simp; linarith
  have he1 : (sigma-1).re+2*(1/8:ℝ)-1 < 0 := by linarith
  have hp (e : ℝ) (he : e < 0) : Tendsto (fun y : ℝ => y^e) atTop (𝓝 0) := by
    simpa only [neg_neg] using tendsto_rpow_neg_atTop (neg_pos.mpr he)
  constructor
  · apply squeeze_zero_norm' _ (by simpa using (hp _ he0).const_mul C)
    filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
    simpa using (hb y hy).1
  · apply squeeze_zero_norm' _ (by simpa using (hp _ he1).const_mul (C*(‖sigma-1‖+2)))
    filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
    simpa using (hb y hy).2.1

/-- Stronger source decay is spent only at zero. -/
theorem endpoint_zero (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (X : ℝ) (hX : 0 < X) :
    Tendsto (primitive (sigma-1) sigma X) (𝓝[>] (0:ℝ)) (𝓝 0) ∧
      Tendsto (first (sigma-1) sigma X) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  obtain ⟨C,hC,hb⟩ := bounds (sigma-1) sigma hs X 2 hX (by norm_num)
  have hr := (abs_le.mp ((abs_re_le_norm sigma).trans hn)).1
  have he0 : 0 < (sigma-1).re+2*(2:ℝ) := by simp; linarith
  have he1 : 0 < (sigma-1).re+2*(2:ℝ)-1 := by simp; linarith
  have hp (e : ℝ) (he : 0 < e) : Tendsto (fun y : ℝ => y^e) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hh := (Real.continuousAt_rpow_const 0 e (Or.inr he.le)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
    simpa [Real.zero_rpow he.ne'] using hh
  constructor
  · apply squeeze_zero_norm' _ (by simpa using (hp _ he0).const_mul C)
    filter_upwards [self_mem_nhdsWithin] with y hy
    simpa using (hb y hy).1
  · apply squeeze_zero_norm' _ (by simpa using (hp _ he1).const_mul (C*(‖sigma-1‖+2)))
    filter_upwards [self_mem_nhdsWithin] with y hy
    simpa using (hb y hy).2.1

#print axioms source_caps
#print axioms power_norm
#print axioms reciprocal_scale
#print axioms normalized_power
#print axioms bounds
#print axioms endpoint_infinity
#print axioms endpoint_zero
end XiPrime8845.PRZZCosineSpatialBoundary
