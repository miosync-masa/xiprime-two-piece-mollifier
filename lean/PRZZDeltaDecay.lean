import PRZZWeightFourier
import PRZZSourceCutoffs

/-! Time oscillation of discarded source gaps. The logarithmic phase is
kept exact, with no small-ratio expansion outside the cutoff. Derivative
L1 masses remain explicit until supplied for the actual time amplitude. -/
noncomputable section
open scoped ContDiff FourierTransform BigOperators
open Complex MeasureTheory
namespace XiPrime8845.PRZZDeltaDecay
set_option maxHeartbeats 3000000

theorem gap_le_log (x y B : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hxb : x ≤ B) (hyb : y ≤ B) :
    |y-x| ≤ B*|Real.log (y/x)| := by
  have step (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x ≤ y) (hyb : y ≤ B) :
      y-x ≤ B*|Real.log (y/x)| := by
    have hh := Real.one_sub_inv_le_log_of_pos (div_pos hy hx)
    have he : 1-(y/x)⁻¹ = (y-x)/y := by field_simp
    rw [he] at hh
    have hl : 0 ≤ Real.log (y/x) := Real.log_nonneg ((one_le_div hx).mpr hxy)
    rw [abs_of_nonneg hl]
    have hm := (div_le_iff₀ hy).mp hh
    nlinarith [mul_le_mul_of_nonneg_right hyb hl]
  rcases le_total x y with hxy | hyx
  · simpa [abs_of_nonneg (sub_nonneg.mpr hxy)] using step x y hx hy hxy hyb
  · have hh := step y x hy hx hyx hxb
    rw [Real.log_div hx.ne' hy.ne', Real.log_div hy.ne' hx.ne'] at *
    simpa only [abs_of_nonpos (sub_nonpos.mpr hyx), neg_sub, abs_sub_comm] using hh

/-- Repeated time integration by parts. Compact support supplies all
boundary cancellations and derivative integrability. -/
theorem oscillatory_bound (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) (n : ℕ) (omega : ℝ) (ho : omega ≠ 0) :
    ‖∫ t : ℝ, exp (I*((t*omega:ℝ):ℂ))*f t‖ ≤
      (∫ t, ‖iteratedDeriv n f t‖)/|omega|^n := by
  have hi (i : ℕ) : Integrable (iteratedDeriv i f) :=
    (hf.continuous_iteratedDeriv i (by exact_mod_cast (le_top : (i:ℕ∞) ≤ ⊤))).integrable_of_hasCompactSupport
      (PRZZCutoffJets.jet_support f hs i)
  have hjet := Real.fourier_iteratedDeriv (N := ⊤) hf (fun i _ => hi i)
    (by simp : (n:ℕ∞) ≤ ⊤)
  have hb := PRZZWeightFourier.norm_fourier_le (iteratedDeriv n f) (-omega/(2*Real.pi))
  rw [hjet] at hb
  have he : 𝓕 f (-omega/(2*Real.pi)) =
      ∫ t : ℝ, exp (I*((t*omega:ℝ):ℂ))*f t := by
    rw [Real.fourier_eq']
    congr 1
    funext t
    simp only [RCLike.inner_apply,conj_trivial,smul_eq_mul]
    congr 2
    push_cast
    field_simp
    <;> ring
  have hn : ‖(2*Real.pi*I*((-omega/(2*Real.pi):ℝ):ℂ):ℂ)‖ = |omega| := by
    have he : (2*Real.pi*I*((-omega/(2*Real.pi):ℝ):ℂ):ℂ) = -I*omega := by
      push_cast
      field_simp
      <;> ring
    rw [he]
    simp
  rw [norm_smul,norm_pow] at hb
  rw [hn,he] at hb
  exact (le_div_iff₀ (pow_pos (abs_pos.mpr ho) n)).mpr (by simpa [mul_comm] using hb)

/-- A discarded nonzero gap gains an arbitrary inverse power. This is
valid for both signs and does not assume that the ratio is close to one. -/
theorem discarded_bound (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) (n : ℕ) (x y B D : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hxb : x ≤ B) (hyb : y ≤ B)
    (hD : 0 < D) (hgap : D ≤ |y-x|) :
    ‖∫ t : ℝ, exp (I*((t*Real.log (y/x):ℝ):ℂ))*f t‖ ≤
      (∫ t, ‖iteratedDeriv n f t‖)*(B/D)^n := by
  have hB : 0 < B := hx.trans_le hxb
  have hh := hgap.trans (gap_le_log x y B hx hy hxb hyb)
  have ho : Real.log (y/x) ≠ 0 := by intro he; simp [he] at hh; linarith
  apply (oscillatory_bound f hf hs n _ ho).trans
  have hr : 1/|Real.log (y/x)| ≤ B/D := by
    apply (div_le_div_iff₀ (abs_pos.mpr ho) hD).mpr
    simpa [mul_comm] using hh
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1/|Real.log (y/x)|) hr n
  have hm := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ ∫ t, ‖iteratedDeriv n f t‖ from integral_nonneg (fun t => norm_nonneg _))
  simpa only [div_pow,one_pow,mul_one_div] using hm

/-- The actual coefficient-weighted finite sum is integrated before its
norm is estimated. Smooth compact amplitudes justify the exchange. -/
theorem finite_discarded {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (f : ι → ℝ → ℂ) (hf : ∀ i ∈ s, ContDiff ℝ ∞ (f i))
    (hs : ∀ i ∈ s, HasCompactSupport (f i)) (n : ℕ) (x y B D : ι → ℝ)
    (hx : ∀ i ∈ s, 0 < x i) (hy : ∀ i ∈ s, 0 < y i)
    (hxb : ∀ i ∈ s, x i ≤ B i) (hyb : ∀ i ∈ s, y i ≤ B i)
    (hD : ∀ i ∈ s, 0 < D i) (hgap : ∀ i ∈ s, D i ≤ |y i-x i|) :
    ‖∫ t : ℝ, ∑ i ∈ s, c i*(exp (I*((t*Real.log (y i/x i):ℝ):ℂ))*f i t)‖ ≤
      ∑ i ∈ s, ‖c i‖*(∫ t, ‖iteratedDeriv n (f i) t‖)*(B i/D i)^n := by
  have hi (i : ι) (hi : i ∈ s) :
      Integrable (fun t : ℝ => c i*(exp (I*((t*Real.log (y i/x i):ℝ):ℂ))*f i t)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · have hc := (hf i hi).continuous
      fun_prop
    · exact ((hs i hi).mul_left).mul_left
  rw [integral_finsetSum s hi]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [integral_const_mul,norm_mul]
  exact (mul_le_mul_of_nonneg_left
    (discarded_bound (f i) (hf i hi) (hs i hi) n (x i) (y i) (B i) (D i)
      (hx i hi) (hy i hi) (hxb i hi) (hyb i hi) (hD i hi) (hgap i hi))
    (norm_nonneg _)).trans_eq (by ring)

/-- Audit the time-derivative gain against the discarded gap scale.
The time-amplitude derivative estimate is explicit, not inferred from
spatial Poisson derivatives. The resulting exponent is 1-n*eps. -/
theorem height_gain (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) (n : ℕ) (x y B D T C U eps : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hxb : x ≤ B) (hyb : y ≤ B)
    (hD : 0 < D) (hgap : D ≤ |y-x|) (hT : 0 < T)
    (hC : 0 ≤ C) (hU : 0 ≤ U)
    (hmass : (∫ t, ‖iteratedDeriv n f t‖) ≤ U*T^(1-(n:ℝ)))
    (hscale : B/D ≤ C*T^(1-eps)) :
    ‖∫ t : ℝ, exp (I*((t*Real.log (y/x):ℝ):ℂ))*f t‖ ≤
      U*C^n*T^(1-(n:ℝ)*eps) := by
  have hB : 0 < B := hx.trans_le hxb
  apply (discarded_bound f hf hs n x y B D hx hy hxb hyb hD hgap).trans
  calc
    _ ≤ (U*T^(1-(n:ℝ)))*(C*T^(1-eps))^n := by
      gcongr
    _ = U*C^n*T^(1-(n:ℝ)*eps) := by
      rw [mul_pow, ← Real.rpow_natCast (T^(1-eps)) n, ← Real.rpow_mul hT.le]
      rw [show 1-(n:ℝ)*eps = (1-(n:ℝ))+(1-eps)*(n:ℝ) by ring,
        Real.rpow_add hT]
      ring

/-- Substitute the literal source Delta cutoff before taking powers. -/
theorem source_scale (T M Q d C eps : ℝ) (hT : 0 < T) (hM : 0 < M)
    (hQ : 0 < Q) (hd : 0 < d) :
    (C*M*Q/d)/(PRZZSourceCutoffs.deltaCutoff T M Q eps/d) = C*T^(1-eps) := by
  unfold PRZZSourceCutoffs.deltaCutoff
  field_simp

#print axioms source_scale
#print axioms height_gain
#print axioms finite_discarded
#print axioms gap_le_log
#print axioms oscillatory_bound
#print axioms discarded_bound
end XiPrime8845.PRZZDeltaDecay
