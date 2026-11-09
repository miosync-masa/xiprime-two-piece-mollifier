import PRZZMellinSeminorm

/-! Quantitative Mellin mass on any fixed positive support interval.
Dimensionless ordinary jets give logarithmic pullback bounds without
scale-dependent constants. The width log(b/a) is retained explicitly.
The existing [1,2] API is unchanged. -/
noncomputable section
open scoped ContDiff FourierTransform Topology
open Complex MeasureTheory Set Filter
namespace XiPrime8845.PRZZMellinInterval
open PRZZSmoothMellin PRZZMellinSeparation PRZZMellinSeminorm
set_option maxHeartbeats 8000000

theorem frequency_power (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (a b : ℝ) (ha : 0 < a) (hs : Function.support f ⊆ Icc a b) (n : ℕ) (t : ℝ) :
    |t|^n*‖mellin f (t*I)‖ ≤ mass f n := by
  have hg : ContDiff ℝ ∞ (logPull f) := hf.comp (by fun_prop)
  have hc := logPull_compact f a b ha hs
  have hi (i : ℕ) : Integrable (iteratedDeriv i (logPull f)) :=
    (hg.continuous_iteratedDeriv i (by exact_mod_cast (le_top : (i:ℕ∞) ≤ ⊤))).integrable_of_hasCompactSupport
      (PRZZCutoffJets.jet_support _ hc i)
  have he := congrFun (Real.fourier_iteratedDeriv (N := ⊤) hg (fun i _ => hi i)
    (by simp : (n:ℕ∞) ≤ ⊤)) (t/(2*Real.pi))
  have hb := PRZZWeightFourier.norm_fourier_le (iteratedDeriv n (logPull f)) (t/(2*Real.pi))
  rw [he] at hb
  simp only [norm_smul,norm_pow,norm_mul,Complex.norm_ofNat,Complex.norm_I,
    Complex.norm_real,Real.norm_eq_abs,abs_div,abs_of_pos Real.pi_pos,mul_one] at hb
  rw [mellin_fourier]
  have hp : 2*Real.pi*(|t|/|2*Real.pi|) = |t| := by
    rw [abs_of_pos (by positivity : 0 < 2*Real.pi)]; field_simp
  rw [hp] at hb
  exact hb

theorem log_jet_support (f : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support f ⊆ Icc a b) (n : ℕ) :
    tsupport (iteratedDeriv n (logPull f)) ⊆ Icc (-Real.log b) (-Real.log a) := by
  induction n with
  | zero =>
    apply closure_minimal _ isClosed_Icc
    simpa only [iteratedDeriv_zero] using logPull_support f a b ha hs
  | succ n ih => rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans ih

theorem mass_le (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hs : Function.support f ⊆ Icc a b)
    (n : ℕ) (B : ℝ)
    (hb : ∀ u ∈ Icc (-Real.log b) (-Real.log a), ‖iteratedDeriv n (logPull f) u‖ ≤ B) :
    mass f n ≤ Real.log (b/a)*B := by
  have hg : ContDiff ℝ ∞ (logPull f) := hf.comp (by fun_prop)
  have hi : Integrable (iteratedDeriv n (logPull f)) :=
    (hg.continuous_iteratedDeriv n (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))).integrable_of_hasCompactSupport
      (PRZZCutoffJets.jet_support _ (logPull_compact f a b ha hs) n)
  have he : mass f n = ∫ u in Icc (-Real.log b) (-Real.log a), ‖iteratedDeriv n (logPull f) u‖ := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    have hz : iteratedDeriv n (logPull f) u = 0 := by
      by_contra hh
      exact hu (log_jet_support f a b ha hs n (subset_closure hh))
    rw [hz,norm_zero]
  rw [he]
  have hh := setIntegral_mono_on hi.norm.integrableOn
    (show IntegrableOn (fun _ : ℝ => B) (Icc (-Real.log b) (-Real.log a)) from continuous_const.integrableOn_Icc)
    measurableSet_Icc hb
  apply hh.trans_eq
  have hl : Real.log a ≤ Real.log b := Real.log_le_log ha hab
  have hw : -Real.log a-(-Real.log b) = Real.log (b/a) := by
    rw [Real.log_div (ha.trans_le hab).ne' ha.ne']; ring
  have hw0 : 0 ≤ Real.log (b/a) := Real.log_nonneg ((one_le_div ha).mpr hab)
  simp [Measure.real,Real.volume_Icc,smul_eq_mul,hw,hw0,mul_comm]

theorem mass_from_scaled_jets (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hs : Function.support f ⊆ Icc a b)
    (U : ℕ → ℝ) (hu : ∀ n (x : ℝ), ‖(x:ℂ)^n*iteratedDeriv n f x‖ ≤ U n) :
    mass f 0 ≤ Real.log (b/a)*U 0 ∧
      mass f 3 ≤ Real.log (b/a)*(U 1+3*U 2+U 3) := by
  refine ⟨mass_le f hf a b ha hab hs 0 (U 0) (by intro u huu; simpa [logPull,xlog] using hu 0 (xlog u)),?_⟩
  apply mass_le f hf a b ha hab hs 3
  intro u huu
  rw [log_third f hf]
  dsimp only
  have hh := (norm_sub_le
    (-(xlog u:ℂ)*iteratedDeriv 1 f (xlog u)-3*(xlog u:ℂ)^2*iteratedDeriv 2 f (xlog u))
    ((xlog u:ℂ)^3*iteratedDeriv 3 f (xlog u))).trans
      (add_le_add (norm_sub_le _ _) le_rfl)
  have h1 : ‖-(xlog u:ℂ)*iteratedDeriv 1 f (xlog u)‖ ≤ U 1 := by
    simpa only [neg_mul,norm_neg,pow_one] using hu 1 (xlog u)
  have h2 : ‖3*(xlog u:ℂ)^2*iteratedDeriv 2 f (xlog u)‖ ≤ 3*U 2 := by
    rw [mul_assoc,norm_mul,Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left (hu 2 (xlog u)) (by norm_num)
  linarith [hu 3 (xlog u)]

theorem linear_pointwise (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (a b : ℝ) (ha : 0 < a) (hs : Function.support f ⊆ Icc a b)
    (B : ℝ) (hB : 0 ≤ B) (h0 : mass f 0 ≤ B) (h3 : mass f 3 ≤ B) (t : ℝ) :
    (1+|t|)*‖mellin f (t*I)‖ ≤ 4*B*(1+t^2)⁻¹ := by
  have hzero : ‖mellin f (t*I)‖ ≤ B := by simpa using (frequency_power f hf a b ha hs 0 t).trans h0
  have hcube := (frequency_power f hf a b ha hs 3 t).trans h3
  have ht : 0 ≤ |t| := abs_nonneg t
  rw [← sq_abs t]
  by_cases hh : |t| ≤ 1
  · apply (show (1+|t|)*‖mellin f (t*I)‖ ≤ 2*B by nlinarith [norm_nonneg (mellin f (t*I))]).trans
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity : 0 < 1+|t|^2)).mpr
    nlinarith [mul_nonneg hB (show 0 ≤ 1-|t|^2 by nlinarith)]
  · have ht1 : 1 ≤ |t| := le_of_lt (lt_of_not_ge hh)
    have ht0 : 0 < |t| := by linarith
    have hp : |t| * ‖mellin f (t*I)‖ ≤ B/|t|^2 := by
      apply (le_div_iff₀ (sq_pos_of_pos ht0)).mpr
      nlinarith only [hcube]
    calc
      _ ≤ 2*(|t| * ‖mellin f (t*I)‖) := by nlinarith [norm_nonneg (mellin f (t*I))]
      _ ≤ 2*(B/|t|^2) := mul_le_mul_of_nonneg_left hp (by norm_num)
      _ ≤ _ := by
        rw [← div_eq_mul_inv]
        apply (le_div_iff₀ (by positivity : 0 < 1+|t|^2)).mpr
        have hd : (B/|t|^2) * |t|^2 = B := by field_simp
        have hd' : B/|t|^2 ≤ B := div_le_self hB (by nlinarith)
        nlinarith

theorem linear_mass_bound (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (a b : ℝ) (ha : 0 < a) (hs : Function.support f ⊆ Icc a b)
    (B : ℝ) (hB : 0 ≤ B) (h0 : mass f 0 ≤ B) (h3 : mass f 3 ≤ B) :
    (∫ t : ℝ, (1+|t|)*‖mellin f (t*I)‖) ≤
      4*B*(∫ t : ℝ, (1+t^2)⁻¹) := by
  have hi := integrable_inv_one_add_sq.const_mul (4*B)
  apply (integral_mono_of_nonneg (Eventually.of_forall (fun t => by positivity)) hi
    (Eventually.of_forall (linear_pointwise f hf a b ha hs B hB h0 h3))).trans_eq
  exact integral_const_mul _ _

/-- The common dimensionless jet constants and logarithmic support width
completely determine the weighted Mellin mass bound. -/
theorem uniform_mass_from_scaled_jets (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hs : Function.support f ⊆ Icc a b)
    (U : ℕ → ℝ) (hU : ∀ n, 0 ≤ U n)
    (hu : ∀ n (x : ℝ), ‖(x:ℂ)^n*iteratedDeriv n f x‖ ≤ U n) :
    (∫ t : ℝ, (1+|t|)*‖mellin f (t*I)‖) ≤
      4*(Real.log (b/a)*(U 0+U 1+3*U 2+U 3))*(∫ t : ℝ, (1+t^2)⁻¹) := by
  have hm := mass_from_scaled_jets f hf a b ha hab hs U hu
  have hl : 0 ≤ Real.log (b/a) := Real.log_nonneg ((one_le_div ha).mpr hab)
  have hU0 := hU 0
  have hU1 := hU 1
  have hU2 := hU 2
  have hU3 := hU 3
  let B := Real.log (b/a)*(U 0+U 1+3*U 2+U 3)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have h0 : mass f 0 ≤ B := hm.1.trans (by dsimp [B]; gcongr; linarith [hU 1,hU 2,hU 3])
  have h3 : mass f 3 ≤ B := hm.2.trans (by dsimp [B]; gcongr; linarith [hU 0])
  exact linear_mass_bound f hf a b ha hs B hB h0 h3

theorem mass_from_jets (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hs : Function.support f ⊆ Icc a b)
    (U : ℕ → ℝ) (hU : ∀ n, 0 ≤ U n) (hu : ∀ n x, ‖iteratedDeriv n f x‖ ≤ U n) :
    mass f 0 ≤ Real.log (b/a)*U 0 ∧
      mass f 3 ≤ Real.log (b/a)*(b*U 1+3*b^2*U 2+b^3*U 3) := by
  refine ⟨mass_le f hf a b ha hab hs 0 (U 0) (by intro u huu; exact hu 0 (xlog u)),?_⟩
  apply mass_le f hf a b ha hab hs 3
  intro u huu
  have hx : 0 < xlog u := Real.exp_pos _
  have hxb : xlog u ≤ b := by
    have hh := Real.exp_le_exp.mpr (show -u ≤ Real.log b by linarith [huu.1])
    exact hh.trans_eq (Real.exp_log (ha.trans_le hab))
  rw [log_third f hf]
  dsimp only
  have hh := (norm_sub_le
    (-(xlog u:ℂ)*iteratedDeriv 1 f (xlog u)-3*(xlog u:ℂ)^2*iteratedDeriv 2 f (xlog u))
    ((xlog u:ℂ)^3*iteratedDeriv 3 f (xlog u))).trans
      (add_le_add (norm_sub_le _ _) le_rfl)
  apply hh.trans
  simp only [norm_mul,norm_neg,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hx,Complex.norm_ofNat]
  calc
    _ ≤ xlog u*U 1+3*(xlog u)^2*U 2+(xlog u)^3*U 3 := by gcongr <;> apply hu
    _ ≤ _ := by gcongr <;> exact hU _

/-- Ordinary-jet version of the old [1,2] result, with explicit log(b/a).
The scaled-jet version avoids the b,b^2,b^3 factors altogether. -/
theorem uniform_mass_from_jets (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hs : Function.support f ⊆ Icc a b)
    (U : ℕ → ℝ) (hU : ∀ n, 0 ≤ U n) (hu : ∀ n x, ‖iteratedDeriv n f x‖ ≤ U n) :
    (∫ t : ℝ, (1+|t|)*‖mellin f (t*I)‖) ≤
      4*(Real.log (b/a)*(U 0+b*U 1+3*b^2*U 2+b^3*U 3))*(∫ t : ℝ, (1+t^2)⁻¹) := by
  have hm := mass_from_jets f hf a b ha hab hs U hU hu
  have hl : 0 ≤ Real.log (b/a) := Real.log_nonneg ((one_le_div ha).mpr hab)
  have hb : 0 < b := ha.trans_le hab
  have hU0 := hU 0
  have hU1 := hU 1
  have hU2 := hU 2
  have hU3 := hU 3
  apply linear_mass_bound f hf a b ha hs _ (by positivity)
  · apply hm.1.trans
    gcongr
    have hp : 0 ≤ b*U 1+3*b^2*U 2+b^3*U 3 := by positivity
    linarith
  · apply hm.2.trans
    gcongr
    linarith [hU 0]

#print axioms mass_from_jets
#print axioms uniform_mass_from_jets
#print axioms linear_mass_bound
#print axioms frequency_power
#print axioms log_jet_support
#print axioms mass_le
#print axioms mass_from_scaled_jets
#print axioms linear_pointwise
#print axioms uniform_mass_from_scaled_jets
end XiPrime8845.PRZZMellinInterval
