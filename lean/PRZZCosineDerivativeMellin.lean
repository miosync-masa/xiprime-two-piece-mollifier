import PRZZCosineFiniteFubini
import PRZZCosineSpatialImproper
import PRZZSourceWLine
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Differentiate the actual positive-line sourceW representation under
the integral. All Gaussian domination is supplied, not a Fubini premise. -/
noncomputable section
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZCosineDerivativeMellin
open PRZZCosineMellinCore PRZZCosineMellin PRZZCosineSpatialJets
set_option maxHeartbeats 6000000

def cap : ℕ → ℝ
  | 0 => 1
  | n+1 => cap n*(6+n)

def kernel (sigma : ℂ) (X : ℝ) (n : ℕ) (tau y : ℝ) : ℂ :=
  coefficient sigma X tau*exp ((line tau)^2)*
    PRZZPowerJets.jet (1-exponent sigma tau) n y

theorem cap_pos (n : ℕ) : 0 < cap n := by
  induction n with
  | zero => norm_num [cap]
  | succ n ih => simp only [cap]; positivity

theorem coeff_bound (sigma : ℂ) (hn : ‖sigma‖ ≤ 1/8) (n : ℕ) (tau : ℝ) :
    ‖PRZZPowerJets.coeff (1-exponent sigma tau) n‖ ≤ cap n*(1+|tau|)^n := by
  let V := 1+|tau|
  have hV : 1 ≤ V := by dsimp [V]; linarith [abs_nonneg tau]
  have hz : ‖exponent sigma tau‖ ≤ 5*V := by
    have hh := norm_add_le (2*line tau) sigma
    norm_num [norm_mul] at hh
    have hl := (line_bounds tau).2
    dsimp [exponent,V]; linarith
  induction n with
  | zero => simp [PRZZPowerJets.coeff,cap]
  | succ n ih =>
    have hp : ‖-(1-exponent sigma tau)-(n:ℂ)‖ ≤ (6+(n:ℝ))*V := by
      have he : -(1-exponent sigma tau)-(n:ℂ) = exponent sigma tau-((1:ℂ)+n) := by ring
      rw [he]
      have hh := norm_sub_le (exponent sigma tau) ((1:ℂ)+n)
      have hnat : ‖(1:ℂ)+(n:ℂ)‖ = 1+(n:ℝ) := by
        rw [← Complex.ofReal_natCast,← Complex.ofReal_one,← Complex.ofReal_add,
          Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      rw [hnat] at hh
      nlinarith [mul_nonneg (show 0 ≤ (n:ℝ)+1 by positivity) (sub_nonneg.mpr hV)]
    rw [PRZZPowerJets.coeff,norm_mul,cap,pow_succ]
    exact (mul_le_mul ih hp (norm_nonneg _) (mul_nonneg (cap_pos n).le (by positivity))).trans_eq (by dsimp [V]; ring)

theorem kernel_bound (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (X : ℝ) (hX : 0 < X) (n : ℕ) (tau y : ℝ) (hy : 0 < y) :
    ‖kernel sigma X n tau y‖ ≤
      (cap n*Real.exp 2*X^(-5/4:ℝ)*(1+16/‖sigma‖^2))*
        ((1+|tau|)^(n+2)*Real.exp (-tau^2))*y^(3/2+sigma.re-n) := by
  have hj : ‖PRZZPowerJets.jet (1-exponent sigma tau) n y‖ ≤
      (cap n*(1+|tau|)^n)*y^(3/2+sigma.re-n) := by
    rw [PRZZPowerJets.jet,norm_div,norm_mul,norm_pow,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hy]
    have he : ‖PRZZPowerJets.power (1-exponent sigma tau) y‖ = y^(3/2+sigma.re) := by
      rw [PRZZPowerJets.power,norm_exp,Real.rpow_def_of_pos hy]
      congr 1
      simp [exponent,line]
      ring
    rw [he,Real.rpow_sub hy,Real.rpow_natCast]
    exact (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (coeff_bound sigma hn n tau)
        (Real.rpow_nonneg hy.le _)) (pow_nonneg hy.le n)).trans_eq (by ring)
  have he : ‖exp ((line tau)^2)‖ ≤ Real.exp 2*Real.exp (-tau^2) := by
    rw [norm_exp,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    simp [line,pow_two,mul_re]
    nlinarith
  rw [kernel,norm_mul,norm_mul]
  apply (mul_le_mul
    (mul_le_mul (coefficient_cap sigma hs X tau hX) he (norm_nonneg _) (by positivity))
    hj (by positivity) (by positivity)).trans_eq
  rw [pow_add]
  ring

theorem kernel_measurable (sigma : ℂ) (X : ℝ) (hX : 0 < X) (n : ℕ) (y : ℝ) :
    AEStronglyMeasurable (fun tau : ℝ => kernel sigma X n tau y) := by
  have hc := (coefficient_continuous sigma X hX).measurable
  have hp : ∀ n : ℕ, Continuous (fun tau : ℝ => PRZZPowerJets.coeff (1-exponent sigma tau) n) := by
    intro n
    induction n with
    | zero => simp only [PRZZPowerJets.coeff]; fun_prop
    | succ n ih =>
      simp only [PRZZPowerJets.coeff]
      exact ih.mul (by unfold exponent line; fun_prop)
  have hh := (hp n).measurable
  exact (by unfold kernel PRZZPowerJets.jet PRZZPowerJets.power exponent line
            fun_prop : Measurable (fun tau : ℝ => kernel sigma X n tau y)).aestronglyMeasurable

theorem kernel_integrable (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (X : ℝ) (hX : 0 < X) (n : ℕ) (y : ℝ) (hy : 0 < y) :
    Integrable (fun tau : ℝ => kernel sigma X n tau y) := by
  apply (((gaussian_power_integrable (n+2)).const_mul
    (cap n*Real.exp 2*X^(-5/4:ℝ)*(1+16/‖sigma‖^2))).mul_const
      (y^(3/2+sigma.re-n))).mono' (kernel_measurable sigma X hX n y)
  exact Eventually.of_forall (fun tau => kernel_bound sigma hs hn X hX n tau y hy)

theorem kernel_deriv (sigma : ℂ) (X : ℝ) (n : ℕ) (tau y : ℝ) (hy : 0 < y) :
    HasDerivAt (kernel sigma X n tau) (kernel sigma X (n+1) tau y) y :=
  (PRZZPowerJets.jet_deriv (1-exponent sigma tau) n y hy).const_mul _

theorem integral_deriv (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (X : ℝ) (hX : 0 < X) (n : ℕ) (y : ℝ) (hy : 0 < y) :
    HasDerivAt (fun u : ℝ => ∫ tau : ℝ, kernel sigma X n tau u)
      (∫ tau : ℝ, kernel sigma X (n+1) tau y) y := by
  let e : ℝ := 3/2+sigma.re-(n+1)
  have hp : ContinuousOn (fun u : ℝ => u^e) (Icc (y/2) (2*y)) := by
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt (by linarith [hu.1])
    exact (Real.continuousAt_rpow_const u e (Or.inl hu0)).continuousWithinAt
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hp
  let C := cap (n+1)*Real.exp 2*X^(-5/4:ℝ)*(1+16/‖sigma‖^2)
  have hb : Integrable (fun tau : ℝ => (C*((1+|tau|)^((n+1)+2)*Real.exp (-tau^2)))*B) :=
    ((gaussian_power_integrable ((n+1)+2)).const_mul C).mul_const B
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds (show y/2 < y by linarith) (show y < 2*y by linarith))
    (Eventually.of_forall (fun u => kernel_measurable sigma X hX n u))
    (kernel_integrable sigma hs hn X hX n y hy)
    (kernel_measurable sigma X hX (n+1) y)
    (Eventually.of_forall (fun tau u (hu : u ∈ Ioo (y/2) (2*y)) => show
      ‖kernel sigma X (n+1) tau u‖ ≤ (C*((1+|tau|)^((n+1)+2)*Real.exp (-tau^2)))*B from by
        have hu0 : 0 < u := by linarith [hu.1]
        apply (kernel_bound sigma hs hn X hX (n+1) tau u hu0).trans
        apply mul_le_mul_of_nonneg_left _ (by
          have hc := cap_pos (n+1)
          change 0 ≤ C*((1+|tau|)^((n+1)+2)*Real.exp (-tau^2))
          dsimp [C]; positivity)
        exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs,e,Nat.cast_add,Nat.cast_one] using hB u ⟨hu.1.le,hu.2.le⟩)))
    hb (Eventually.of_forall (fun tau u (hu : u ∈ Ioo (y/2) (2*y)) =>
      kernel_deriv sigma X n tau u (by linarith [hu.1])))
  exact hd.2

theorem primitive_mellin (sigma : ℂ) (hs : sigma ≠ 0) (X y : ℝ)
    (hX : 0 < X) (hy : 0 < y) :
    primitive (sigma-1) sigma X y = (1/(2*Real.pi):ℂ)*
      ∫ tau : ℝ, kernel sigma X 0 tau y := by
  rw [primitive,PRZZCosineSpatialJets.arg,PRZZSourceWLine.sourceW_shift sigma hs (X/y^2) (5/4)
    (by positivity) (by norm_num)]
  rw [mul_left_comm,← integral_const_mul]
  congr 1
  apply integral_congr_ae
  apply Eventually.of_forall
  intro tau
  have he : power (sigma-1) y*((X/y^2:ℝ):ℂ)^(-line tau) =
      (X:ℂ)^(-line tau)*PRZZPowerJets.power (1-exponent sigma tau) y := by
    rw [cpow_def_of_ne_zero (by exact_mod_cast (show 0 < X/y^2 by positivity).ne'),
      cpow_def_of_ne_zero (by exact_mod_cast hX.ne'),
      ← Complex.ofReal_log (show 0 ≤ X/y^2 by positivity),← Complex.ofReal_log hX.le]
    rw [Real.log_div hX.ne' (pow_ne_zero 2 hy.ne'),Real.log_pow]
    unfold power PRZZPowerJets.power
    rw [← exp_add,← exp_add]
    congr 1
    push_cast
    unfold exponent
    ring
  change power (sigma-1) y*PRZZSourceWLine.weight sigma (X/y^2) (5/4) tau = _
  unfold PRZZSourceWLine.weight PRZZSourceWLine.line
  change power (sigma-1) y*(((X/y^2:ℝ):ℂ)^(-line tau)*exp ((line tau)^2)*
    PRZZDyadicEnvelope.annihilator sigma (line tau)/line tau) = _
  simp only [kernel,PRZZPowerJets.jet,PRZZPowerJets.coeff,pow_zero,div_one,one_mul,coefficient]
  linear_combination (norm := ring_nf)
    (exp ((line tau)^2)*PRZZDyadicEnvelope.annihilator sigma (line tau)/line tau)*he

theorem first_mellin (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (X y : ℝ) (hX : 0 < X) (hy : 0 < y) :
    first (sigma-1) sigma X y = (1/(2*Real.pi):ℂ)*
      ∫ tau : ℝ, kernel sigma X 1 tau y := by
  have hd := (integral_deriv sigma hs hn X hX 0 y hy).const_mul (1/(2*Real.pi):ℂ)
  have he : (fun u : ℝ => (1/(2*Real.pi):ℂ)*∫ tau : ℝ, kernel sigma X 0 tau u)
      =ᶠ[𝓝 y] primitive (sigma-1) sigma X := by
    filter_upwards [eventually_gt_nhds hy] with u hu
    exact (primitive_mellin sigma hs X u hX hu).symm
  exact (primitive_deriv (sigma-1) sigma hs X y hX hy).unique (hd.congr_of_eventuallyEq he.symm)

theorem second_mellin (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (X y : ℝ) (hX : 0 < X) (hy : 0 < y) :
    second (sigma-1) sigma X y = (1/(2*Real.pi):ℂ)*
      ∫ tau : ℝ, kernel sigma X 2 tau y := by
  have hd := (integral_deriv sigma hs hn X hX 1 y hy).const_mul (1/(2*Real.pi):ℂ)
  have he : (fun u : ℝ => (1/(2*Real.pi):ℂ)*∫ tau : ℝ, kernel sigma X 1 tau u)
      =ᶠ[𝓝 y] first (sigma-1) sigma X := by
    filter_upwards [eventually_gt_nhds hy] with u hu
    exact (first_mellin sigma hs hn X u hX hu).symm
  exact (first_deriv (sigma-1) sigma hs X y hX hy).unique (hd.congr_of_eventuallyEq he.symm)

theorem kernel_second_density (sigma : ℂ) (X tau y : ℝ) (hy : 0 < y) :
    kernel sigma X 2 tau y*cos (y:ℂ) = PRZZCosineFiniteFubini.density sigma X tau y := by
  have hl : exp (Real.log y:ℂ) = (y:ℂ) := by rw [← Complex.ofReal_exp,Real.exp_log hy]
  have he : exp ((exponent sigma tau-1)*(Real.log y:ℂ)) =
      exp ((exponent sigma tau-3)*(Real.log y:ℂ))*(y:ℂ)^2 := by
    rw [show (exponent sigma tau-1)*(Real.log y:ℂ) =
      (exponent sigma tau-3)*(Real.log y:ℂ)+((Real.log y:ℂ)+(Real.log y:ℂ)) by ring,
      exp_add,exp_add,hl]
    ring
  unfold kernel PRZZPowerJets.jet PRZZPowerJets.coeff PRZZPowerJets.power
    PRZZCosineFiniteFubini.density
  norm_num only [PRZZPowerJets.coeff,Nat.cast_zero,Nat.cast_one,sub_zero,one_mul]
  rw [show -(1-exponent sigma tau) = exponent sigma tau-1 by ring,he]
  have hyC : (y:ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  field_simp [hyC]
  ring

/-- The literal second sourceW derivative, not an assumed identification. -/
theorem second_cosine_mellin (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (X y : ℝ) (hX : 0 < X) (hy : 0 < y) :
    second (sigma-1) sigma X y*cos (y:ℂ) = (1/(2*Real.pi):ℂ)*
      ∫ tau : ℝ, PRZZCosineFiniteFubini.density sigma X tau y := by
  rw [second_mellin sigma hs hn X y hX hy,mul_assoc,← integral_mul_const]
  congr 1
  exact integral_congr_ae (Eventually.of_forall (fun tau => kernel_second_density sigma X tau y hy))

theorem actual_finite_exchange (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (X R : ℝ) (hX : 0 < X) (hR : 0 ≤ R) :
    (∫ y in Ioc (0:ℝ) R, second (sigma-1) sigma X y*cos (y:ℂ)) =
      (1/(2*Real.pi):ℂ)*∫ tau : ℝ, truncated sigma X R tau := by
  rw [← PRZZCosineFiniteFubini.finite_exchange sigma hs hn X R hX hR,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
  exact second_cosine_mellin sigma hs hn X y hX hy.1

theorem actual_integral (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (X : ℝ) (hX : 0 < X) :
    (∫ y in Ioi (0:ℝ), second (sigma-1) sigma X y*cos (y:ℂ)) =
      (1/(2*Real.pi):ℂ)*∫ tau : ℝ, evaluated sigma X tau := by
  have hactual := intervalIntegral_tendsto_integral_Ioi (0:ℝ)
    (PRZZCosineSpatialImproper.second_integrable sigma hs hn X hX).2 tendsto_id
  have hm := (integral_exchange sigma hs hn X hX).const_mul (1/(2*Real.pi):ℂ)
  apply tendsto_nhds_unique hactual
  apply hm.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with R hR
  simp only [id_eq]
  rw [intervalIntegral.integral_of_le hR]
  exact (actual_finite_exchange sigma hs hn X R hX hR).symm

theorem actual_improper (sigma : ℂ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (X : ℝ) (hX : 0 < X) :
    Tendsto (fun R : ℝ => ∫ y in (1/R)..R, primitive (sigma-1) sigma X y*cos (y:ℂ)) atTop
      (𝓝 (-((1/(2*Real.pi):ℂ)*∫ tau : ℝ, evaluated sigma X tau))) := by
  rw [← actual_integral sigma hs hn X hX]
  exact PRZZCosineSpatialImproper.improper_cosine sigma hs hn X hX

#print axioms cap_pos
#print axioms coeff_bound
#print axioms kernel_bound
#print axioms kernel_measurable
#print axioms kernel_integrable
#print axioms kernel_deriv
#print axioms integral_deriv
#print axioms primitive_mellin
#print axioms first_mellin
#print axioms second_mellin
#print axioms kernel_second_density
#print axioms second_cosine_mellin
#print axioms actual_finite_exchange
#print axioms actual_integral
#print axioms actual_improper
end XiPrime8845.PRZZCosineDerivativeMellin
