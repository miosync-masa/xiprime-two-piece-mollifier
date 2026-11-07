import PRZZZeroOuterMellin
import PRZZCosineGapCorrection

/-! Exact normalization of the actual reciprocal zero row. The factor
P^sigma is essential for the arithmetic coefficient reflection. -/
noncomputable section
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZZeroNormalization
open PRZZCosineMellinCore PRZZCosineMellin PRZZCosineGapMellin
set_option maxHeartbeats 6000000

theorem evaluated_mul_square (sigma : ℂ) (X delta tau : ℝ) (hX : 0 < X) (hd : 0 < delta) :
    evaluated sigma (X*delta^2) tau = exp (-(2*line tau)*(Real.log delta:ℂ))*evaluated sigma X tau := by
  rw [PRZZCosineTimeMellin.evaluated_scale sigma (X*delta^2) tau (by positivity),
    PRZZCosineTimeMellin.evaluated_scale sigma X tau hX,
    Real.log_mul hX.ne' (pow_ne_zero 2 hd.ne'),Real.log_pow]
  push_cast
  rw [← mul_assoc,← exp_add]
  congr 1
  ring

theorem gap_normalization (sigma : ℂ) (P t tau : ℝ) (n : ℕ) (hP : 0 < P) (ht : 0 < t) :
    exp (-sigma*(Real.log (t*((n+1:ℕ):ℝ)/P):ℂ))*
      evaluated sigma ((2*Real.pi*P/t)*(t*((n+1:ℕ):ℝ)/P)^2) tau =
      exp (sigma*(Real.log P:ℂ))*exp (-sigma*(Real.log t:ℂ))*
        term sigma (2*Real.pi*t/P) n tau := by
  let delta : ℝ := (n+1:ℕ)
  have hd : 0 < delta := by dsimp [delta]; positivity
  have hscale : (2*Real.pi*P/t)*(t*delta/P)^2 = (2*Real.pi*t/P)*delta^2 := by field_simp
  change exp (-sigma*(Real.log (t*delta/P):ℂ))*evaluated sigma ((2*Real.pi*P/t)*(t*delta/P)^2) tau = _
  rw [hscale,evaluated_mul_square sigma (2*Real.pi*t/P) delta tau (by positivity) hd]
  have hc : (((n+1:ℕ):ℂ)^(exponent sigma tau))⁻¹ =
      exp (-(exponent sigma tau)*(Real.log delta:ℂ)) := by
    have hnC : ((n+1:ℕ):ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
    rw [cpow_def_of_ne_zero hnC,← Complex.ofReal_natCast,
      ← Complex.ofReal_log hd.le,← exp_neg]
    congr 1
    ring
  have hterm : term sigma (2*Real.pi*t/P) n tau = evaluated sigma (2*Real.pi*t/P) tau*
      exp (-(exponent sigma tau)*(Real.log delta:ℂ)) := by
    change evaluated sigma (2*Real.pi*t/P) tau*((((n+1:ℕ):ℂ)^(exponent sigma tau))⁻¹) = _
    rw [hc]
  rw [hterm,Real.log_div (mul_ne_zero ht.ne' hd.ne') hP.ne',Real.log_mul ht.ne' hd.ne']
  push_cast
  have he : exp (-sigma*((Real.log t:ℂ)+(Real.log delta:ℂ)-(Real.log P:ℂ)))*
      exp (-(2*line tau)*(Real.log delta:ℂ)) =
      exp (sigma*(Real.log P:ℂ))*exp (-sigma*(Real.log t:ℂ))*
        exp (-(exponent sigma tau)*(Real.log delta:ℂ)) := by
    simp only [← exp_add]
    congr 1
    unfold exponent
    ring
  calc
    _ = (exp (-sigma*((Real.log t:ℂ)+(Real.log delta:ℂ)-(Real.log P:ℂ)))*
      exp (-(2*line tau)*(Real.log delta:ℂ)))*evaluated sigma (2*Real.pi*t/P) tau := by ring
    _ = _ := by rw [he]; ring

theorem value_normalization (Phi : ℝ → ℂ) (T P t : ℝ) (sigma : ℂ) (n : ℕ)
    (hP : 0 < P) (ht : 0 < t) :
    PRZZZeroRowMellin.value Phi T P sigma ((n+1:ℕ):ℝ) t =
      -(exp (sigma*(Real.log P:ℂ))*(1/(2*Real.pi):ℂ))*
        (Phi (t/T)*exp (-sigma*(Real.log t:ℂ)))*
          (∫ tau : ℝ, term sigma (2*Real.pi*t/P) n tau) := by
  unfold PRZZZeroRowMellin.value
  have he : exp (-sigma*(Real.log (t*((n+1:ℕ):ℝ)/P):ℂ))*
      (∫ tau : ℝ, evaluated sigma ((2*Real.pi*P/t)*(t*((n+1:ℕ):ℝ)/P)^2) tau) =
      (exp (sigma*(Real.log P:ℂ))*exp (-sigma*(Real.log t:ℂ)))*
        ∫ tau : ℝ, term sigma (2*Real.pi*t/P) n tau := by
    rw [← integral_const_mul,← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall (fun tau => gap_normalization sigma P t tau n hP ht))
  linear_combination (norm := ring_nf) (-(1/(2*Real.pi):ℂ)*Phi (t/T))*he

theorem coefficient_reflection (a : ℕ → ℂ) (F1 F2 : ℝ → ℂ) (alpha beta : ℂ)
    (d u v : ℕ) (hu : 0 < u) (hv : 0 < v) :
    PRZZDiagonalAssembly.coefficient a F1 F2 alpha beta d u v *
      exp ((alpha+beta)*(Real.log ((u:ℝ)*v):ℂ)) =
      PRZZDiagonalAssembly.coefficient a F1 F2 (-beta) (-alpha) d u v := by
  have huR : (0:ℝ) < u := by exact_mod_cast hu
  have hvR : (0:ℝ) < v := by exact_mod_cast hv
  have he : PRZZPowerJets.power (1+beta) u*PRZZPowerJets.power (1+alpha) v*
      exp ((alpha+beta)*(Real.log ((u:ℝ)*v):ℂ)) =
      PRZZPowerJets.power (1+-alpha) u*PRZZPowerJets.power (1+-beta) v := by
    unfold PRZZPowerJets.power
    rw [Real.log_mul huR.ne' hvR.ne']
    push_cast
    simp only [← exp_add]
    congr 1
    ring
  unfold PRZZDiagonalAssembly.coefficient
  linear_combination (norm := ring_nf)
    (F1 (d*u)*F2 (d*v)*a (d*u)*star (a (d*v))*PRZZPowerJets.power 1 d)*he

#print axioms evaluated_mul_square
#print axioms gap_normalization
#print axioms value_normalization
#print axioms coefficient_reflection
end XiPrime8845.PRZZZeroNormalization
