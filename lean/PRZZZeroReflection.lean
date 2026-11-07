import PRZZCoupledAFE

/-! The Gamma/cosine functional equation in [58], section 3.2.1.
This identifies the actual Mellin integrand after cosine transformation
with the reflected diagonal integrand. It does not assume or prove the
preceding improper cosine-Mellin interchange or Delta/M cutoff removal. -/
noncomputable section
open Complex MeasureTheory Set
namespace XiPrime8845.PRZZZeroReflection
open PRZZDyadicEnvelope PRZZDiagonalMellin
set_option maxHeartbeats 3000000

theorem cosine_functional (z : ℂ) (hz : 0 < z.re) (hz1 : z ≠ 1) :
    2*riemannZeta z*Gamma z*cos ((Real.pi:ℂ)*(z-2)/2) =
      -((2*Real.pi:ℝ):ℂ)^z*riemannZeta (1-z) := by
  have hneg : ∀ n : ℕ, z ≠ -(n:ℂ) := by
    intro n he
    have hh := congrArg Complex.re he
    simp only [neg_re,natCast_re] at hh
    have hn : (0:ℝ) ≤ n := by positivity
    linarith
  have he := riemannZeta_one_sub hneg hz1
  have hc : cos ((Real.pi:ℂ)*(z-2)/2) = -cos ((Real.pi:ℂ)*z/2) := by
    rw [show (Real.pi:ℂ)*(z-2)/2 = (Real.pi:ℂ)*z/2-Real.pi by ring,cos_sub_pi]
  have hp : (((2*Real.pi:ℝ):ℂ)^z) ≠ 0 := by
    rw [cpow_def_of_ne_zero (by exact_mod_cast (show 2*Real.pi ≠ 0 by positivity))]
    exact exp_ne_zero _
  rw [hc,he]
  push_cast
  rw [cpow_neg]
  field_simp

def cosineKernel (sigma : ℂ) (P t : ℝ) (s : ℂ) : ℂ :=
  (2*riemannZeta (2*s+sigma)*Gamma (2*s+sigma)*
    cos ((Real.pi:ℂ)*(2*s+sigma-2)/2))*
      ((2*Real.pi*t/P:ℝ):ℂ)^(-s)*exp (s^2)*annihilator sigma s/s

theorem positive_power_identity (sigma s : ℂ) (P t : ℝ) (hP : 0 < P) (ht : 0 < t) :
    ((t:ℂ)^(-sigma))*((2*Real.pi:ℝ):ℂ)^(2*s+sigma)*
      ((2*Real.pi*t/P:ℝ):ℂ)^(-s) =
      ((t/(2*Real.pi):ℝ):ℂ)^(-sigma)*((t/(2*Real.pi*P):ℝ):ℂ)^(-s) := by
  have hc : 0 < 2*Real.pi := by positivity
  rw [cpow_def_of_ne_zero (by exact_mod_cast ht.ne'),
    cpow_def_of_ne_zero (by exact_mod_cast hc.ne'),
    cpow_def_of_ne_zero (by exact_mod_cast (ne_of_gt (show 0 < 2*Real.pi*t/P by positivity))),
    cpow_def_of_ne_zero (by exact_mod_cast (ne_of_gt (show 0 < t/(2*Real.pi) by positivity))),
    cpow_def_of_ne_zero (by exact_mod_cast (ne_of_gt (show 0 < t/(2*Real.pi*P) by positivity)))]
  rw [← Complex.ofReal_log ht.le,← Complex.ofReal_log hc.le,
    ← Complex.ofReal_log (show 0 ≤ 2*Real.pi*t/P by positivity),
    ← Complex.ofReal_log (show 0 ≤ t/(2*Real.pi) by positivity),
    ← Complex.ofReal_log (show 0 ≤ t/(2*Real.pi*P) by positivity)]
  simp only [Real.log_div (by positivity : 2*Real.pi*t ≠ 0) hP.ne',
    Real.log_mul hc.ne' ht.ne',Real.log_div ht.ne' hc.ne',
    Real.log_div ht.ne' (by positivity : 2*Real.pi*P ≠ 0),Real.log_mul hc.ne' hP.ne',
    Complex.ofReal_sub,Complex.ofReal_add,← Complex.exp_add]
  congr 1
  ring

/-- The reflection is to the opposite shift branch, including the sign
from 1/(-s), the full Gaussian and the source annihilator. -/
theorem reflected_kernel (sigma s : ℂ) (P t : ℝ) (hP : 0 < P) (ht : 0 < t)
    (hz : 0 < (2*s+sigma).re) (hz1 : 2*s+sigma ≠ 1) :
    (t:ℂ)^(-sigma)*cosineKernel sigma P t s =
      ((t/(2*Real.pi):ℝ):ℂ)^(-sigma)*
        integrand (-sigma) (t/(2*Real.pi*P)) (-s) := by
  have ha : annihilator (-sigma) (-s) = annihilator sigma s := by
    unfold annihilator
    simp only [neg_sq,mul_neg,neg_sq]
  have he := cosine_functional (2*s+sigma) hz hz1
  unfold cosineKernel
  rw [he]
  unfold integrand amplitude
  rw [ha,neg_sq,show 1+ -sigma+2*(-s) = 1-(2*s+sigma) by ring]
  have hp := positive_power_identity sigma s P t hP ht
  calc
    _ = -( (t:ℂ)^(-sigma)*((2*Real.pi:ℝ):ℂ)^(2*s+sigma)*
        ((2*Real.pi*t/P:ℝ):ℂ)^(-s)) *
        (exp (s^2)*annihilator sigma s/s)*riemannZeta (1-(2*s+sigma)) := by ring
    _ = _ := by rw [hp]; ring

/-- The whole Re s=1/8 line is in the regular functional-equation strip
for all shifts in the fixed small disc. No Gamma-pole premise remains. -/
theorem reflected_vertical (sigma : ℂ) (hn : ‖sigma‖ ≤ 1/8)
    (P t y : ℝ) (hP : 0 < P) (ht : 0 < t) :
    let s : ℂ := (1/8:ℝ)+(y:ℂ)*I
    (t:ℂ)^(-sigma)*cosineKernel sigma P t s =
      ((t/(2*Real.pi):ℝ):ℂ)^(-sigma)*
        integrand (-sigma) (t/(2*Real.pi*P)) (-s) := by
  dsimp only
  have hr := abs_le.mp ((abs_re_le_norm sigma).trans hn)
  apply reflected_kernel sigma _ P t hP ht
  · simp only [add_re,mul_re,ofReal_re,ofReal_im,I_re,I_im,mul_zero,mul_one,sub_zero]
    norm_num
    linarith [hr.1]
  · intro he
    have hh := congrArg Complex.re he
    simp at hh
    linarith [hr.2]

/-- Reflection of the entire vertical Mellin integral. The reversal of
the imaginary coordinate is measure preserving and supplies no extra sign. -/
theorem cosine_vertical_integrable (sigma : ℂ) (hs : sigma ≠ 0)
    (hn : ‖sigma‖ ≤ 1/8) (P t : ℝ) (hP : 0 < P) (ht : 0 < t) :
    Integrable (fun y : ℝ => cosineKernel sigma P t ((1/8:ℝ)+(y:ℂ)*I)) := by
  have hi := PRZZDiagonalContour.vertical_integrable (-sigma) (neg_ne_zero.mpr hs)
    (by simpa using hn) (t/(2*Real.pi*P)) (-(1/8)) (by positivity) (Or.inl rfl)
  have hr := hi.comp_mul_left' (by norm_num : (-1:ℝ) ≠ 0)
  have hp : (t:ℂ)^(-sigma) ≠ 0 := by
    rw [cpow_def_of_ne_zero (by exact_mod_cast ht.ne')]
    exact exp_ne_zero _
  have he (y : ℝ) : (t:ℂ)^(-sigma)*cosineKernel sigma P t ((1/8:ℝ)+(y:ℂ)*I) =
      ((t/(2*Real.pi):ℝ):ℂ)^(-sigma)*
        integrand (-sigma) (t/(2*Real.pi*P)) ((-(1/8:ℝ):ℂ)+((-y:ℝ):ℂ)*I) := by
    have hh := reflected_vertical sigma hn P t y hP ht
    dsimp only at hh
    rw [show -((1/8:ℝ)+(y:ℂ)*I) =
      ((-(1/8:ℝ):ℂ)+((-y:ℝ):ℂ)*I) by push_cast; ring] at hh
    exact hh
  have hh : Integrable (fun y : ℝ => (t:ℂ)^(-sigma)*
      cosineKernel sigma P t ((1/8:ℝ)+(y:ℂ)*I)) := by
    simp_rw [he]
    simpa only [neg_one_mul,Complex.ofReal_neg] using
      hr.const_mul (((t/(2*Real.pi):ℝ):ℂ)^(-sigma))
  simpa only [← mul_assoc,inv_mul_cancel₀ hp,one_mul] using hh.const_mul ((t:ℂ)^(-sigma))⁻¹

theorem reflected_integral (sigma : ℂ) (hn : ‖sigma‖ ≤ 1/8)
    (P t : ℝ) (hP : 0 < P) (ht : 0 < t) :
    (t:ℂ)^(-sigma)*(1/(2*Real.pi):ℂ)*
        (∫ y : ℝ, cosineKernel sigma P t ((1/8:ℝ)+(y:ℂ)*I)) =
      ((t/(2*Real.pi):ℝ):ℂ)^(-sigma)*(1/(2*Real.pi):ℂ)*
        (∫ y : ℝ, integrand (-sigma) (t/(2*Real.pi*P))
          ((-(1/8:ℝ):ℂ)+(y:ℂ)*I)) := by
  have he : (fun y : ℝ => (t:ℂ)^(-sigma)*
      cosineKernel sigma P t ((1/8:ℝ)+(y:ℂ)*I)) =
      (fun y : ℝ => ((t/(2*Real.pi):ℝ):ℂ)^(-sigma)*
        integrand (-sigma) (t/(2*Real.pi*P)) ((-(1/8:ℝ):ℂ)+((-y:ℝ):ℂ)*I)) := by
    funext y
    have hh := reflected_vertical sigma hn P t y hP ht
    dsimp only at hh
    rw [show -((1/8:ℝ)+(y:ℂ)*I) =
      ((-(1/8:ℝ):ℂ)+((-y:ℝ):ℂ)*I) by push_cast; ring] at hh
    exact hh
  have hneg := MeasureTheory.Measure.integral_comp_mul_left
    (fun y : ℝ => integrand (-sigma) (t/(2*Real.pi*P))
      ((-(1/8:ℝ):ℂ)+(y:ℂ)*I)) (-1)
  simp only [neg_one_mul,inv_neg,inv_one,abs_neg,abs_one,one_smul] at hneg
  calc
    _ = (1/(2*Real.pi):ℂ)*(∫ y : ℝ, (t:ℂ)^(-sigma)*
        cosineKernel sigma P t ((1/8:ℝ)+(y:ℂ)*I)) := by
      rw [integral_const_mul]; ring
    _ = _ := by rw [he,integral_const_mul,hneg]; ring

/-- The cosine Mellin integral is exactly the opposite diagonal correction,
not an absolute-value estimate. Identification with the original zero
Fourier integral is still a separate improper-transform theorem. -/
theorem cosine_diagonal_correction (sigma : ℂ) (hs : sigma ≠ 0)
    (hn : ‖sigma‖ ≤ 1/8) (P t : ℝ) (hP : 0 < P) (ht : 0 < t) :
    (t:ℂ)^(-sigma)*(1/(2*Real.pi):ℂ)*
        (∫ y : ℝ, cosineKernel sigma P t ((1/8:ℝ)+(y:ℂ)*I)) =
      ((t/(2*Real.pi):ℝ):ℂ)^(-sigma)*
        (diagonal (-sigma) (t/(2*Real.pi*P))-riemannZeta (1-sigma)) := by
  rw [reflected_integral sigma hn P t hP ht]
  have hh := PRZZDiagonalContour.shifted_identity (-sigma) (neg_ne_zero.mpr hs)
    (by simpa using hn) (t/(2*Real.pi*P)) (by positivity)
  simpa only [sub_eq_add_neg,mul_assoc] using
    congrArg (fun z : ℂ => ((t/(2*Real.pi):ℝ):ℂ)^(-sigma)*z) hh.symm

theorem cosine_diagonal_balance (sigma : ℂ) (hs : sigma ≠ 0)
    (hn : ‖sigma‖ ≤ 1/8) (P t : ℝ) (hP : 0 < P) (ht : 0 < t) :
    ((t/(2*Real.pi):ℝ):ℂ)^(-sigma)*diagonal (-sigma) (t/(2*Real.pi*P))-
      (t:ℂ)^(-sigma)*(1/(2*Real.pi):ℂ)*
        (∫ y : ℝ, cosineKernel sigma P t ((1/8:ℝ)+(y:ℂ)*I)) =
      ((t/(2*Real.pi):ℝ):ℂ)^(-sigma)*riemannZeta (1-sigma) := by
  rw [cosine_diagonal_correction sigma hs hn P t hP ht]
  ring

#print axioms cosine_vertical_integrable
#print axioms reflected_integral
#print axioms cosine_diagonal_correction
#print axioms cosine_diagonal_balance
#print axioms cosine_functional
#print axioms positive_power_identity
#print axioms reflected_kernel
#print axioms reflected_vertical
end XiPrime8845.PRZZZeroReflection
