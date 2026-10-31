import WuCriticalDeflation

/-! The imaginary-part detector survives removal of the common divisor,
even at its zeros. A single logarithm on the entire retained interval now
detects precisely the remaining xi' zeros. -/
noncomputable section
open scoped BigOperators
open Complex Set
namespace XiPrime8845.WuCriticalDeflation
open WuAuxiliary Zeta23.XiPrime
set_option maxHeartbeats 2000000

theorem Data.realDivisor_ne_zero {L u v : ℝ} (d : Data L u v) (t : ℝ)
    (ht : t ∉ d.zeros.image Complex.im) : d.realDivisor t ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro s hs
  apply pow_ne_zero
  intro hz
  exact ht (Finset.mem_image.mpr ⟨s,hs,(sub_eq_zero.mp hz).symm⟩)

/-- Continuity fills the removed points; cancellation is only used away
from the finite real divisor, never at one of its zeros. -/
theorem Data.curve_im {L u v : ℝ} (d : Data L u v) (t : ℝ) :
    (d.curve (critical t)).im = (rCoeff 1/L)*(d.remaining (critical t)).im := by
  classical
  have hp : Continuous critical := by unfold critical; fun_prop
  have hc : Continuous d.curve := continuous_const.mul d.eta_entire.continuous
  have hr : Continuous d.remaining := continuous_const.mul d.xi_entire.continuous
  have hd : Dense ((d.zeros.image Complex.im : Finset ℝ) : Set ℝ)ᶜ :=
    (d.zeros.image Complex.im).finite_toSet.countable.dense_compl ℝ
  have hleft : Continuous (fun x => (d.curve (critical x)).im) :=
    Complex.continuous_im.comp (hc.comp hp)
  have hright : Continuous (fun x => (rCoeff 1/L)*(d.remaining (critical x)).im) :=
    continuous_const.mul (Complex.continuous_im.comp (hr.comp hp))
  have he := Continuous.ext_on hd hleft hright (by
      intro x hx
      have hn : d.realDivisor x ≠ 0 := d.realDivisor_ne_zero x (by simpa using hx)
      have hh := eta_im L x
      rw [d.eta_critical,d.xi_critical] at hh
      simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero] at hh
      exact mul_left_cancel₀ hn (hh.trans (by ring)))
  exact congrFun he t

theorem Data.remaining_re {L u v : ℝ} (d : Data L u v) (t : ℝ) :
    (d.remaining (critical t)).re = 0 := by
  classical
  have hp : Continuous critical := by unfold critical; fun_prop
  have hr : Continuous d.remaining := continuous_const.mul d.xi_entire.continuous
  have hd : Dense ((d.zeros.image Complex.im : Finset ℝ) : Set ℝ)ᶜ :=
    (d.zeros.image Complex.im).finite_toSet.countable.dense_compl ℝ
  have hleft : Continuous (fun x => (d.remaining (critical x)).re) :=
    Complex.continuous_re.comp (hr.comp hp)
  have he := Continuous.ext_on hd hleft (continuous_const (y := (0:ℝ))) (by
      intro x hx
      have hn : d.realDivisor x ≠ 0 := d.realDivisor_ne_zero x (by simpa using hx)
      have hh : (xiDeriv (critical x)).re = 0 := by simpa [xiDeriv] using xi_odd_re 0 x
      rw [d.xi_critical] at hh
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hh
      exact (mul_eq_zero.mp hh).resolve_left hn)
  exact congrFun he t

theorem Data.curve_im_zero_iff {L u v : ℝ} (d : Data L u v) (hL : L ≠ 0) (t : ℝ) :
    (d.curve (critical t)).im = 0 ↔ d.xiPart (critical t) = 0 := by
  have hn : rCoeff 1/L ≠ 0 := div_ne_zero linear_coefficient_pos.ne' hL
  rw [d.curve_im,mul_eq_zero,or_iff_right hn]
  have he : (d.remaining (critical t)).im = 0 ↔ d.remaining (critical t) = 0 := by
    constructor
    · intro h; apply Complex.ext <;> simp [d.remaining_re,h]
    · intro h; rw [h]; rfl
  rw [he,Data.remaining,mul_eq_zero,or_iff_right (pow_ne_zero _ I_ne_zero)]

/-- Phase crossings are zeros of the deflated xi' factor, not merely zeros
of the original function (whose removed orders are separately budgeted). -/
theorem Data.phase_zero_iff {L u v : ℝ} (d : Data L u v) (hL : L ≠ 0)
    (q : WuLittlewood.EdgeLog d.curve (1/2) I u v) (t : ℝ) (ht : t ∈ uIcc u v) :
    Real.sin (q.value t).im = 0 ↔ d.xiPart (critical t) = 0 := by
  have hh := congrArg Complex.im (q.exp_eq t ht)
  change (exp (q.value t)).im = (d.curve (critical t)).im at hh
  rw [Complex.exp_im] at hh
  rw [← d.curve_im_zero_iff hL t,← hh,mul_eq_zero,or_iff_right (Real.exp_ne_zero _)]

#print axioms Data.realDivisor_ne_zero
#print axioms Data.curve_im
#print axioms Data.remaining_re
#print axioms Data.curve_im_zero_iff
#print axioms Data.phase_zero_iff
end XiPrime8845.WuCriticalDeflation
