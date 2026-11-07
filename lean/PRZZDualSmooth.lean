import PRZZZeroExhaustionCross
import Mathlib.Analysis.Complex.CauchyIntegral

/-! Smoothness of the genuine dual Gamma quotient on the full real time
axis for small shifts. This supplies the weighted cutoff needed for the
second branch's actual zero-mode exhaustion. -/
noncomputable section
open scoped ContDiff
open Complex Set Filter Topology
namespace XiPrime8845.PRZZDualSmooth
set_option maxHeartbeats 5000000

theorem gamma_contDiffAt (z : ℂ) (hz : 0 < z.re) : ContDiffAt ℝ ∞ Gamma z := by
  have hd : DifferentiableOn ℂ Gamma {w : ℂ | 0 < w.re} := by
    intro w hw
    apply (differentiableAt_Gamma w ?_).differentiableWithinAt
    intro n he
    have hh := congrArg Complex.re he
    simp at hh
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    change 0 < w.re at hw
    linarith
  have ha := hd.analyticAt ((isOpen_lt continuous_const continuous_re).mem_nhds hz)
  have hc : ContDiffAt ℂ ∞ Gamma z := ha.contDiffAt
  exact hc.restrict_scalars ℝ

theorem gamma_line (c k : ℂ) (hc : 0 < c.re) (hk : k.re = 0) :
    ContDiff ℝ ∞ (fun t : ℝ => Gamma (c+(t:ℂ)*k)) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  have hz : 0 < (c+(t:ℂ)*k).re := by simp [hk]; exact hc
  have hf : ContDiff ℝ ∞ (fun t : ℝ => (t:ℂ)) := Complex.ofRealCLM.contDiff
  have hg : ContDiff ℝ ∞ (fun t : ℝ => c+(t:ℂ)*k) :=
    contDiff_const.add (hf.mul contDiff_const)
  exact (gamma_contDiffAt _ hz).comp t hg.contDiffAt

theorem multiplier_contDiff (a b : ℂ) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4) :
    ContDiff ℝ ∞ (PRZZAFEDual.dualMultiplier a b) := by
  have hl (z : ℂ) (hz : 0 < 1/2+z.re) :
      ContDiff ℝ ∞ (fun t : ℝ => Gamma (PRZZAFEDual.leftArg z t/2)) := by
    have he : (fun t : ℝ => Gamma (PRZZAFEDual.leftArg z t/2)) =
        (fun t : ℝ => Gamma ((1/2+z)/2+(t:ℂ)*(I/2))) := by
      funext t; congr 1; unfold PRZZAFEDual.leftArg; ring
    rw [he]
    exact gamma_line _ _ (by simp; linarith) (by simp)
  have hr (z : ℂ) (hz : 0 < 1/2+z.re) :
      ContDiff ℝ ∞ (fun t : ℝ => Gamma (PRZZAFEDual.rightArg z t/2)) := by
    have he : (fun t : ℝ => Gamma (PRZZAFEDual.rightArg z t/2)) =
        (fun t : ℝ => Gamma ((1/2+z)/2+(t:ℂ)*(-I/2))) := by
      funext t; congr 1; unfold PRZZAFEDual.rightArg; ring
    rw [he]
    exact gamma_line _ _ (by simp; linarith) (by simp)
  have har := abs_le.mp ((abs_re_le_norm a).trans ha)
  have hbr := abs_le.mp ((abs_re_le_norm b).trans hb)
  have hn (z : ℂ) (hz : 0 < z.re) : Gamma z ≠ 0 := by
    apply Gamma_ne_zero
    intro n he
    have hh := congrArg Complex.re he
    simp at hh
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have he : PRZZAFEDual.dualMultiplier a b = fun t : ℝ =>
      (Real.pi:ℂ)^(a+b)*(Gamma (PRZZAFEDual.leftArg (-b) t/2)*Gamma (PRZZAFEDual.rightArg (-a) t/2))/
        (Gamma (PRZZAFEDual.leftArg a t/2)*Gamma (PRZZAFEDual.rightArg b t/2)) := by
    funext t; exact PRZZAFEDual.dualMultiplier_formula a b t
  rw [he]
  have hnum : ContDiff ℝ ∞ (fun t : ℝ => (Real.pi:ℂ)^(a+b)*
      (Gamma (PRZZAFEDual.leftArg (-b) t/2)*Gamma (PRZZAFEDual.rightArg (-a) t/2))) :=
    contDiff_const.mul ((hl (-b) (by simp; linarith [hbr.2])).mul
    (hr (-a) (by simp; linarith [har.2])))
  have hden := (hl a (by linarith [har.1])).mul (hr b (by linarith [hbr.1]))
  have hi := hden.inv (fun t => mul_ne_zero
    (hn _ (by simp [PRZZAFEDual.leftArg]; linarith [har.1]))
    (hn _ (by simp [PRZZAFEDual.rightArg]; linarith [hbr.1])))
  simpa only [div_eq_mul_inv,Pi.mul_apply,Pi.inv_apply] using hnum.mul hi

#print axioms gamma_contDiffAt
#print axioms gamma_line
#print axioms multiplier_contDiff
end XiPrime8845.PRZZDualSmooth
