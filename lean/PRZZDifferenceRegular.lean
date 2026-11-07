import PRZZGammaMain
import Mathlib.Analysis.Analytic.IsolatedZeros
import Zeta23.FromPNTPlus.ResidueCalcOnRectangles

/-! Remove the apparent central pole of the actual V-W difference before
 contour shifting. No horizontal-edge estimate or shifted infinite integral identity
is assumed or asserted here. -/
noncomputable section
open Complex Filter Topology
namespace XiPrime8845.PRZZDifferenceRegular
open PRZZAFEGamma PRZZDyadicEnvelope
set_option maxHeartbeats 2000000

def numerator (a b : ℂ) (t q : ℝ) (s : ℂ) : ℂ := gammaRatio a b s t-(q:ℂ)^s

def regular (a b : ℂ) (x t q : ℝ) (s : ℂ) : ℂ :=
  (x:ℂ)^(-s)*exp (s^2)*annihilator (a+b) s*dslope (numerator a b t q) 0 s

theorem denominator_nonzero (a b : ℂ) (t : ℝ)
    (ha : -(1/2:ℝ) < a.re) (hb : -(1/2:ℝ) < b.re) :
    Gamma ((1/2+a+(t:ℂ)*I)/2)*Gamma ((1/2+b-(t:ℂ)*I)/2) ≠ 0 := by
  apply mul_ne_zero <;> apply Gamma_ne_zero_of_re_pos <;>
    simp only [div_ofNat_re,add_re,sub_re,mul_re,ofReal_re,ofReal_im,I_re,I_im,
      mul_zero,zero_mul,sub_zero,sub_self,add_zero] <;> norm_num <;> linarith

theorem numerator_zero (a b : ℂ) (t q : ℝ)
    (ha : -(1/2:ℝ) < a.re) (hb : -(1/2:ℝ) < b.re) :
    numerator a b t q 0 = 0 := by
  simp only [numerator,gammaRatio,neg_zero,cpow_zero,one_mul,add_zero]
  rw [div_self (denominator_nonzero a b t ha hb),sub_self]

theorem numerator_analytic (a b s : ℂ) (t q : ℝ)
    (ha : -(1/2:ℝ) < a.re) (hb : -(1/2:ℝ) < b.re)
    (has : 0 < (1/2+a+s).re) (hbs : 0 < (1/2+b+s).re) (hq : 0 < q) :
    AnalyticAt ℂ (numerator a b t q) s := by
  have hga : AnalyticAt ℂ (fun z : ℂ => Gamma ((1/2+a+z+(t:ℂ)*I)/2)) s :=
    (PRZZGammaPath.gamma_analytic _ (by simpa using half_pos has)).comp
      (by fun_prop)
  have hgb : AnalyticAt ℂ (fun z : ℂ => Gamma ((1/2+b+z-(t:ℂ)*I)/2)) s :=
    (PRZZGammaPath.gamma_analytic _ (by simpa using half_pos hbs)).comp
      (by fun_prop)
  have hp : AnalyticAt ℂ (fun z : ℂ => (Real.pi:ℂ)^(-z)) s := by
    simp only [cpow_def_of_ne_zero (show (Real.pi:ℂ) ≠ 0 by exact_mod_cast Real.pi_ne_zero)]
    fun_prop
  have hq' : AnalyticAt ℂ (fun z : ℂ => (q:ℂ)^z) s := by
    simp only [cpow_def_of_ne_zero (show (q:ℂ) ≠ 0 by exact_mod_cast hq.ne')]
    fun_prop
  exact ((hp.mul (hga.mul hgb)).div analyticAt_const
    (denominator_nonzero a b t ha hb)).sub hq'

/-- The quotient has an analytic extension at zero, supplied from the
actual Gamma factors rather than an assumed removable-pole premise. -/
theorem regular_analytic_zero (a b : ℂ) (x t q : ℝ)
    (ha : -(1/2:ℝ) < a.re) (hb : -(1/2:ℝ) < b.re) (hx : 0 < x) (hq : 0 < q) :
    AnalyticAt ℂ (regular a b x t q) 0 := by
  have hn := numerator_analytic a b 0 t q ha hb (by simp; linarith) (by simp; linarith) hq
  obtain ⟨p,hp⟩ := hn
  have hd : AnalyticAt ℂ (dslope (numerator a b t q) 0) 0 :=
    ⟨p.fslope,hp.has_fpower_series_dslope_fslope⟩
  have hf : AnalyticAt ℂ (fun s : ℂ =>
      (x:ℂ)^(-s)*exp (s^2)*annihilator (a+b) s) 0 := by
    simp only [cpow_def_of_ne_zero (show (x:ℂ) ≠ 0 by exact_mod_cast hx.ne'),annihilator]
    fun_prop
  exact hf.mul hd

theorem regular_eq (a b s : ℂ) (x t q : ℝ)
    (ha : -(1/2:ℝ) < a.re) (hb : -(1/2:ℝ) < b.re) (hs : s ≠ 0) :
    regular a b x t q s =
      (x:ℂ)^(-s)*exp (s^2)*annihilator (a+b) s/s*numerator a b t q s := by
  rw [regular,dslope_of_ne _ hs]
  simp only [slope,vsub_eq_sub,sub_zero,numerator_zero a b t q ha hb,smul_eq_mul]
  ring

theorem on_original_line (a b : ℂ) (x t q v : ℝ)
    (ha : -(1/2:ℝ) < a.re) (hb : -(1/2:ℝ) < b.re) :
    regular a b x t q (2+(v:ℂ)*I) =
      PRZZKernelDifference.errorIntegrand a b x t q v := by
  rw [regular_eq a b _ x t q ha hb (by
    intro he; have hh := congrArg Complex.re he; norm_num at hh)]
  unfold PRZZKernelDifference.errorIntegrand PRZZMellinTail.factor numerator
  ring

/-- Holomorphy throughout the pole-free Gamma region, including zero. -/
theorem regular_analytic (a b s : ℂ) (x t q : ℝ)
    (ha : -(1/2:ℝ) < a.re) (hb : -(1/2:ℝ) < b.re)
    (has : 0 < (1/2+a+s).re) (hbs : 0 < (1/2+b+s).re)
    (hx : 0 < x) (hq : 0 < q) : AnalyticAt ℂ (regular a b x t q) s := by
  by_cases hs : s = 0
  · subst s; exact regular_analytic_zero a b x t q ha hb hx hq
  have hn := numerator_analytic a b s t q ha hb has hbs hq
  have hd : AnalyticAt ℂ (fun z => numerator a b t q z/z) s :=
    hn.div analyticAt_id hs
  have hf : AnalyticAt ℂ (fun z : ℂ =>
      (x:ℂ)^(-z)*exp (z^2)*annihilator (a+b) z) s := by
    simp only [cpow_def_of_ne_zero (show (x:ℂ) ≠ 0 by exact_mod_cast hx.ne'),annihilator]
    fun_prop
  apply (hf.mul hd).congr
  filter_upwards [eventually_ne_nhds hs] with z hz
  rw [regular_eq a b z x t q ha hb hz]
  simp only [Pi.mul_apply]
  ring

/-- Small shifts permit moving left of zero without crossing Gamma poles.
The strict -1/4 boundary is retained; no claim is made beyond this strip. -/
theorem pole_free_strip (a b : ℂ) (x t q : ℝ)
    (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4) (hx : 0 < x) (hq : 0 < q) :
    AnalyticOnNhd ℂ (regular a b x t q) {s : ℂ | -(1/4:ℝ) < s.re} := by
  have har := (abs_le.mp ((abs_re_le_norm a).trans ha)).1
  have hbr := (abs_le.mp ((abs_re_le_norm b).trans hb)).1
  intro s hs
  change -(1/4:ℝ) < s.re at hs
  apply regular_analytic a b s x t q (by linarith) (by linarith) _ _ hx hq
  · simp only [add_re]; norm_num; linarith
  · simp only [add_re]; norm_num; linarith

/-- A finite contour may cross zero without a residue contribution. Both
vertical edges remain strictly to the right of the first possible Gamma poles.
The horizontal edges are retained, not discarded by this identity. -/
theorem finite_rectangle (a b z w : ℂ) (x t q : ℝ)
    (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4) (hx : 0 < x) (hq : 0 < q)
    (hz : -(1/4:ℝ) < z.re) (hw : -(1/4:ℝ) < w.re) :
    RectangleIntegral (regular a b x t q) z w = 0 := by
  have hh : HolomorphicOn (regular a b x t q) {s : ℂ | -(1/4:ℝ) < s.re} := by
    intro s hs
    exact ((pole_free_strip a b x t q ha hb hx hq) s hs).differentiableAt.differentiableWithinAt
  apply hh.vanishesOnRectangle
  intro s hs
  change s.re ∈ Set.uIcc z.re w.re ∧ s.im ∈ Set.uIcc z.im w.im at hs
  exact lt_of_lt_of_le (lt_min hz hw) hs.1.1

#print axioms finite_rectangle
#print axioms regular_analytic
#print axioms pole_free_strip
#print axioms denominator_nonzero
#print axioms numerator_zero
#print axioms numerator_analytic
#print axioms regular_analytic_zero
#print axioms regular_eq
#print axioms on_original_line
end XiPrime8845.PRZZDifferenceRegular
