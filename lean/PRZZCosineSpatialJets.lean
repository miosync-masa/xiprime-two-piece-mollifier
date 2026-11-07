import PRZZSourceWDerivatives
import PRZZPowerJets

/-! Exact derivatives after the reciprocal spatial substitution in the
actual zero cosine integral. These are the actual sourceW derivatives,
not a formal replacement by a cosine Mellin moment. Boundary limits and
the improper integration-by-parts argument are separate statements. -/
noncomputable section
open Complex Set MeasureTheory
namespace XiPrime8845.PRZZCosineSpatialJets
open PRZZDyadicEnvelope PRZZSourceWDerivatives
set_option maxHeartbeats 5000000

def arg (X y : ℝ) : ℝ := X/y^2
def power (p : ℂ) (y : ℝ) : ℂ := exp (p*(Real.log y:ℂ))
def primitive (p sigma : ℂ) (X y : ℝ) : ℂ := power p y*sourceW sigma (arg X y)
def first (p sigma : ℂ) (X y : ℝ) : ℂ :=
  power p y/(y:ℂ)*(p*sourceW sigma (arg X y)-2*(arg X y:ℂ)*jet sigma 0 (arg X y))
def second (p sigma : ℂ) (X y : ℝ) : ℂ :=
  power p y/(y:ℂ)^2*(p*(p-1)*sourceW sigma (arg X y)+
    (6-4*p)*(arg X y:ℂ)*jet sigma 0 (arg X y)+4*(arg X y:ℂ)^2*jet sigma 1 (arg X y))

theorem arg_deriv (X y : ℝ) (hy : 0 < y) :
    HasDerivAt (arg X) (-2*X/y^3) y := by
  have h := (hasDerivAt_const y X).div ((hasDerivAt_id y).pow 2) (pow_ne_zero 2 hy.ne')
  convert h using 1 <;> first | rfl | skip
  simp only [Pi.pow_apply,Pi.div_apply,id_eq,Nat.cast_ofNat,Nat.reduceSub,pow_one,
    mul_one,zero_mul,zero_sub]
  field_simp <;> ring

theorem power_deriv (p : ℂ) (y : ℝ) (hy : 0 < y) :
    HasDerivAt (power p) (power p y*p/(y:ℂ)) y := by
  have h := ((Real.hasDerivAt_log hy.ne').ofReal_comp.const_mul p).cexp
  convert h using 1 <;> first | rfl | skip
  simp only [power,Complex.real_smul,Complex.ofReal_inv]
  ring

theorem primitive_deriv (p sigma : ℂ) (hs : sigma ≠ 0) (X y : ℝ)
    (hX : 0 < X) (hy : 0 < y) :
    HasDerivAt (primitive p sigma X) (first p sigma X y) y := by
  have ha := arg_deriv X y hy
  have hw := (source_hasDerivAt sigma hs (arg X y) (by unfold arg; positivity)).scomp y ha
  have hh := (power_deriv p y hy).mul hw
  convert hh using 1 <;> first | rfl | skip
  simp only [first,Function.comp_apply,Pi.mul_apply,Pi.sub_apply,Pi.div_apply,
    Complex.real_smul,arg,Complex.ofReal_div,Complex.ofReal_pow,
    Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_ofNat]
  have hyC : (y:ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  field_simp [hyC]
  ring

theorem first_deriv (p sigma : ℂ) (hs : sigma ≠ 0) (X y : ℝ)
    (hX : 0 < X) (hy : 0 < y) :
    HasDerivAt (first p sigma X) (second p sigma X y) y := by
  have ha := arg_deriv X y hy
  have hw := (source_hasDerivAt sigma hs (arg X y) (by unfold arg; positivity)).scomp y ha
  have hj := (jet_hasDerivAt sigma 0 (arg X y) (by unfold arg; positivity)).scomp y ha
  have hp := (power_deriv p y hy).div Complex.ofRealCLM.hasDerivAt
    (by change (y:ℂ) ≠ 0; exact_mod_cast hy.ne')
  have hh := hp.mul ((hw.const_mul p).sub ((ha.ofReal_comp.const_mul 2).mul hj))
  convert hh using 1 <;> first | rfl | skip
  simp only [second,Function.comp_apply,Pi.mul_apply,Pi.sub_apply,Pi.div_apply,
    Complex.real_smul,Complex.ofRealCLM_apply,arg,Complex.ofReal_div,
    Complex.ofReal_pow,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_ofNat,Complex.ofReal_one]
  have hyC : (y:ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  field_simp [hyC]
  ring

/-- Two integrations by parts on a genuine positive spatial interval.
Both boundary terms are retained; the second-derivative integral carries
a minus sign. No improper boundary limit is a hypothesis here. -/
theorem finite_cosine_ibp (p sigma : ℂ) (hs : sigma ≠ 0) (X a b : ℝ)
    (hX : 0 < X) (ha : 0 < a) (hab : a ≤ b) :
    (∫ y in a..b, primitive p sigma X y*cos (y:ℂ)) =
      (primitive p sigma X b*sin (b:ℂ)+first p sigma X b*cos (b:ℂ))-
      (primitive p sigma X a*sin (a:ℂ)+first p sigma X a*cos (a:ℂ))-
        ∫ y in a..b, second p sigma X y*cos (y:ℂ) := by
  have hpos (y : ℝ) (hy : y ∈ Icc a b) : 0 < y := ha.trans_le hy.1
  have hf : ContinuousOn (fun y : ℝ => primitive p sigma X y*cos (y:ℂ)) (Icc a b) := by
    intro y hy
    exact ((primitive_deriv p sigma hs X y hX (hpos y hy)).continuousAt.mul
      (Complex.hasDerivAt_cos (y:ℂ)).comp_ofReal.continuousAt).continuousWithinAt
  have hg : ContinuousOn (fun y : ℝ => second p sigma X y*cos (y:ℂ)) (Icc a b) := by
    intro y hy
    have hypos := hpos y hy
    have hyC : (y:ℂ) ≠ 0 := by exact_mod_cast hypos.ne'
    have ha' := arg_deriv X y hypos
    have hp := (power_deriv p y hypos).continuousAt
    have hw := ((source_hasDerivAt sigma hs (arg X y) (by unfold arg; positivity)).scomp y ha').continuousAt
    have hj := ((jet_hasDerivAt sigma 0 (arg X y) (by unfold arg; positivity)).scomp y ha').continuousAt
    have hj' := ((jet_hasDerivAt sigma 1 (arg X y) (by unfold arg; positivity)).scomp y ha').continuousAt
    have haC := ha'.ofReal_comp.continuousAt
    apply ContinuousAt.continuousWithinAt
    unfold second
    fun_prop (disch := simp [hyC])
  have hfi := hf.intervalIntegrable_of_Icc (μ := volume) hab
  have hgi := hg.intervalIntegrable_of_Icc (μ := volume) hab
  have hd (y : ℝ) (hy : y ∈ uIcc a b) :
      HasDerivAt (fun y : ℝ => primitive p sigma X y*sin (y:ℂ)+first p sigma X y*cos (y:ℂ))
        (primitive p sigma X y*cos (y:ℂ)+second p sigma X y*cos (y:ℂ)) y := by
    have hypos := hpos y (by simpa only [uIcc_of_le hab] using hy)
    have hh := ((primitive_deriv p sigma hs X y hX hypos).mul
      (Complex.hasDerivAt_sin (y:ℂ)).comp_ofReal).add
      ((first_deriv p sigma hs X y hX hypos).mul (Complex.hasDerivAt_cos (y:ℂ)).comp_ofReal)
    convert hh using 1 <;> first | rfl | skip
    ring
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hfi.add hgi)
  rw [intervalIntegral.integral_add hfi hgi] at hh
  linear_combination hh

#print axioms arg_deriv
#print axioms power_deriv
#print axioms primitive_deriv
#print axioms first_deriv
#print axioms finite_cosine_ibp
end XiPrime8845.PRZZCosineSpatialJets
