import ZetaMomentMainTerm
import LogarithmicBudget

/-! The fixed degree-six witness connected to the certified numerical bound.
The weight is fixed before taking T to infinity. Its mass is explicit; the
counting interface uses a nonnegative weight of positive mass. Finite heights
receive a strict slack above the limiting cap, not the limiting cap itself.
Only limit-derived statements use the existing PRZZ input. No Wu zero-counting
inequality, removal of smoothing, or zero-proportion theorem is asserted. -/
noncomputable section
open Filter Topology MeasureTheory
namespace XiPrime8845.WitnessMomentBound
open ZetaMomentPolynomial ConreyCoefficientBridge
set_option maxHeartbeats 1000000

def qReal (n : ℕ) : ℝ := (NumericalGate.qCoeff n).re

theorem qReal_cast (n : ℕ) : (qReal n : ℂ) = NumericalGate.qCoeff n := by
  by_cases hn : n ≤ 6
  · interval_cases n <;> norm_num [qReal, NumericalGate.qCoeff]
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 7 := ⟨n - 7, by omega⟩
    rfl

theorem profiles_match :
    complexify PRZZ.witness.conrey = NumericalGate.F ∧
    complexify PRZZ.witness.feng = NumericalGate.G := by
  constructor <;> norm_num [complexify, PRZZ.witness, NumericalGate.F, NumericalGate.G]

theorem radius_match : PRZZAsymptotic.R = NumericalGate.R := by
  norm_num [PRZZAsymptotic.R, NumericalGate.R, radiusParameter]

/-- No numerical approximation occurs in this identification. -/
theorem evaluator_eq_actual :
    IntegralJet.exactEvaluator 6 (fun n => (qReal n : ℂ))
      (-(PRZZAsymptotic.R:ℂ)) (-(PRZZAsymptotic.R:ℂ)) PRZZAsymptotic.theta
      (complexify PRZZ.witness.conrey) (complexify PRZZ.witness.feng) =
        NumericalGate.actual := by
  simp only [qReal_cast, profiles_match.1, profiles_match.2, radius_match]
  exact (IntegralJet.K2_exact_evaluator 6 NumericalGate.qCoeff
    (-(NumericalGate.R:ℂ)) (-(NumericalGate.R:ℂ))
    (by norm_num [NumericalGate.R]) NumericalGate.θ NumericalGate.F NumericalGate.G).symm

def mass (Phi : ℝ → ℝ) : ℝ := ∫ u in Set.Icc (1:ℝ) 2, Phi u

theorem weightMass_eq (Phi : ℝ → ℝ) : ConreyMainTerm.weightMass Phi = (mass Phi : ℂ) := by
  simp only [ConreyMainTerm.weightMass, mass, integral_complex_ofReal]

def witnessMoment (Phi : ℝ → ℝ) (T : ℝ) : ℝ :=
  squareMoment 6 qReal PRZZ.witness PRZZAsymptotic.theta T Phi
    (1/2-PRZZAsymptotic.R/Real.log T)

/-- The original mollifier remains on Re(s)=1/2; only zeta is shifted. -/
theorem witnessMoment_tendsto (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi) :
    Tendsto (witnessMoment Phi) atTop (nhds (NumericalGate.actual.re * mass Phi)) := by
  change Tendsto (fun T => squareMoment 6 qReal PRZZ.witness PRZZAsymptotic.theta T Phi
    (1/2-PRZZAsymptotic.R/Real.log T)) atTop _
  simpa only [evaluator_eq_actual, weightMass_eq, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using
    ZetaMomentMainTerm.squareMoment_exactEvaluator_tendsto 6 qReal Phi hPhi

theorem mass_nonneg (Phi : ℝ → ℝ) (hPhi : ∀ t, 0 ≤ Phi t) : 0 ≤ mass Phi :=
  integral_nonneg (fun t => hPhi t)

theorem witnessMoment_nonneg (Phi : ℝ → ℝ) (hPhi : ∀ t, 0 ≤ Phi t)
    (T : ℝ) (hT : 0 ≤ T) : 0 ≤ witnessMoment Phi T := by
  unfold witnessMoment squareMoment
  exact div_nonneg (integral_nonneg (fun t => mul_nonneg (sq_nonneg _) (hPhi _))) hT

/-- Mass-aware upper bound, with an arbitrarily small additive finite-T slack. -/
theorem witnessMoment_eventually_lt (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi)
    (hm : 0 ≤ mass Phi) (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ T : ℝ in atTop,
      witnessMoment Phi T < LogarithmicBudget.certifiedCap * mass Phi + eps := by
  have h := mul_le_mul_of_nonneg_right LogarithmicBudget.actual_le_cap hm
  exact (witnessMoment_tendsto Phi hPhi).eventually
    (gt_mem_nhds (by linarith : NumericalGate.actual.re * mass Phi <
      LogarithmicBudget.certifiedCap * mass Phi + eps))

def normalizedMoment (Phi : ℝ → ℝ) (T : ℝ) : ℝ := witnessMoment Phi T / mass Phi

theorem normalizedMoment_tendsto (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi)
    (hm : 0 < mass Phi) :
    Tendsto (normalizedMoment Phi) atTop (nhds NumericalGate.actual.re) := by
  change Tendsto (fun T => witnessMoment Phi T / mass Phi) atTop _
  simpa only [mul_div_cancel_right₀ _ hm.ne'] using
    (witnessMoment_tendsto Phi hPhi).div_const (mass Phi)

theorem normalizedMoment_eventually_lt (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi)
    (hm : 0 < mass Phi) (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ T : ℝ in atTop,
      normalizedMoment Phi T < LogarithmicBudget.certifiedCap + eps :=
  (normalizedMoment_tendsto Phi hPhi hm).eventually
    (gt_mem_nhds (lt_of_le_of_lt LogarithmicBudget.actual_le_cap (by linarith)))

/-- One micro-unit of slack, still strictly inside the numerical target. -/
def countingCap : ℝ := 1.128202

theorem countingCap_lt_target : countingCap < NumericalGate.target := by
  have h := NumericalGate.target_lower
  norm_num [countingCap] at ⊢
  linarith

theorem countingCap_budget :
    (0.8845 : ℝ) < 1 - Real.log countingCap / NumericalGate.R := by
  have hl : Real.log countingCap < NumericalGate.R * (1 - 0.8845) :=
    (Real.log_lt_iff_lt_exp (by norm_num [countingCap] : 0 < countingCap)).mpr
    countingCap_lt_target
  have hr : 0 < NumericalGate.R := by norm_num [NumericalGate.R]
  have hd : Real.log countingCap / NumericalGate.R < 1 - 0.8845 :=
    (div_lt_iff₀ hr).mpr (by nlinarith)
  linarith

/-- A single interface for the future counting adapter: the ACTUAL normalized
square moment has an eventual numerical upper bound and the cap has a fixed
strict logarithmic margin. No positivity of the moment is inferred from its
upper bound, and no logarithm of the moment is taken here. -/
theorem witness_moment_bound (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi)
    (hPhi0 : ∀ t, 0 ≤ Phi t) (hm : 0 < mass Phi) :
    (0.8845 : ℝ) < 1 - Real.log countingCap / NumericalGate.R ∧
      ∀ᶠ T : ℝ in atTop, 1 < T ∧
        0 ≤ normalizedMoment Phi T ∧ normalizedMoment Phi T < countingCap := by
  refine ⟨countingCap_budget, ?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ),
    normalizedMoment_eventually_lt Phi hPhi hm (1/1000000) (by norm_num)] with T hT hbound
  refine ⟨hT, div_nonneg (witnessMoment_nonneg Phi hPhi0 T (by linarith)) hm.le, ?_⟩
  convert hbound using 1
  norm_num [LogarithmicBudget.certifiedCap, countingCap]

theorem unit_mass_moment_bound (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi)
    (hPhi0 : ∀ t, 0 ≤ Phi t) (hm : mass Phi = 1) :
    ∀ᶠ T : ℝ in atTop, 0 ≤ witnessMoment Phi T ∧ witnessMoment Phi T < countingCap := by
  have h := (witness_moment_bound Phi hPhi hPhi0 (by rw [hm]; norm_num)).2
  filter_upwards [h] with T hT
  simpa only [normalizedMoment, hm, div_one] using hT.2

#print axioms qReal_cast
#print axioms profiles_match
#print axioms radius_match
#print axioms evaluator_eq_actual
#print axioms weightMass_eq
#print axioms witnessMoment_tendsto
#print axioms mass_nonneg
#print axioms witnessMoment_nonneg
#print axioms witnessMoment_eventually_lt
#print axioms normalizedMoment_tendsto
#print axioms normalizedMoment_eventually_lt
#print axioms countingCap_lt_target
#print axioms countingCap_budget
#print axioms witness_moment_bound
#print axioms unit_mass_moment_bound
end XiPrime8845.WitnessMomentBound
