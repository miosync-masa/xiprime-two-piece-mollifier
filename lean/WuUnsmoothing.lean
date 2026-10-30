import SmoothWindowLimit
import WuMomentTransfer

/-! Fixed-width unsmoothing for the literal V*Psi density at the original T.
First T tends to infinity, then the omitted relative width tends to zero.
Full-window convergence is stated only with an explicit endpoint-mass input. -/
noncomputable section
open Filter Topology MeasureTheory
namespace XiPrime8845.WuUnsmoothing
open SmoothWindow SmoothWindowLimit WuAuxiliary WuStirling WuMomentTransfer WitnessMomentBound
set_option maxHeartbeats 2000000

def density (T t : ℝ) : ℝ := ‖V T (leftPoint T t)*psi T (leftPoint T t)‖^2
def trimmedMoment (δ T : ℝ) : ℝ := windowMoment density (1/2-δ) T
def trimmedMean (δ T : ℝ) : ℝ := trimmedMoment δ T/(1-2*δ)
def fullMoment (T : ℝ) : ℝ := windowMoment density (1/2) T
def endpointMoment (δ T : ℝ) : ℝ :=
  (∫ t in window (1/2) T \ window (1/2-δ) T, density T t)/T

theorem trimmedMoment_eq (δ T : ℝ) :
    trimmedMoment δ T =
      (∫ t in Set.Icc ((1+δ)*T) ((2-δ)*T), density T t)/T := by
  simp only [trimmedMoment, windowMoment, window]
  rw [show (3/2-(1/2-δ) : ℝ) = 1+δ by ring,
    show (3/2+(1/2-δ) : ℝ) = 2-δ by ring]

theorem fullMoment_eq (T : ℝ) :
    fullMoment T = (∫ t in Set.Icc T (2*T), density T t)/T := by
  norm_num [fullMoment, windowMoment, window]

theorem weighted_integrable (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi) :
    ∀ᶠ T : ℝ in atTop, Integrable (fun t => density T t*Phi (t/T)) := by
  filter_upwards [WuStirlingTransfer.leftPoint_strip] with T hs
  exact v_integrable Phi hPhi T hs.1 hs.2.2

theorem trimmed_integrable (δ : ℝ) (hδ : 0 < δ) (hd : δ < 1/2) :
    ∀ᶠ T : ℝ in atTop, IntegrableOn (density T) (window (1/2-δ) T) :=
  window_integrable density weighted_integrable _ (by linarith) (by linarith)

/-- The threshold may depend on δ. The integrand's T is never rescaled. -/
theorem trimmedMoment_tendsto (δ : ℝ) (hδ : 0 < δ) (hd : δ < 1/2) :
    Tendsto (trimmedMoment δ) atTop (nhds (NumericalGate.actual.re*(1-2*δ))) := by
  have h := windowMoment_tendsto density NumericalGate.actual.re
    (fun T t => sq_nonneg _) weighted_integrable
    (fun Phi hPhi hPhi0 => vMoment_tendsto Phi hPhi hPhi0)
    (1/2-δ) (by linarith) (by linarith)
  have he : NumericalGate.actual.re*(2*(1/2-δ)) =
      NumericalGate.actual.re*(1-2*δ) := by ring
  rw [he] at h
  exact h

theorem trimmedMean_tendsto (δ : ℝ) (hδ : 0 < δ) (hd : δ < 1/2) :
    Tendsto (trimmedMean δ) atTop (nhds NumericalGate.actual.re) := by
  have hn : 1-2*δ ≠ 0 := by linarith
  change Tendsto (fun T => trimmedMoment δ T/(1-2*δ)) atTop _
  simpa only [mul_div_cancel_right₀ _ hn] using
    (trimmedMoment_tendsto δ hδ hd).div_const (1-2*δ)

theorem trimmed_counting_bound (δ : ℝ) (hδ : 0 < δ) (hd : δ < 1/2) :
    (0.8845 : ℝ) < 1-Real.log countingCap/NumericalGate.R ∧
      ∀ᶠ T : ℝ in atTop, 1 < T ∧
        0 ≤ trimmedMean δ T ∧ trimmedMean δ T < countingCap := by
  refine ⟨countingCap_budget, ?_⟩
  have hc : NumericalGate.actual.re < countingCap :=
    LogarithmicBudget.actual_le_cap.trans_lt (by
      norm_num [LogarithmicBudget.certifiedCap, countingCap])
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (trimmedMean_tendsto δ hδ hd).eventually (gt_mem_nhds hc)] with T hT hb
  refine ⟨hT, ?_, hb⟩
  exact div_nonneg (div_nonneg (integral_nonneg (fun t => sq_nonneg _)) (by linarith))
    (by linarith)

/-- The loss of interval length fits inside the strict numerical margin.
This numerical budget is not itself a zero-counting inequality. -/
theorem width_budget :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 < 1/2 ∧ ∀ δ : ℝ, 0 < δ → δ < δ0 →
      (0.8845 : ℝ) < (1-2*δ)*(1-Real.log countingCap/NumericalGate.R) := by
  let B := 1-Real.log countingCap/NumericalGate.R
  have hB : (0.8845 : ℝ) < B := countingCap_budget
  have hB0 : 0 < B := by linarith
  let δ0 := min (1/4 : ℝ) ((B-0.8845)/(4*B))
  refine ⟨δ0, lt_min (by norm_num) (by positivity),
    (min_le_left _ _).trans_lt (by norm_num), ?_⟩
  intro δ hδ hd
  have hh := (lt_div_iff₀ (show 0 < 4*B by positivity)).mp
    (hd.trans_le (min_le_right _ _))
  change (0.8845 : ℝ) < (1-2*δ)*B
  nlinarith

/-- One unsmoothed inner-window interface for the later counting argument.
Choose the width first; the eventual height threshold may depend on it. -/
theorem trimmed_budget_bound :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 < 1/2 ∧ ∀ δ : ℝ, 0 < δ → δ < δ0 →
      (0.8845 : ℝ) < (1-2*δ)*(1-Real.log countingCap/NumericalGate.R) ∧
      ∀ᶠ T : ℝ in atTop, 1 < T ∧
        0 ≤ trimmedMean δ T ∧ trimmedMean δ T < countingCap := by
  obtain ⟨δ0, h0, hh, hb⟩ := width_budget
  exact ⟨δ0, h0, hh, fun δ hδ hd =>
    ⟨hb δ hδ hd, (trimmed_counting_bound δ hδ (hd.trans hh)).2⟩⟩

/-- Literal iterated limit: each positive width is fixed in the inner limit. -/
theorem iterated_width_limit :
    (∀ δ : ℝ, 0 < δ → δ < 1/2 →
      Tendsto (trimmedMoment δ) atTop (nhds (NumericalGate.actual.re*(1-2*δ)))) ∧
    Tendsto (fun δ : ℝ => NumericalGate.actual.re*(1-2*δ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds NumericalGate.actual.re) := by
  refine ⟨trimmedMoment_tendsto, ?_⟩
  have h : Continuous (fun δ : ℝ => NumericalGate.actual.re*(1-2*δ)) := by fun_prop
  simpa using (h.tendsto 0).mono_left nhdsWithin_le_nhds

/-- Quantifiers keep the height threshold AFTER selection of the width. -/
theorem sequential_unsmoothing (eps : ℝ) (heps : 0 < eps) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 < 1/2 ∧ ∀ δ : ℝ, 0 < δ → δ < δ0 →
      ∀ᶠ T : ℝ in atTop, |trimmedMoment δ T-NumericalGate.actual.re| < eps := by
  let c := NumericalGate.actual.re
  let δ0 := min (1/4 : ℝ) (eps/(8*(|c|+1)))
  have hδ0 : 0 < δ0 := lt_min (by norm_num) (by positivity)
  have hsmall : δ0 < 1/2 := (min_le_left _ _).trans_lt (by norm_num)
  refine ⟨δ0, hδ0, hsmall, ?_⟩
  intro δ hδ hd
  have he : δ < eps/(8*(|c|+1)) := hd.trans_le (min_le_right _ _)
  have hclose : |c*(1-2*δ)-c| < eps/2 := by
    rw [show c*(1-2*δ)-c = -c*(2*δ) by ring, abs_mul, abs_neg,
      abs_of_pos (by positivity : 0 < 2*δ)]
    have hh := (lt_div_iff₀ (show 0 < 8*(|c|+1) by positivity)).mp he
    nlinarith [abs_nonneg c]
  filter_upwards [Metric.tendsto_nhds.mp (trimmedMoment_tendsto δ hδ (hd.trans hsmall))
    (eps/2) (by positivity)] with T hT
  rw [Real.dist_eq] at hT
  exact (abs_sub_le _ (c*(1-2*δ)) c).trans_lt (by linarith)

/-- Continuity supplies integrability of the full finite interval, not a
uniform endpoint estimate as T grows. -/
theorem full_integrable :
    ∀ᶠ T : ℝ in atTop, IntegrableOn (density T) (window (1/2) T) := by
  filter_upwards [WuStirlingTransfer.leftPoint_strip] with T hs
  have hp : Continuous (fun t => leftPoint T t) := by unfold leftPoint; fun_prop
  have hc : ContinuousOn (fun t => V T (leftPoint T t)*psi T (leftPoint T t))
      (window (1/2) T) := by
    apply ContinuousOn.mul _ ((psi_entire T).continuous.comp hp).continuousOn
    intro t ht
    have ht' : T ≤ t := by norm_num [window] at ht; exact ht.1
    have hr : 0 < (leftPoint T t).re := by
      simp only [leftPoint, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero]
      linarith [hs.2.2.1]
    have h1 : leftPoint T t ≠ 1 := by
      intro he
      have hh := congrArg Complex.im he
      simp [leftPoint] at hh
      linarith [hs.1]
    exact (((eta_entire (Real.log T) _).continuousAt.div
      (H_analytic _ hr).continuousAt (H_ne_zero _ hr h1)).comp hp.continuousAt).continuousWithinAt
  exact (hc.norm.pow 2).integrableOn_compact isCompact_Icc

theorem full_split (δ T : ℝ) (hδ : 0 ≤ δ) (hT : 0 < T)
    (hi : IntegrableOn (density T) (window (1/2) T)) :
    fullMoment T = trimmedMoment δ T+endpointMoment δ T := by
  have hsub : window (1/2-δ) T ⊆ window (1/2) T := by
    intro t ht
    constructor <;> dsimp [window] at ht ⊢ <;> nlinarith [ht.1, ht.2]
  have h := setIntegral_sdiff measurableSet_Icc hi hsub
  unfold fullMoment trimmedMoment endpointMoment windowMoment
  dsimp [window] at h ⊢
  rw [h]
  ring

/-- Explicit missing supplier for upgrading the iterated interior result to
the full dyadic interval. This is a proposition, not an added axiom. -/
def EndpointTight : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ δ0 : ℝ, 0 < δ0 ∧
    ∀ δ : ℝ, 0 < δ → δ < δ0 → δ < 1/2 →
      ∀ᶠ T : ℝ in atTop, endpointMoment δ T < eps

theorem fullMoment_tendsto_of_endpointTight (hboundary : EndpointTight) :
    Tendsto fullMoment atTop (nhds NumericalGate.actual.re) := by
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  obtain ⟨a, ha, hah, htrim⟩ := sequential_unsmoothing (eps/2) (by positivity)
  obtain ⟨b, hb, hend⟩ := hboundary (eps/2) (by positivity)
  obtain ⟨δ, hδ, hd⟩ := exists_between (lt_min ha hb)
  have hda : δ < a := hd.trans_le (min_le_left _ _)
  have hdb : δ < b := hd.trans_le (min_le_right _ _)
  filter_upwards [htrim δ hδ hda, hend δ hδ hdb (hda.trans hah),
    full_integrable, eventually_gt_atTop (0 : ℝ)] with T ht he hi hT
  have hen : 0 ≤ endpointMoment δ T :=
    div_nonneg (integral_nonneg (fun t => sq_nonneg _)) hT.le
  rw [Real.dist_eq, full_split δ T hδ.le hT hi]
  have h := abs_add_le (trimmedMoment δ T-NumericalGate.actual.re) (endpointMoment δ T)
  rw [abs_of_nonneg hen] at h
  have hh : trimmedMoment δ T+endpointMoment δ T-NumericalGate.actual.re =
      (trimmedMoment δ T-NumericalGate.actual.re)+endpointMoment δ T := by ring
  rw [hh]
  exact h.trans_lt (by linarith)

#print axioms trimmedMoment_eq
#print axioms fullMoment_eq
#print axioms weighted_integrable
#print axioms trimmed_integrable
#print axioms trimmedMoment_tendsto
#print axioms trimmedMean_tendsto
#print axioms trimmed_counting_bound
#print axioms width_budget
#print axioms trimmed_budget_bound
#print axioms iterated_width_limit
#print axioms sequential_unsmoothing
#print axioms full_integrable
#print axioms full_split
#print axioms fullMoment_tendsto_of_endpointTight
end XiPrime8845.WuUnsmoothing
