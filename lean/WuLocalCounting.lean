import WuQuotientReturn

/-! An actual local counting inequality after returning to the original left
line. No contour, Littlewood identity, zero-free left side, or counting
inequality is supplied by the caller. The finite count is closed at both
endpoints; conversion to a half-open cumulative count is a separate step. -/
noncomputable section
open scoped BigOperators
open Set Filter Topology MeasureTheory Complex
namespace XiPrime8845.WuLocalCounting
open WuLittlewood WuAuxiliary WuAuxiliaryBoundary WuQuotientReturn WuGammaPhase WuStirling
set_option maxHeartbeats 2000000

/-- A positive majorant, rather than the possibly negative actual boundary
integral, permits elimination of the existential parallel side. -/
theorem divide_positive_budget (d d₀ x q : ℝ) (hd₀ : 0 < d₀)
    (hd : d₀ ≤ d) (hq : 0 ≤ q) (h : d*x ≤ q) : x ≤ q/d₀ := by
  apply (le_div_iff₀ hd₀).mpr
  by_cases hx : 0 ≤ x
  · have hh := mul_le_mul_of_nonneg_right hd hx
    nlinarith
  · have hh := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hx) hd₀.le
    exact hh.trans hq

def boundaryBudget (T u v ε : ℝ) : ℝ :=
  (v-u)*Real.log WitnessMomentBound.countingCap/2+ε*(v-u)+1+
    3*Real.pi+6*WuHorizontalBound.phaseConstant*Real.log T

def countLower (T u v ε : ℝ) : ℝ :=
  (v-u)*Real.log T/2-
    (firstConstant*(v-u)+2*WuVHorizontal.phaseConstant*Real.log T+Real.pi)-
    Real.pi-1-boundaryBudget T u v ε*Real.log T/PRZZAsymptotic.R

/-- Uniform over both independently chosen inward endpoints, with only
their safety for this frozen auxiliary required. The original height and
mollifier are unchanged. -/
theorem closed_count_lower (δ ε : ℝ) (hδ : 0 < δ) (hd : δ < 1/2) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop,
      ∀ u ∈ Icc ((1+δ)*T) ((1+δ)*T+1),
      ∀ v ∈ Icc ((2-δ)*T-1) ((2-δ)*T), u ≤ v →
      u ∉ WuSafeEndpoints.badHeights (auxiliary T) →
      v ∉ WuSafeEndpoints.badHeights (auxiliary T) →
      ∃ S : Finset ℂ,
        (∀ s, s ∈ S ↔ s ∈ critical '' Icc u v ∧
          Zeta23.XiPrime.xiDeriv s = 0) ∧
        countLower T u v ε ≤
          Real.pi*(∑ s ∈ S, (analyticOrderNatAt Zeta23.XiPrime.xiDeriv s:ℝ)) := by
  have hR := PRZZAsymptotic.radius_pos
  filter_upwards [WuEtaMainPhase.gamma_free_merger,original_budget δ hδ hd,
    WuRightBoundary.right_nonzero,WuRightBoundary.rightLog_integral_bound ε hε,
    eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (32*PRZZAsymptotic.R))]
    with T hmerge hleft hright hrightLog hT hlarge
  intro u hu v hv huv hsu hsv
  have hL : 0 < Real.log T := Real.log_pos hT
  have hTu : T ≤ u := by nlinarith [hu.1]
  have hvT : v ≤ 2*T := by nlinarith [hv.2]
  have hu0 : 0 < u := (by linarith : 0 < T).trans_le hTu
  let a : ℝ := 1/2-PRZZAsymptotic.R/Real.log T
  have hra : PRZZAsymptotic.R/Real.log T < 1/32 :=
    (div_lt_iff₀ hL).mpr (by linarith)
  have ha : 7/16 < a := by dsimp [a]; linarith
  have ha' : a < 1/2 := by dsimp [a]; exact sub_lt_self _ (div_pos hR hL)
  obtain ⟨x,hx,hnx,hret⟩ := WuQuotientReturn.exists_safe_left T a u v 1 (a-7/16)
    hT (by linarith) hu0 huv (by norm_num) (by linarith)
  have hx7 : 7/16 ≤ x := by linarith [hx.1]
  have hx0 : 0 < x := by linarith
  have hxhalf : x < 1/2 := hx.2.trans ha'
  have hnr (t : ℝ) (ht : t ∈ Icc u v) := hright t ⟨hTu.trans ht.1,ht.2.trans hvT⟩
  obtain ⟨Z,q,hZ,hq⟩ := WuSafeEndpoints.littlewood_of_safe_heights (auxiliary T) x 3 u v
    (by linarith) huv (fun z _ => (auxiliary_entire T).analyticAt z) hsu hsv
    (fun t _ => hnx t) hnr
  have hn := WuSafeEndpoints.boundary_nonzero (auxiliary T) x 3 u v
    (by linarith) huv hsu hsv (fun t _ => hnx t) hnr
  obtain ⟨S,hS,hs⟩ := hmerge x u v hx7 hxhalf hTu huv hvT hsu hsv hn Z hZ q hq
  refine ⟨S,hS,?_⟩
  obtain ⟨c,hc,hcount⟩ := hs 1 (by norm_num)
  rw [quotient_integral_eq T x u v hT hx0 hu0 huv] at hcount
  have hr := (abs_le.mp (hrightLog u v hTu huv hvT)).1
  have hri : (∫ t in u..v, Real.log ‖V T (point 3 t)*psi T (point 3 t)‖) =
      ∫ t in Icc u v, WuRightBoundary.rightLog T t := by
    rw [intervalIntegral.integral_of_le huv,← integral_Icc_eq_integral_Ioc]
    rfl
  rw [← hri] at hr
  have hl := hleft u hu v hv
  change logIntegral T a u v ≤ _ at hl
  have hK : 0 ≤ WuHorizontalBound.phaseConstant := WuHorizontalBound.phaseConstant_pos.le
  have hKL : 0 ≤ WuHorizontalBound.phaseConstant*Real.log T := mul_nonneg hK hL.le
  have hQ : 0 ≤ boundaryBudget T u v ε := by
    have hcap : 0 ≤ Real.log WitnessMomentBound.countingCap :=
      Real.log_nonneg (by norm_num [WitnessMomentBound.countingCap])
    unfold boundaryBudget
    positivity
  have hbound : (c-x)*((v-u)*Real.log T/2-
      (firstConstant*(v-u)+2*WuVHorizontal.phaseConstant*Real.log T+Real.pi)-
      Real.pi*((∑ s ∈ S, (analyticOrderNatAt Zeta23.XiPrime.xiDeriv s:ℝ))+1)-1) ≤
      boundaryBudget T u v ε := by
    unfold boundaryBudget
    nlinarith [Real.pi_pos,mul_nonneg hx0.le hKL]
  have hd0 : PRZZAsymptotic.R/Real.log T ≤ c-x := by
    dsimp [a] at hx
    linarith [hc.1,hx.2]
  have hf := divide_positive_budget _ _ _ _ (div_pos hR hL) hd0 hQ hbound
  rw [div_div_eq_mul_div] at hf
  unfold countLower
  linarith

#print axioms divide_positive_budget
#print axioms closed_count_lower
end XiPrime8845.WuLocalCounting
