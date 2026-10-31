import WuRightBoundary

/-! Actual right-edge supplier for Littlewood and a multiplicity-weighted
eta count. The horizontal boundary term is retained explicitly. This is
not a phase-to-xi-prime counting theorem or a completed local Wu inequality. -/
noncomputable section
open scoped BigOperators
open Filter Topology Set Finset MeasureTheory
namespace XiPrime8845.WuRightLittlewood
open WuAuxiliary WuAuxiliaryBoundary WuLittlewood WuAuxiliaryMultiplicity
set_option maxHeartbeats 2000000

/-- The former right nonvanishing hypothesis is now discharged uniformly
for the actual moving family. Only the left side is perturbed. -/
theorem littlewood_eventually : ∀ᶠ T : ℝ in atTop,
    ∀ a u v ε w : ℝ, a ≤ 3 → T ≤ u → u ≤ v → v ≤ 2*T → 0 < ε → 0 < w →
    u ∉ WuSafeEndpoints.badHeights (auxiliary T) →
    v ∉ WuSafeEndpoints.badHeights (auxiliary T) →
    ∃ x ∈ Ioo (a-w) a, ∃ Z : Finset ℂ, ∃ q : BoundaryLogs (auxiliary T) x 3 u v,
      (∀ s, s ∈ Z ↔ s ∈ Complex.Rectangle (point x u) (point 3 v) ∧ auxiliary T s = 0) ∧
      2*Real.pi*(∑ s ∈ Z, (analyticOrderNatAt (auxiliary T) s:ℝ)*(s.re-x)) =
        boundaryLog (auxiliary T) x 3 u v q ∧
      (∫ t in Icc u v, Real.log ‖auxiliary T (point x t)‖) <
        (∫ t in Icc u v, Real.log ‖auxiliary T (point a t)‖)+ε := by
  filter_upwards [WuRightBoundary.right_nonzero,eventually_gt_atTop (1:ℝ)] with T hn hT
  intro a u v ε w ha hu huv hv hε hw hsu hsv
  exact WuLeftReturn.littlewood_fixed_right T a 3 u v ε w hT ha huv hε hw hsu hsv
    (fun t ht => hn t ⟨hu.trans ht.1,ht.2.trans hv⟩)

/-- Full eta multiplicities, not sign changes or distinct-zero counts.
An arbitrary finite selection to the right of c is controlled by the
actual auxiliary Littlewood sum; psi zeros can only enlarge that sum. -/
theorem eta_count_le_weighted (T x c : ℝ) (hT : 1 < T) (hxc : x ≤ c)
    (W Z : Finset ℂ) (hWZ : W ⊆ Z)
    (hW : ∀ s ∈ W, c ≤ s.re) (hZ : ∀ s ∈ Z, x ≤ s.re) :
    (c-x)*(∑ s ∈ W, (analyticOrderNatAt (eta (Real.log T)) s:ℝ)) ≤
      ∑ s ∈ Z, (analyticOrderNatAt (auxiliary T) s:ℝ)*(s.re-x) := by
  rw [mul_sum]
  calc
    _ ≤ ∑ s ∈ W, (analyticOrderNatAt (eta (Real.log T)) s:ℝ)*(s.re-x) := by
      apply sum_le_sum
      intro s hs
      exact (mul_comm _ _).le.trans
        (mul_le_mul_of_nonneg_left (sub_le_sub_right (hW s hs) x) (Nat.cast_nonneg _))
    _ ≤ ∑ s ∈ W, (analyticOrderNatAt (auxiliary T) s:ℝ)*(s.re-x) :=
      weighted_eta_le_auxiliary T x hT W (fun s hs => hxc.trans (hW s hs))
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hWZ
      (fun s hs _ => mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (hZ s hs)))

/-- The boundary expression is deliberately not replaced by an assumed
horizontal phase bound. The next analytic supplier must bound that term. -/
theorem eta_count_le_boundary (T x c b u v : ℝ) (hT : 1 < T) (hxc : x ≤ c)
    (W Z : Finset ℂ) (hWZ : W ⊆ Z)
    (hW : ∀ s ∈ W, c ≤ s.re) (hZ : ∀ s ∈ Z, x ≤ s.re)
    (q : BoundaryLogs (auxiliary T) x b u v)
    (hl : 2*Real.pi*(∑ s ∈ Z, (analyticOrderNatAt (auxiliary T) s:ℝ)*(s.re-x)) =
      boundaryLog (auxiliary T) x b u v q) :
    2*Real.pi*(c-x)*(∑ s ∈ W, (analyticOrderNatAt (eta (Real.log T)) s:ℝ)) ≤
      boundaryLog (auxiliary T) x b u v q := by
  rw [← hl,mul_assoc]
  exact mul_le_mul_of_nonneg_left (eta_count_le_weighted T x c hT hxc W Z hWZ hW hZ)
    (by positivity)

#print axioms littlewood_eventually
#print axioms eta_count_le_weighted
#print axioms eta_count_le_boundary
end XiPrime8845.WuRightLittlewood
