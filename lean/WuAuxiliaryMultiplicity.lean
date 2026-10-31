import WuBoundaryZeros

/-! Actual auxiliary multiplicities and zero-free vertical perturbations.
The odd part detects xi' with its full analytic order, and multiplying by
psi cannot decrease any zero order. This is not a phase-counting inequality:
horizontal bounds and passage back from perturbed sides remain separate. -/
noncomputable section
open scoped BigOperators
open Set Filter Topology
namespace XiPrime8845.WuAuxiliaryMultiplicity
open WuAuxiliary WuAuxiliaryBoundary WuBoundaryZeros WuLittlewood
set_option maxHeartbeats 2000000

theorem entire_order_ne_top (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hn : ∃ z, f z ≠ 0) (s : ℂ) : analyticOrderAt f s ≠ ⊤ := by
  intro he
  have hh := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero s (fun z => hf.analyticAt z)).mp he
  obtain ⟨z,hz⟩ := hn
  exact hz (congrFun hh z)

theorem auxiliary_order (T : ℝ) (hT : 1 < T) (s : ℂ) :
    analyticOrderNatAt (auxiliary T) s =
      analyticOrderNatAt (eta (Real.log T)) s+analyticOrderNatAt (psi T) s := by
  exact analyticOrderNatAt_mul ((eta_entire _).analyticAt s) ((psi_entire T).analyticAt s)
    (entire_order_ne_top _ (eta_entire _) (eta_not_identically_zero _ (Real.log_pos hT).ne') s)
    (entire_order_ne_top _ (psi_entire T) (psi_not_identically_zero T hT) s)

theorem eta_order_le_auxiliary (T : ℝ) (hT : 1 < T) (s : ℂ) :
    analyticOrderNatAt (eta (Real.log T)) s ≤ analyticOrderNatAt (auxiliary T) s := by
  rw [auxiliary_order T hT s]
  omega

/-- The antisymmetric holomorphic part, not a sign-change count. -/
def oddPart (L : ℝ) (s : ℂ) : ℂ := (eta L s-eta L (1-s))/2

theorem oddPart_eq (L : ℝ) (s : ℂ) :
    oddPart L s = ((rCoeff 1:ℂ)/(L:ℂ))*Zeta23.XiPrime.xiDeriv s := by
  rw [oddPart,eta_reflection_difference]
  ring

/-- Full complex analytic multiplicity agrees, including even orders.
Converting this identity into a variation-of-argument count is still required. -/
theorem oddPart_order (L : ℝ) (hL : L ≠ 0) (s : ℂ) :
    analyticOrderNatAt (oddPart L) s = analyticOrderNatAt Zeta23.XiPrime.xiDeriv s := by
  have hc : (rCoeff 1:ℂ)/(L:ℂ) ≠ 0 := div_ne_zero
    (by exact_mod_cast linear_coefficient_pos.ne') (by exact_mod_cast hL)
  have he : oddPart L = (fun _ : ℂ => (rCoeff 1:ℂ)/(L:ℂ))*Zeta23.XiPrime.xiDeriv :=
    funext (oddPart_eq L)
  have hc0 : analyticOrderAt (fun _ : ℂ => (rCoeff 1:ℂ)/(L:ℂ)) s = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr hc)
  rw [he,analyticOrderNatAt,analyticOrderAt_mul analyticAt_const
    (Zeta23.XiPrime.xiDeriv_differentiable.analyticAt s),
    hc0,zero_add]
  rfl

/-- Any finite selection in the right half of a rectangle gains, never
loses, Littlewood weight when the actual mollifier is multiplied in. -/
theorem weighted_eta_le_auxiliary (T a : ℝ) (hT : 1 < T) (Z : Finset ℂ)
    (hZ : ∀ s ∈ Z, a ≤ s.re) :
    (∑ s ∈ Z, (analyticOrderNatAt (eta (Real.log T)) s:ℝ)*(s.re-a)) ≤
      ∑ s ∈ Z, (analyticOrderNatAt (auxiliary T) s:ℝ)*(s.re-a) := by
  apply Finset.sum_le_sum
  intro s hs
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast eta_order_le_auxiliary T hT s)
    (sub_nonneg.mpr (hZ s hs))

/-- T is frozen. Both vertical sides can be chosen arbitrarily close on
the outside of prescribed sides. No uniform lower modulus is claimed. -/
theorem exists_safe_sides (T a b ε : ℝ) (hT : 1 < T) (hε : 0 < ε) :
    ∃ a' ∈ Ioo (a-ε) a, ∃ b' ∈ Ioo b (b+ε),
      (∀ t : ℝ, auxiliary T (point a' t) ≠ 0) ∧
      (∀ t : ℝ, auxiliary T (point b' t) ≠ 0) := by
  let bad : Set ℝ := Complex.re '' {s | auxiliary T s = 0}
  have hc : bad.Countable := (auxiliary_zeros_countable T hT).image _
  obtain ⟨a',ha',ha⟩ := (hc.dense_compl ℝ).exists_between (show a-ε < a by linarith)
  obtain ⟨b',hb',hb⟩ := (hc.dense_compl ℝ).exists_between (show b < b+ε by linarith)
  refine ⟨a',ha,b',hb,?_,?_⟩
  · intro t hz
    exact ha' ⟨point a' t,hz,by simp [point]⟩
  · intro t hz
    exact hb' ⟨point b' t,hz,by simp [point]⟩

/-- The actual function satisfies Littlewood on arbitrarily close outward
vertical perturbations, once safe horizontal heights have been selected.
This theorem does not identify the limit as epsilon tends to zero. -/
theorem littlewood_perturbed (T a b u v ε : ℝ) (hT : 1 < T) (hab : a ≤ b)
    (huv : u ≤ v) (hε : 0 < ε)
    (hu : u ∉ WuSafeEndpoints.badHeights (auxiliary T))
    (hv : v ∉ WuSafeEndpoints.badHeights (auxiliary T)) :
    ∃ a' ∈ Ioo (a-ε) a, ∃ b' ∈ Ioo b (b+ε),
      ∃ Z : Finset ℂ, ∃ q : BoundaryLogs (auxiliary T) a' b' u v,
        (∀ s, s ∈ Z ↔ s ∈ Complex.Rectangle (point a' u) (point b' v) ∧ auxiliary T s = 0) ∧
        2*Real.pi*(∑ s ∈ Z, (analyticOrderNatAt (auxiliary T) s:ℝ)*(s.re-a')) =
          boundaryLog (auxiliary T) a' b' u v q := by
  obtain ⟨a',ha,b',hb,hna,hnb⟩ := exists_safe_sides T a b ε hT hε
  refine ⟨a',ha,b',hb,?_⟩
  exact WuSafeEndpoints.littlewood_of_safe_heights _ _ _ _ _ (by linarith [ha.2,hb.1]) huv
    (fun s _ => (auxiliary_entire T).analyticAt s) hu hv (fun t _ => hna t) (fun t _ => hnb t)

#print axioms entire_order_ne_top
#print axioms auxiliary_order
#print axioms eta_order_le_auxiliary
#print axioms oddPart_eq
#print axioms oddPart_order
#print axioms weighted_eta_le_auxiliary
#print axioms exists_safe_sides
#print axioms littlewood_perturbed
end XiPrime8845.WuAuxiliaryMultiplicity
