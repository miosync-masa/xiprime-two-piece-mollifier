import WuSafeEndpoints
import WuWindowTiling

/-! Freeze the function in each window, then choose independent inward
horizontal edges. Only the ORIGINAL cumulative counts telescope. Unit-band
count bounds and local analytic counting inequalities remain explicit inputs;
no xi-prime strip bound or horizontal argument bound is asserted here. -/
noncomputable section
open scoped BigOperators
open Set Finset Filter Topology
namespace XiPrime8845.WuIndependentWindows
open WuSafeEndpoints WuLittlewood WuWindowTiling
set_option maxHeartbeats 1000000

/-- Both deleted bands have width less than one; the retained interval is
nonempty. The function is already fixed when these heights are selected. -/
theorem exists_inward_heights (f : ℂ → ℂ) (hf : (badHeights f).Countable)
    (l h : ℝ) (hlen : 2 < h-l) :
    ∃ u ∈ Ioo l (l+1), ∃ v ∈ Ioo (h-1) h,
      u < v ∧ u ∉ badHeights f ∧ v ∉ badHeights f := by
  obtain ⟨u,hu,huI⟩ := (hf.dense_compl ℝ).exists_between (show l < l+1 by linarith)
  obtain ⟨v,hv,hvI⟩ := (hf.dense_compl ℝ).exists_between (show h-1 < h by linarith)
  exact ⟨u,huI,v,hvI,by linarith [huI.2,hvI.1],hu,hv⟩

/-- Choice is inside each fixed window. There is no common terminal
parameter to avoid and no countability assumption on a moving diagonal. -/
theorem exists_independent_heights {ι : Type*} (F : ι → ℂ → ℂ) (l h : ι → ℝ)
    (hF : ∀ i, (badHeights (F i)).Countable) (hlen : ∀ i, 2 < h i-l i) :
    ∃ u v : ι → ℝ, ∀ i, u i ∈ Ioo (l i) (l i+1) ∧ v i ∈ Ioo (h i-1) (h i) ∧
      u i < v i ∧ u i ∉ badHeights (F i) ∧ v i ∉ badHeights (F i) := by
  classical
  choose u hu v hv hgood using fun i => exists_inward_heights (F i) (hF i) (l i) (h i) (hlen i)
  exact ⟨u,v,fun i => ⟨hu i,hv i,hgood i⟩⟩

/-- Enlarging a retained counting interval costs only B times the missing
TOTAL count. No endpoint estimate for the good count is necessary. -/
theorem counting_transfer (N G : ℝ → ℝ) (hG : Monotone G)
    (l u v h B e d : ℝ) (hB : 0 ≤ B) (hlu : l ≤ u) (hvh : v ≤ h)
    (hband : N u-N l+(N h-N v) ≤ d)
    (hlocal : B*(N v-N u)-e ≤ G v-G u) :
    B*(N h-N l)-(e+B*d) ≤ G h-G l := by
  have h1 := hG hlu
  have h2 := hG hvh
  have h3 := mul_le_mul_of_nonneg_left hband hB
  nlinarith

theorem unit_band_transfer (N G : ℝ → ℝ) (hN : Monotone N) (hG : Monotone G)
    (l u v h B e d : ℝ) (hB : 0 ≤ B)
    (hu : u ∈ Icc l (l+1)) (hv : v ∈ Icc (h-1) h)
    (hlower : N (l+1)-N l ≤ d) (hupper : N h-N (h-1) ≤ d)
    (hlocal : B*(N v-N u)-e ≤ G v-G u) :
    B*(N h-N l)-(e+2*B*d) ≤ G h-G l := by
  have hb : N u-N l+(N h-N v) ≤ 2*d := by
    have := hN hu.2
    have := hN hv.1
    linarith
  convert counting_transfer N G hG l u v h B e (2*d) hB hu.1 hv.2 hb hlocal using 1
  ring

/-- Independently trimmed cells feed the original telescoping increments.
The band supplier counts a fixed target, not the varying auxiliary functions. -/
theorem aggregate_independent (δ X B d : ℝ) (N G : ℝ → ℝ)
    (hN : Monotone N) (hG : Monotone G) (hB : 0 ≤ B)
    (n : ℕ) (u v e : ℕ → ℝ)
    (hu : ∀ j ∈ range n, u j ∈ Icc (boundary δ X (j+1)) (boundary δ X (j+1)+1))
    (hv : ∀ j ∈ range n, v j ∈ Icc (boundary δ X j-1) (boundary δ X j))
    (hlower : ∀ j ∈ range n, N (boundary δ X (j+1)+1)-N (boundary δ X (j+1)) ≤ d)
    (hupper : ∀ j ∈ range n, N (boundary δ X j)-N (boundary δ X j-1) ≤ d)
    (hlocal : ∀ j ∈ range n, B*(N (v j)-N (u j))-e j ≤ G (v j)-G (u j)) :
    B*(N X-N (boundary δ X n))-(∑ j ∈ range n, e j)-2*B*d*n ≤
      G X-G (boundary δ X n) := by
  have hh := aggregate_counting δ X B G N (fun j => e j+2*B*d) n (by
    intro j hj
    exact unit_band_transfer N G hN hG _ _ _ _ B (e j) d hB
      (hu j hj) (hv j hj) (hlower j hj) (hupper j hj) (hlocal j hj))
  simp only [sum_add_distrib,sum_const,card_range,nsmul_eq_mul] at hh
  linarith

/-- A logarithmic upper bound on the number of retained geometric cells.
The stopping condition is explicit and independent of safe-height choices. -/
theorem number_cells_bound (δ X : ℝ) (hδ : 0 < δ) (hd : δ < 1/2)
    (hX : 1 ≤ X) (n : ℕ) (hstop : ∀ j < n, 1 ≤ boundary δ X j) :
    (n:ℝ) ≤ 1+Real.log X/(-Real.log (ratio δ)) := by
  have hr := ratio_mem δ hδ hd
  have hl : 0 < -Real.log (ratio δ) := neg_pos.mpr (Real.log_neg hr.1 hr.2)
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hX
  cases n with
  | zero => simp only [Nat.cast_zero]; positivity
  | succ n =>
    have hb := Real.log_nonneg (hstop n (Nat.lt_succ_self n))
    rw [boundary,Real.log_mul (by linarith : X ≠ 0) (pow_ne_zero n hr.1.ne'),Real.log_pow] at hb
    have hn : (n:ℝ) ≤ Real.log X/(-Real.log (ratio δ)) :=
      (le_div_iff₀ hl).mpr (by nlinarith)
    exact_mod_cast (show (n:ℝ)+1 ≤ 1+Real.log X/(-Real.log (ratio δ)) by linarith)

/-- If each unit band costs C log X, the total deleted-band budget is
explicitly O(log^2 X), with delta fixed. This is not a proof of that supplier. -/
theorem band_budget_bound (δ X B C : ℝ) (hδ : 0 < δ) (hd : δ < 1/2)
    (hX : 1 ≤ X) (hB : 0 ≤ B) (hC : 0 ≤ C) (n : ℕ)
    (hstop : ∀ j < n, 1 ≤ boundary δ X j) :
    2*B*(C*Real.log X)*n ≤
      2*B*C*(Real.log X+Real.log X^2/(-Real.log (ratio δ))) := by
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hX
  have hh := mul_le_mul_of_nonneg_left (number_cells_bound δ X hδ hd hX n hstop)
    (show 0 ≤ 2*B*(C*Real.log X) by positivity)
  exact hh.trans_eq (by ring)

/-- The explicit deleted-band budget is negligible on the counting scale. -/
theorem band_budget_normalized_tendsto (δ B C : ℝ) (hδ : 0 < δ) (hd : δ < 1/2) :
    Tendsto (fun X : ℝ =>
      (2*B*C*(Real.log X+Real.log X^2/(-Real.log (ratio δ))))/(X*Real.log X))
      atTop (nhds 0) := by
  have hr := ratio_mem δ hδ hd
  have hl : -Real.log (ratio δ) ≠ 0 := (neg_pos.mpr (Real.log_neg hr.1 hr.2)).ne'
  have hlog : Tendsto (fun X : ℝ => Real.log X/X) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hh := (tendsto_inv_atTop_zero.add (hlog.div_const (-Real.log (ratio δ)))).const_mul (2*B*C)
  simp only [zero_div,add_zero,mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with X hX
  field_simp [hl,(show X ≠ 0 by linarith),(Real.log_pos hX).ne']

/-- Return to the original terminal X, retaining the low-height remainder.
The deleted-band term is explicit and vanishes after division by X log X.
Both the unit-band estimates and the analytic local counting inequality
are supplied hypotheses, not conclusions about the actual xi derivative. -/
theorem global_independent_bound (δ X K B C eps : ℝ)
    (hδ : 0 < δ) (hd : δ < 1/2) (hX : 1 ≤ X) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (N G : ℝ → ℝ) (hN : Monotone N) (hG : Monotone G) (hGn : ∀ x, 0 ≤ G x)
    (n : ℕ) (u v e : ℕ → ℝ)
    (hstop : ∀ j < n, 1 ≤ boundary δ X j) (hcut : boundary δ X n ≤ K)
    (hu : ∀ j ∈ range n, u j ∈ Icc (boundary δ X (j+1)) (boundary δ X (j+1)+1))
    (hv : ∀ j ∈ range n, v j ∈ Icc (boundary δ X j-1) (boundary δ X j))
    (hlower : ∀ j ∈ range n,
      N (boundary δ X (j+1)+1)-N (boundary δ X (j+1)) ≤ C*Real.log X)
    (hupper : ∀ j ∈ range n,
      N (boundary δ X j)-N (boundary δ X j-1) ≤ C*Real.log X)
    (hlocal : ∀ j ∈ range n, B*(N (v j)-N (u j))-e j ≤ G (v j)-G (u j))
    (herr : (∑ j ∈ range n, e j) ≤ eps*X*Real.log X) :
    B*N X-eps*X*Real.log X-
      2*B*C*(Real.log X+Real.log X^2/(-Real.log (ratio δ)))-B*N K ≤ G X := by
  have ha := aggregate_independent δ X B (C*Real.log X) N G hN hG hB
    n u v e hu hv hlower hupper hlocal
  have hb := band_budget_bound δ X B C hδ hd hX hB hC n hstop
  have hk := mul_le_mul_of_nonneg_left (hN hcut) hB
  have hg := hGn (boundary δ X n)
  nlinarith

#print axioms exists_inward_heights
#print axioms exists_independent_heights
#print axioms counting_transfer
#print axioms unit_band_transfer
#print axioms aggregate_independent
#print axioms number_cells_bound
#print axioms band_budget_bound
#print axioms band_budget_normalized_tendsto
#print axioms global_independent_bound
end XiPrime8845.WuIndependentWindows
