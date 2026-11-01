import PRZZLocalReexpansion

/-! A bounded-support alternative to balanced DI for small residual scales.
The variation cost depends on the local support M, not the original N.
This is a trivial row bound, not the final h-averaged A* estimate. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZSmallRowVariation
open PRZZTypeI
set_option maxHeartbeats 2000000

theorem supported_variation (w : ℕ → ℂ) (M H : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ n, ‖w n‖ ≤ C) (hs : ∀ n, M < n → w n = 0) :
    variation (fun k => w (k+1)) H ≤ (1+2*(M:ℝ))*C := by
  have hd (k : ℕ) : ‖w (k+1+1)-w (k+1)‖ ≤ if k < M then 2*C else 0 := by
    by_cases hk : k < M
    · rw [if_pos hk]
      exact (norm_sub_le _ _).trans (by linarith [hw (k+1+1),hw (k+1)])
    · simp [hk,hs (k+1) (by omega),hs (k+1+1) (by omega)]
  have hb := sum_le_sum (fun k (_ : k ∈ range (H-1)) => hd k)
  rw [← sum_filter] at hb
  have hsub : (range (H-1)).filter (fun k => k < M) ⊆ range M := by
    intro k hk
    exact mem_range.mpr (mem_filter.mp hk).2
  have hh : (∑ k ∈ (range (H-1)).filter (fun k => k < M), (2*C:ℝ)) ≤
      ∑ k ∈ range M, (2*C:ℝ) :=
    sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => mul_nonneg (by norm_num) hC)
  have hc : (∑ k ∈ (range (H-1)).filter (fun k => k < M), (2*C:ℝ)) ≤ (M:ℝ)*(2*C) := by
    simpa using hh
  unfold variation
  dsimp only
  have he := hw (H-1+1)
  linarith

/-- Uniform in height and frequency when the actual row's upper support
is bounded by M. No derivative hypothesis or balanced partition is needed. -/
theorem actual_row (F1 : ℝ → ℂ) (hf : Continuous F1) (hs : HasCompactSupport F1)
    (S : ℝ) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N d j h M H : ℕ, ∀ T t : ℝ, ∀ α : ℂ,
      0 < d → 0 < h → 1 < T → (N:ℝ) ≤ T → |α.re| ≤ S/Real.log T →
      PRZZRowWindow.hi N d h j ≤ M →
      variation (fun k => PRZZResidualRow.weight N d j h F1 α t (k+1)) H ≤
        (1+2*(M:ℝ))*(C*Real.exp S) := by
  obtain ⟨C,hC,hb⟩ := PRZZRowWindow.weight_bound F1 hf hs S hS
  refine ⟨C,hC,?_⟩
  intro N d j h M H T t α hd hh hT hNT hα hM
  apply supported_variation _ M H _ (mul_nonneg hC (Real.exp_pos S).le)
    (hb N d j h T t α hT hNT hα)
  intro n hn
  rw [PRZZRowWindow.weight_eq N d h j hd hh]
  simp [PRZZMaskedVariation.mask,not_le.mpr (lt_of_le_of_lt hM hn)]

/-- At small U the local upper support c*U is bounded by c^2.
No assertion that such a box is balanced is made. -/
theorem small_scale (M : ℕ) (c U : ℝ) (hc : 0 ≤ c) (hU : U ≤ c)
    (hM : (M:ℝ) ≤ c*U) : M ≤ ⌊c^2⌋₊ := by
  apply (Nat.le_floor_iff (sq_nonneg c)).mpr
  exact hM.trans ((mul_le_mul_of_nonneg_left hU hc).trans_eq (by ring))

#print axioms supported_variation
#print axioms actual_row
#print axioms small_scale

theorem actual_small_row (F1 : ℝ → ℂ) (hf : Continuous F1) (hs : HasCompactSupport F1)
    (S : ℝ) (hS : 0 ≤ S) (c : ℝ) (hc : 0 ≤ c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N d j h H : ℕ, ∀ T t U : ℝ, ∀ α : ℂ,
      0 < d → 0 < h → 1 < T → (N:ℝ) ≤ T → |α.re| ≤ S/Real.log T →
      U ≤ c → (PRZZRowWindow.hi N d h j:ℝ) ≤ c*U →
      variation (fun k => PRZZResidualRow.weight N d j h F1 α t (k+1)) H ≤ C := by
  obtain ⟨C,hC,hb⟩ := actual_row F1 hf hs S hS
  refine ⟨(1+2*(⌊c^2⌋₊:ℝ))*(C*Real.exp S),by positivity,?_⟩
  intro N d j h H T t U α hd hh hT hNT hα hU hi
  exact hb N d j h _ H T t α hd hh hT hNT hα (small_scale _ c U hc hU hi)

#print axioms actual_small_row
end XiPrime8845.PRZZSmallRowVariation
