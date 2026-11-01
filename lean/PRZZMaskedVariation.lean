import PRZZTypeIVariation

/-! Sharp interval restrictions have two jumps, independent of height.
The smooth variation is retained; no N-fold endpoint cost is introduced. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZMaskedVariation
open PRZZTypeI
set_option maxHeartbeats 2000000

def mask (a b : ℕ) (w : ℕ → ℂ) (k : ℕ) : ℂ :=
  if a ≤ k ∧ k ≤ b then w k else 0

theorem mask_step (a b k : ℕ) (w : ℕ → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hk : ‖w k‖ ≤ C) (hk' : ‖w (k+1)‖ ≤ C) :
    ‖mask a b w (k+1)-mask a b w k‖ ≤ ‖w (k+1)-w k‖+
      (if k+1=a then C else 0)+(if k=b then C else 0) := by
  unfold mask
  split_ifs
  all_goals try simp only [sub_zero,zero_sub,norm_neg,norm_zero]
  all_goals first | omega | positivity | linarith [norm_nonneg (w (k+1)-w k)]

theorem mask_variation (a b H : ℕ) (w : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ k ≤ H, ‖w k‖ ≤ C) :
    variation (mask a b w) H ≤ variation w H+2*C := by
  have hend : ‖mask a b w (H-1)‖ ≤ ‖w (H-1)‖ := by
    unfold mask; split_ifs <;> simp
  have h1 : (∑ k ∈ range (H-1), if k+1=a then C else 0) ≤ C := by
    by_cases ha : a=0
    · simp [ha,hC]
    · have he (k : ℕ) : k+1=a ↔ k=a-1 := by omega
      simp_rw [he]
      simp only [sum_ite_eq']
      split_ifs <;> simp_all
  have h2 : (∑ k ∈ range (H-1), if k=b then C else 0) ≤ C := by
    simp only [sum_ite_eq']; split_ifs <;> simp_all
  have hh := sum_le_sum (fun k (hk : k ∈ range (H-1)) => mask_step a b k w C hC
    (hw k (by have := mem_range.mp hk; omega))
    (hw (k+1) (by have := mem_range.mp hk; omega)))
  simp only [sum_add_distrib] at hh
  unfold variation
  linarith

/-- The envelope constant stays outside all cutoff and height choices. -/
theorem mask_of_variation (a b H : ℕ) (w : ℕ → ℂ) (C D : ℝ)
    (hC : 0 ≤ C) (hw : ∀ k ≤ H, ‖w k‖ ≤ C) (hv : variation w H ≤ D) :
    variation (mask a b w) H ≤ D+2*C :=
  (mask_variation a b H w C hC hw).trans (add_le_add hv le_rfl)

#print axioms mask_step
#print axioms mask_variation
#print axioms mask_of_variation
end XiPrime8845.PRZZMaskedVariation
