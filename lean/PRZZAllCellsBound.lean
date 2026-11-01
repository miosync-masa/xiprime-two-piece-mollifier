import PRZZAllSignedSources
import PRZZSplitScaleSum

/-! Aggregate actual local cells through supported h, labelled allocations,
and both outer dyadic indices. The analytic cell envelope is an explicit
input; branch weights, cutoffs, multiplicities and the G average are supplied.
No Weil/DI estimate or source-scale comparison is silently assumed. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZAllCellsBound
open PRZZAllSignedSources PRZZCoefficientSeparation PRZZSupportedSplit PRZZGCoefficient
set_option maxHeartbeats 2000000

/-- The two outside dyadic sums cost only a fixed subpower. -/
theorem outer_sum_bound (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ T B : ℝ,
      (N:ℝ) ≤ T → 1 ≤ Real.log T → 0 ≤ B → ∀ z : ℕ → ℕ → ℂ,
      (∀ j ∈ range (Nat.log 2 N+1), ∀ l ∈ range (Nat.log 2 N+1), ‖z j l‖ ≤ B) →
      ‖∑ j ∈ range (Nat.log 2 N+1), ∑ l ∈ range (Nat.log 2 N+1), z j l‖ ≤ C*T^eta*B := by
  obtain ⟨C,hC,h⟩ := PRZZDyadicBudget.grids_absorbed 2 eta heta
  refine ⟨C,hC,?_⟩
  intro N hN T B hNT hL hB z hz
  have hb := (norm_sum_le _ _).trans (sum_le_sum (fun j hj =>
    (norm_sum_le _ _).trans (sum_le_sum (fun l hl => hz j hj l hl))))
  have he : (∑ j ∈ range (Nat.log 2 N+1), ∑ l ∈ range (Nat.log 2 N+1), B) =
      (Nat.log 2 N+1:ℝ)^2*B := by simp; ring
  rw [he] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right (h N hN T hNT hL 2 le_rfl) hB)

/-- Uniform local block bounds give an allocation bound, including the
absolute supported G mass. The list is not deduplicated. -/
theorem allocation_bound (js : List ℕ) (eta beta : ℝ)
    (heta : 0 < eta) (hbeta : 0 < beta) :
    ∃ C : ℝ, 0 < C ∧ ∀ d N : ℕ, 1 ≤ d → 1 ≤ N →
      ∀ B : (List ℕ × List ℕ) → ℝ, ∀ z : (List ℕ × List ℕ) → ℕ → ℂ,
      (∀ q ∈ allocations js, 0 ≤ B q) →
      (∀ q ∈ allocations js, ∀ h ∈ hSupport N d, ‖z q h‖ ≤ B q) →
      ‖((allocations js).map (fun q => ∑ h ∈ hSupport N d,
        (sourceG q.1 0 0 d h:ℂ)*z q h)).sum‖ ≤
        C*(d:ℝ)^eta*(N:ℝ)^beta*((allocations js).map B).sum := by
  choose c hc hg using fun q : List ℕ × List ℕ =>
    PRZZSplitScaleSum.absolute_mass q.1 0 eta beta heta hbeta
  let C := ((allocations js).map c).sum+1
  have hcs : 0 ≤ ((allocations js).map c).sum := by
    apply List.sum_nonneg
    intro v hv
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hv
    exact (hc q).le
  refine ⟨C,by dsimp [C]; linarith,?_⟩
  intro d N hd hN B z hB hz
  have hq (q) (hq : q ∈ allocations js) :
      ‖∑ h ∈ hSupport N d, (sourceG q.1 0 0 d h:ℂ)*z q h‖ ≤
        C*(d:ℝ)^eta*(N:ℝ)^beta*B q := by
    have hm := hg q 0 d N le_rfl hd hN (hSupport N d)
      (fun h hh => mem_hSupport N d h hh)
    have hcq : c q ≤ C := by
      have hh := List.single_le_sum (fun v hv => by
        obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hv
        exact (hc r).le) (c q) (List.mem_map.mpr ⟨q,hq,rfl⟩)
      dsimp [C]; linarith
    calc
      _ ≤ ∑ h ∈ hSupport N d, |sourceG q.1 0 0 d h| * B q := by
        apply (norm_sum_le _ _).trans
        apply sum_le_sum; intro h hh
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hz q hq h hh) (abs_nonneg _)
      _ = (∑ h ∈ hSupport N d, |sourceG q.1 0 0 d h|)*B q := by rw [sum_mul]
      _ ≤ (c q*(d:ℝ)^eta*(N:ℝ)^beta)*B q := mul_le_mul_of_nonneg_right hm (hB q hq)
      _ ≤ _ := by gcongr; exact hB q hq
  have hs (qs : List (List ℕ × List ℕ)) (hs : ∀ q ∈ qs, q ∈ allocations js) :
      ‖(qs.map (fun q => ∑ h ∈ hSupport N d, (sourceG q.1 0 0 d h:ℂ)*z q h)).sum‖ ≤
        C*(d:ℝ)^eta*(N:ℝ)^beta*(qs.map B).sum := by
    induction qs with
    | nil => simp
    | cons q qs ih =>
      simp only [List.map_cons,List.sum_cons,mul_add]
      exact (norm_add_le _ _).trans (add_le_add (hq q (hs q (by simp)))
        (ih (fun r hr => hs r (by simp [hr]))))
  exact hs _ (fun q hq => hq)

#print axioms outer_sum_bound
#print axioms allocation_bound
end XiPrime8845.PRZZAllCellsBound
