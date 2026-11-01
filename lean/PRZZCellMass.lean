import PRZZRowCellLayout
import PRZZSplitScaleSum

/-! Absolute coefficient mass for actual groups. Small-scale cells and
the complementary group of a free Type I factor get their own support
length, not the global N. Bounds on the remaining analytic factor are
explicit; no cancellation of that factor is asserted. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZCellMass
open PRZZActualBranchCells PRZZHBBranches
set_option maxHeartbeats 2000000

theorem upper_support (y K : ℕ) (js : List ℕ) (b : Branch)
    (hb : b ∈ branches y K js) (k : Fin b.2.length → ℕ)
    (s : Finset (Fin b.2.length)) (L : ℝ)
    (hl : (∏ i ∈ s, (2:ℝ)^(k i)) ≤ L) :
    (∏ i ∈ s, (2:ℝ)^(k i+1)) ≤ (2:ℝ)^((js.length+1)*(2*K))*L := by
  have hc : s.card ≤ (js.length+1)*(2*K) :=
    (card_le_card (subset_univ s)).trans (by
      simpa using PRZZBranchDegrees.branches_length y K js b hb)
  rw [PRZZSourceScales.upper_product]
  exact mul_le_mul (pow_le_pow_right₀ (by norm_num) hc) hl (by positivity) (by positivity)

theorem small_support (y K : ℕ) (js : List ℕ) (b : Branch)
    (hb : b ∈ branches y K js) (k : Fin b.2.length → ℕ) (U : ℝ)
    (hp : ∏ i, (2:ℝ)^(k i) = U)
    (hs : U ≤ 2*((2:ℝ)^((js.length+1)*(2*K)))) :
    (∏ i, (2:ℝ)^(k i+1)) ≤ 2*((2:ℝ)^((js.length+1)*(2*K)))^2 := by
  have ht := upper_support y K js b hb k univ _ hp.le
  have hh := mul_le_mul_of_nonneg_left hs (by positivity : (0:ℝ) ≤ 2^((js.length+1)*(2*K)))
  nlinarith

theorem typeI_support (y K : ℕ) (js : List ℕ) (b : Branch)
    (hb : b ∈ branches y K js) (k : Fin b.2.length → ℕ) (i : Fin b.2.length) (U : ℝ)
    (hs : (∏ r ∈ univ.erase i, (2:ℝ)^(k r)) < U^(1/4:ℝ)) :
    (∏ r ∈ univ.erase i, (2:ℝ)^(k r+1)) ≤
      (2:ℝ)^((js.length+1)*(2*K))*U^(1/4:ℝ) :=
  upper_support y K js b hb k _ _ hs.le

/-- The same constant covers every branch, group, local cutoff and mask.
Only the supplied bound B for the remaining factor is used. -/
theorem weighted_mass (K : ℕ) (js : List ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ N y b, b ∈ branches y K js →
      ∀ k : Fin b.2.length → ℕ, ∀ s : Finset (Fin b.2.length), ∀ L B : ℝ,
      1 ≤ L → 0 ≤ B → (∏ i ∈ s, (2:ℝ)^(k i+1)) ≤ L →
      ∀ z : ℕ → ℂ, (∀ n ∈ Icc 1 N, ‖z n‖ ≤ B) →
      ‖∑ n ∈ Icc 1 N, (group N b k s n:ℂ)*z n‖ ≤ C*L^eta*L*B := by
  obtain ⟨C,hC,h⟩ := common_rectangle K js eta heta
  refine ⟨C,hC,?_⟩
  intro N y b hb k s L B hL hB hs z hz
  let M := min N ⌊L⌋₊
  have he : (∑ n ∈ Icc 1 M, (group N b k s n:ℂ)*z n) =
      ∑ n ∈ Icc 1 N, (group N b k s n:ℂ)*z n := by
    apply sum_subset (Icc_subset_Icc le_rfl (min_le_left _ _))
    intro n hn hnot
    have hg : group N b k s n = 0 := by
      by_contra hg
      have hnL : (n:ℝ) ≤ L := (show (n:ℝ) ≤ ∏ i ∈ s, (2:ℝ)^(k i+1) by
        exact_mod_cast (group_support N b k s n hg).2).trans hs
      have hf : n ≤ ⌊L⌋₊ := (Nat.le_floor_iff (by linarith)).mpr hnL
      exact hnot (mem_Icc.mpr ⟨(mem_Icc.mp hn).1,le_min (mem_Icc.mp hn).2 hf⟩)
    simp [hg]
  rw [← he]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ Icc 1 M, (C*L^eta)*B := by
      apply sum_le_sum
      intro n hn
      have hc := h N y b hb k s Set.univ (fun _ => 1) (by simp) L hL n
        (mem_Icc.mpr ⟨(mem_Icc.mp hn).1,(mem_Icc.mp hn).2.trans (min_le_right _ _)⟩)
      simp only [Set.indicator_univ,mul_one] at hc
      rw [norm_mul]
      exact mul_le_mul hc (hz n (mem_Icc.mpr ⟨(mem_Icc.mp hn).1,
        (mem_Icc.mp hn).2.trans (min_le_left _ _)⟩)) (norm_nonneg _) (by positivity)
    _ = (M:ℝ)*(C*L^eta*B) := by simp
    _ ≤ L*(C*L^eta*B) := mul_le_mul_of_nonneg_right
      ((by exact_mod_cast (min_le_right N ⌊L⌋₊) : (M:ℝ) ≤ ⌊L⌋₊).trans
        (Nat.floor_le (by linarith))) (by positivity)
    _ = _ := by ring

/-- Sum the actual supported h coefficients after the group-mass bound.
The groups, cutoffs and analytic factors may differ with h. Only a common
support length and the bound on the remaining analytic factor are inputs. -/
theorem supported_sum (K : ℕ) (ks js : List ℕ) (r : ℕ)
    (eta beta : ℝ) (heta : 0 < eta) (hbeta : 0 < beta) :
    ∃ C : ℝ, 0 < C ∧ ∀ N d : ℕ, 1 ≤ N → 1 ≤ d →
      ∀ sigma L B : ℝ, sigma ≤ 0 → 1 ≤ L → 0 ≤ B → ∀ H : Finset ℕ,
      (∀ h ∈ H, 1 ≤ h ∧ d*h ≤ N ∧ SmoothMobius.supported d h) →
      ∀ y : ℕ → ℕ, ∀ b : ℕ → Branch,
      (∀ h ∈ H, b h ∈ branches (y h) K ks) →
      ∀ k : (h : ℕ) → Fin (b h).2.length → ℕ,
      ∀ s : (h : ℕ) → Finset (Fin (b h).2.length),
      (∀ h ∈ H, (∏ i ∈ s h, (2:ℝ)^(k h i+1)) ≤ L) →
      ∀ z : ℕ → ℕ → ℂ, (∀ h ∈ H, ∀ n ∈ Icc 1 N, ‖z h n‖ ≤ B) →
      ‖∑ h ∈ H, (PRZZGCoefficient.sourceG js r sigma d h:ℂ)*
        ∑ n ∈ Icc 1 N, (group N (b h) (k h) (s h) n:ℂ)*z h n‖ ≤
        C*(d:ℝ)^eta*(N:ℝ)^beta*L^eta*L*B := by
  obtain ⟨Cg,hCg,hg⟩ := weighted_mass K ks eta heta
  obtain ⟨Ch,hCh,hh⟩ := PRZZSplitScaleSum.absolute_mass js r eta beta heta hbeta
  refine ⟨Cg*Ch,mul_pos hCg hCh,?_⟩
  intro N d hN hd sigma L B hsig hL hB H hH y b hb k s hs z hz
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ h ∈ H, |PRZZGCoefficient.sourceG js r sigma d h| * (Cg*L^eta*L*B) := by
      apply sum_le_sum; intro h hmem
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        (hg N (y h) (b h) (hb h hmem) (k h) (s h) L B hL hB (hs h hmem) (z h) (hz h hmem))
        (abs_nonneg _)
    _ = (∑ h ∈ H, |PRZZGCoefficient.sourceG js r sigma d h|)*(Cg*L^eta*L*B) := by rw [sum_mul]
    _ ≤ (Ch*(d:ℝ)^eta*(N:ℝ)^beta)*(Cg*L^eta*L*B) :=
      mul_le_mul_of_nonneg_right (hh sigma d N hsig hd hN H hH) (by positivity)
    _ = _ := by ring

#print axioms supported_sum
#print axioms upper_support
#print axioms small_support
#print axioms typeI_support
#print axioms weighted_mass
end XiPrime8845.PRZZCellMass
