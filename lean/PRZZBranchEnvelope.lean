import PRZZBranchDegrees

/-! Common subpower envelopes for every subgroup of every actual branch.
Constants precede y and the branch choice; scalar branch weights and dyadic
summation multiplicities are not included in this coefficient envelope. -/
noncomputable section
open scoped BigOperators
open ArithmeticFunction Finset
namespace XiPrime8845.PRZZBranchEnvelope
open PRZZBranchDegrees PRZZGroupBounds PRZZWeightedHeathBrown PRZZHBBranches
set_option maxHeartbeats 2000000

theorem bounded_atom (D : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ Y f, Bounded Y D f → ∀ n : ℕ, 0 < n →
      |f n| ≤ C*(n:ℝ)^eps := by
  choose c hc hb using fun j => atom_subpower j eps heps
  refine ⟨∑ j ∈ range (D+1), c j, sum_pos (fun j _ => hc j) (by simp),?_⟩
  intro Y f hf n hn
  obtain ⟨j,a,hj,_,rfl⟩ := hf
  exact (hb j a n hn).trans (mul_le_mul_of_nonneg_right
    (single_le_sum (fun k _ => (hc k).le) (mem_range.mpr (by omega)))
    (Real.rpow_nonneg (Nat.cast_nonneg _) _))

theorem bounded_product (D L : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ Y (fs : List (ArithmeticFunction ℝ)),
      fs.length ≤ L → (∀ f ∈ fs, Bounded Y D f) → ∀ n : ℕ, 0 < n →
      |fs.prod n| ≤ C*(n:ℝ)^eps := by
  induction L generalizing eps with
  | zero =>
    refine ⟨1,by norm_num,?_⟩
    intro Y fs hlen hf n hn
    have he : fs = [] := by cases fs <;> simp_all
    subst fs
    by_cases h : n=1
    · simp [h]
    · simp [one_apply,h,Real.rpow_nonneg (Nat.cast_nonneg n) eps]
  | succ L ih =>
    obtain ⟨C,hC,hc⟩ := bounded_atom D (eps/3) (by positivity)
    obtain ⟨B,hB,hb⟩ := ih (eps/3) (by positivity)
    obtain ⟨K,hK,hk⟩ := PRZZNuBounds.divisors_subpower (eps/3) (by positivity)
    refine ⟨C*B*K+1,by positivity,?_⟩
    intro Y fs hlen hf n hn
    cases fs with
    | nil =>
      by_cases h : n=1
      · simp only [List.prod_nil,h,one_apply,ite_true,Nat.cast_one,Real.one_rpow,mul_one,abs_one]
        have hp : 0 ≤ C*B*K := by positivity
        linarith
      · simp [one_apply,h]
        positivity
    | cons f fs =>
      have h := convolution_bound (eps/3) C B K (by positivity) hC.le hB.le f fs.prod
        (hc Y f (hf f (by simp)))
        (hb Y fs (by simpa using Nat.le_of_succ_le_succ hlen)
          (fun g hg => hf g (by simp [hg]))) hk n hn
      rw [show 3*(eps/3)=eps by ring] at h
      exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (Nat.cast_nonneg n) _))

/-- The same constant works for both complementary subgroups, in every
actual HB branch, without choosing envelopes separately for each branch. -/
theorem all_branch_subgroups (K : ℕ) (js : List ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ y b, b ∈ branches y K js →
      ∀ fs : List (ArithmeticFunction ℝ), fs.Sublist b.2 → ∀ n : ℕ, 0 < n →
        |fs.prod n| ≤ C*(n:ℝ)^eps := by
  obtain ⟨C,hC,h⟩ := bounded_product js.sum ((js.length+1)*(2*K)) eps heps
  refine ⟨C,hC,?_⟩
  intro y b hb fs hs n hn
  exact h y fs (hs.length_le.trans (branches_length y K js b hb))
    (fun f hf => branches_degrees y K js b hb f (hs.subset hf)) n hn

def mask (s : Set ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ := by
  classical
  exact ⟨fun n => if n ∈ s then f n else 0, by simp⟩

theorem mask_bounded (Y : ℝ) (D : ℕ) (f : ArithmeticFunction ℝ)
    (s : Set ℕ) (hf : Bounded Y D f) : Bounded Y D (mask s f) := by
  classical
  obtain ⟨j,a,hj,ha,rfl⟩ := hf
  refine ⟨j,Atom.restrict a s,hj,ha,?_⟩
  ext n
  change (if n ∈ s then Real.log n^j*atom a n else 0) =
    Real.log n^j*(if n ∈ s then atom a n else 0)
  split_ifs <;> simp

/-- Masks are attached to individual occurrences, so repeated factors may
have different dyadic supports. Unit twists and an outer mask cost nothing. -/
theorem masked_branch_subgroups (K : ℕ) (js : List ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ y b, b ∈ branches y K js →
      ∀ fs : List (ArithmeticFunction ℝ × Set ℕ), (fs.map Prod.fst).Sublist b.2 →
      ∀ s : Set ℕ, ∀ w : ℕ → ℂ, (∀ n, ‖w n‖ ≤ 1) → ∀ n : ℕ, 0 < n →
        ‖s.indicator (fun n => (((fs.map (fun p => mask p.2 p.1)).prod n:ℝ):ℂ)*w n) n‖ ≤
          C*(n:ℝ)^eps := by
  classical
  obtain ⟨C,hC,h⟩ := bounded_product js.sum ((js.length+1)*(2*K)) eps heps
  refine ⟨C,hC,?_⟩
  intro y b hb fs hs s w hw n hn
  have hl : (fs.map (fun p => mask p.2 p.1)).length ≤ (js.length+1)*(2*K) := by
    simpa using hs.length_le.trans (branches_length y K js b hb)
  have hf : ∀ f ∈ fs.map (fun p => mask p.2 p.1), Bounded y js.sum f := by
    intro f hf
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hf
    exact mask_bounded y js.sum p.1 p.2
      (branches_degrees y K js b hb p.1 (hs.subset (List.mem_map.mpr ⟨p,hp,rfl⟩)))
  by_cases hsn : n ∈ s
  · simp only [Set.indicator_of_mem hsn,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hw n) (abs_nonneg _)).trans
      (by simpa using h y _ hl hf n hn)
  · simp only [Set.indicator_of_notMem hsn,norm_zero]
    positivity

def coefficient (fs : List (ArithmeticFunction ℝ × Set ℕ)) (s : Set ℕ)
    (w : ℕ → ℂ) (n : ℕ) : ℂ :=
  s.indicator (fun n => (((fs.map (fun p => mask p.2 p.1)).prod n:ℝ):ℂ)*w n) n

theorem branch_rectangle (K : ℕ) (js : List ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ y b, b ∈ branches y K js →
      ∀ fs : List (ArithmeticFunction ℝ × Set ℕ), (fs.map Prod.fst).Sublist b.2 →
      ∀ s : Set ℕ, ∀ w : ℕ → ℂ, (∀ n, ‖w n‖ ≤ 1) →
      ∀ X : ℝ, 1 ≤ X → ∀ n ∈ Icc 1 ⌊X⌋₊, ‖coefficient fs s w n‖ ≤ C*X^eps := by
  obtain ⟨C,hC,h⟩ := masked_branch_subgroups K js eps heps
  refine ⟨C,hC,?_⟩
  intro y b hb fs hs s w hw X hX n hn
  exact (h y b hb fs hs s w hw n (mem_Icc.mp hn).1).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by positivity)
      ((Nat.cast_le.mpr (mem_Icc.mp hn).2).trans (Nat.floor_le (by linarith))) heps.le) hC.le)

#print axioms branch_rectangle
#print axioms masked_branch_subgroups
#print axioms bounded_atom
#print axioms bounded_product
#print axioms all_branch_subgroups
end XiPrime8845.PRZZBranchEnvelope
