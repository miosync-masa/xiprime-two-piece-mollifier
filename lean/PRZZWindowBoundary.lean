import PRZZWindowNativeTail
import PRZZNativeGcdGrid
import PRZZResolvedBoundary

/-! The actual sharp cover-boundary, not an assembled surrogate field,
vanishes on the complete polynomial M window once L>=4NT^b. Native gap
sets may grow with L; no gap-count or arithmetic-mass bound is needed. -/
noncomputable section
open scoped BigOperators
open Finset Complex MeasureTheory Filter Set
namespace XiPrime8845.PRZZWindowBoundary
open PRZZWindowGrids PRZZNativeComponents
set_option maxHeartbeats 6000000
attribute [local instance] Classical.propDecidable

def part (which : Part) (L J N : ℕ) (F F1 F2 : ℝ → ℂ) (a : ℕ → ℂ)
    (T b t : ℝ) (alpha beta : ℂ) : ℂ :=
  ∑ k ∈ spatial L T b, ∑ d ∈ Finset.Icc 1 N,
    ∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
      if PRZZDiagonalAssembly.admissible N d u v then
        ∑ delta ∈ PRZZNativeFamily.gaps L N (d*u) (d*v), if delta ≠ 0 then
          row which L J F F1 F2 ((2:ℝ)^k) ((u,v),(-delta,1)) alpha beta a d t
        else 0 else 0

def resolved (L J N : ℕ) (F F1 F2 : ℝ → ℂ) (a : ℕ → ℂ)
    (T b t : ℝ) (alpha beta : ℂ) : ℂ :=
  ∑ k ∈ spatial L T b, ∑ d ∈ Finset.Icc 1 N,
    ∑ u ∈ Finset.Icc 1 N, ∑ v ∈ Finset.Icc 1 N,
      if PRZZDiagonalAssembly.admissible N d u v then
        ∑ delta ∈ PRZZNativeFamily.gaps L N (d*u) (d*v), if delta ≠ 0 then
          PRZZAllPoissonRows.resolved L J F F1 F2 ((2:ℝ)^k)
            ((u,v),(-delta,1)) alpha beta a d t else 0 else 0

def originalPart (which : Part) (L J N : ℕ) (F F1 F2 : ℝ → ℂ) (a : ℕ → ℂ)
    (T b t : ℝ) (alpha beta : ℂ) : ℂ :=
  ∑ k ∈ spatial L T b, ∑ n ∈ Finset.Icc 1 N, ∑ r ∈ Finset.Icc 1 N,
    ∑ delta ∈ PRZZNativeFamily.gaps L N n r, if delta ≠ 0 then
      row which L J F F1 F2 ((2:ℝ)^k)
        ((n/Nat.gcd n r,r/Nat.gcd n r),(-delta,1)) alpha beta a (Nat.gcd n r) t else 0

theorem original_part_eq (which : Part) (L J N : ℕ) (F F1 F2 : ℝ → ℂ) (a : ℕ → ℂ)
    (T b t : ℝ) (alpha beta : ℂ) :
    originalPart which L J N F F1 F2 a T b t alpha beta =
      part which L J N F F1 F2 a T b t alpha beta := by
  unfold originalPart part
  apply sum_congr rfl; intro k hk
  exact PRZZNativeGcdGrid.sum_reindex N (fun n r d u v =>
    ∑ delta ∈ PRZZNativeFamily.gaps L N n r, if delta ≠ 0 then
      row which L J F F1 F2 ((2:ℝ)^k) ((u,v),(-delta,1)) alpha beta a d t else 0)

theorem boundary_zero (L J N : ℕ) (F F1 F2 : ℝ → ℂ) (a : ℕ → ℂ)
    (T b t : ℝ) (alpha beta : ℂ) (hN : 1 ≤ N)
    (hsF : Function.support F ⊆ Set.Icc (1/2:ℝ) 3)
    (hL : 4*(N:ℝ)*T^b ≤ L) :
    part .boundary L J N F F1 F2 a T b t alpha beta = 0 := by
  unfold part
  apply sum_eq_zero; intro k hk
  apply sum_eq_zero; intro d hd
  apply sum_eq_zero; intro u hu
  apply sum_eq_zero; intro v hv
  split_ifs with hadm
  · apply sum_eq_zero; intro delta hg
    split_ifs with hne
    · unfold row
      dsimp only
      split_ifs with hsmall
      · have hz := PRZZResolvedBoundary.bounded_cover_zero L N (T^b) ((2:ℝ)^k) t F
          ((u,v),(-delta,1)) alpha beta (alpha+beta)
          (by exact_mod_cast hN) (by positivity) (mem_filter.mp hk).2
          (Finset.mem_Icc.mp hu).1 (Finset.mem_Icc.mp hu).2 (Finset.mem_Icc.mp hv).1 hsF hsmall hL
        simp only [hz,mul_zero]
      · rfl
    · rfl
  · rfl

theorem decomposition (L J N : ℕ) (F F1 F2 : ℝ → ℂ) (a : ℕ → ℂ)
    (T b t : ℝ) (alpha beta : ℂ) :
    resolved L J N F F1 F2 a T b t alpha beta =
      part .central L J N F F1 F2 a T b t alpha beta+
      part .tail L J N F F1 F2 a T b t alpha beta-
      part .boundary L J N F F1 F2 a T b t alpha beta+
      part .freeze L J N F F1 F2 a T b t alpha beta+
      part .outside L J N F F1 F2 a T b t alpha beta := by
  unfold resolved part
  simp_rw [row_decomposition]
  have he (p : Prop) [Decidable p] (a b c d e : ℂ) :
      (if p then a+b-c+d+e else 0) =
        (if p then a else 0)+(if p then b else 0)-(if p then c else 0)+
          (if p then d else 0)+(if p then e else 0) := by split_ifs <;> ring
  simp only [he,sum_add_distrib,sum_sub_distrib]

theorem resolved_eq_four (L J N : ℕ) (F F1 F2 : ℝ → ℂ) (a : ℕ → ℂ)
    (T b t : ℝ) (alpha beta : ℂ) (hN : 1 ≤ N)
    (hsF : Function.support F ⊆ Set.Icc (1/2:ℝ) 3) (hL : 4*(N:ℝ)*T^b ≤ L) :
    resolved L J N F F1 F2 a T b t alpha beta =
      part .central L J N F F1 F2 a T b t alpha beta+
      part .tail L J N F F1 F2 a T b t alpha beta+
      part .freeze L J N F F1 F2 a T b t alpha beta+
      part .outside L J N F F1 F2 a T b t alpha beta := by
  rw [decomposition,boundary_zero L J N F F1 F2 a T b t alpha beta hN hsF hL,sub_zero]

/-- Arbitrary time multipliers, including the genuine dual Gamma
quotient, are allowed because disappearance is exact before integration. -/
theorem boundary_integral_zero (L J N : ℕ) (F F1 F2 : ℝ → ℂ) (a : ℕ → ℂ)
    (T b : ℝ) (alpha beta : ℂ) (phi : ℝ → ℂ) (hN : 1 ≤ N)
    (hsF : Function.support F ⊆ Set.Icc (1/2:ℝ) 3) (hL : 4*(N:ℝ)*T^b ≤ L) :
    (∫ t in Set.Icc T (2*T), phi t*part .boundary L J N F F1 F2 a T b t alpha beta) = 0 := by
  simp_rw [boundary_zero L J N F F1 F2 a T b _ alpha beta hN hsF hL,mul_zero]
  simp

/-- Exact eventual removal on the original pair/label family. J and
the time multiplier may vary with L; neither produces a boundary loss. -/
theorem original_boundary_eventually (N : ℕ) (F F1 F2 : ℝ → ℂ) (a : ℕ → ℂ)
    (T b : ℝ) (alpha beta : ℂ) (J : ℕ → ℕ) (phi : ℕ → ℝ → ℂ) (hN : 1 ≤ N)
    (hsF : Function.support F ⊆ Set.Icc (1/2:ℝ) 3) :
    ∀ᶠ L : ℕ in atTop, (∫ t in Set.Icc T (2*T), phi L t*
      originalPart .boundary L (J L) N F F1 F2 a T b t alpha beta) = 0 := by
  obtain ⟨L0,hL0⟩ := exists_nat_ge (4*(N:ℝ)*T^b)
  filter_upwards [eventually_ge_atTop L0] with L hL
  have hLR : 4*(N:ℝ)*T^b ≤ L := hL0.trans (by exact_mod_cast hL)
  simp_rw [original_part_eq]
  exact boundary_integral_zero L (J L) N F F1 F2 a T b alpha beta (phi L) hN hsF hLR

#print axioms boundary_zero
#print axioms original_part_eq
#print axioms decomposition
#print axioms resolved_eq_four
#print axioms boundary_integral_zero
#print axioms original_boundary_eventually
end XiPrime8845.PRZZWindowBoundary
