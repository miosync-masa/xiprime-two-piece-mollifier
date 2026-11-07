import PRZZPartitionDiscrepancy
import PRZZDiagonalAssembly

/-! Literal gcd coefficients in the multiplicity-free source boundary
envelope. Spatial and gap families may grow arbitrarily with L; the
arithmetic grid N is fixed. This is not an identification of the original
resolved-family boundary with this assembled source lattice, nor a sharp
height estimate for its remaining finite arithmetic mass. -/
noncomputable section
open scoped BigOperators
open Finset MeasureTheory Filter Topology
namespace XiPrime8845.PRZZArithmeticBoundaryFamily
open PRZZPartitionMass PRZZSourceBoundaryDecay
set_option maxHeartbeats 4000000
attribute [local instance] Classical.propDecidable

def grid (N : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  (Icc 1 N ×ˢ Icc 1 N) ×ˢ Icc 1 N

def weight (N : ℕ) (a : ℕ → ℂ) (F1 F2 : ℝ → ℂ) (alpha beta : ℂ)
    (i : (ℕ × ℕ) × ℕ) : ℂ :=
  if PRZZDiagonalAssembly.admissible N i.1.1 i.1.2 i.2 then
    PRZZDiagonalAssembly.coefficient a F1 F2 alpha beta i.1.1 i.1.2 i.2 else 0

def mass (N : ℕ) (a : ℕ → ℂ) (F1 F2 : ℝ → ℂ)
    (alpha beta sigma : ℂ) (T : ℝ) : ℝ :=
  outerMass (grid N) (weight N a F1 F2 alpha beta) (fun i => i.1.2) (fun i => i.2)
    T alpha beta sigma

/-- Exact finite arithmetic mass; no cardinality of the gap or spatial
partition appears, and all original cutoff values remain in coefficient. -/
theorem mass_eq (N : ℕ) (a : ℕ → ℂ) (F1 F2 : ℝ → ℂ)
    (alpha beta sigma : ℂ) (T : ℝ) :
    mass N a F1 F2 alpha beta sigma T =
      ∑ d ∈ Icc 1 N, ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N,
        if PRZZDiagonalAssembly.admissible N d u v then
          ‖PRZZDiagonalAssembly.coefficient a F1 F2 alpha beta d u v‖ *
            cap 1 T ((u,v),(0,0)) alpha beta sigma else 0 := by
  classical
  unfold mass outerMass grid
  simp only [sum_product]
  apply sum_congr rfl
  intro d hd
  apply sum_congr rfl
  intro u hu
  apply sum_congr rfl
  intro v hv
  simp only [weight]
  split_ifs <;> simp

def field (N : ℕ) (a : ℕ → ℂ) (F1 F2 : ℝ → ℂ) (S : ℝ → ℝ)
    (M t : ℝ) (alpha beta sigma : ℂ) (K : ℕ) (D : Finset ℤ) (p : ℕ × ℕ) : ℂ :=
  assembled (grid N) (weight N a F1 F2 alpha beta) (fun i => i.1.2) (fun i => i.2)
    S M t alpha beta sigma K D p

theorem field_bound (N : ℕ) (a : ℕ → ℂ) (F1 F2 : ℝ → ℂ)
    (S : ℝ → ℝ) (hm : Antitone S) (hlo : ∀ x, 0 ≤ S x) (hhi : ∀ x, S x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), S x = 1) (hright : ∀ x, 1 ≤ x → S x = 0)
    (M T t : ℝ) (alpha beta sigma : ℂ) (hM : 0 < M) (hT : 0 < T)
    (ht : t ∈ Set.Icc T (2*T)) (hs : sigma ≠ 0) (hab : 0 ≤ (alpha+beta+1).re)
    (K : ℕ) (D : Finset ℤ) (p : ℕ × ℕ) :
    ‖field N a F1 F2 S M t alpha beta sigma K D p‖ ≤
      mass N a F1 F2 alpha beta sigma T * majorant p := by
  apply assembled_bound _ _ _ _ S hm hlo hhi hleft hright M T t alpha beta sigma
    hM hT ht _ _ hs hab K D p
  · intro i hi
    exact (mem_Icc.mp (mem_product.mp (mem_product.mp hi).1).2).1
  · intro i hi
    exact (mem_Icc.mp (mem_product.mp hi).2).1

/-- One fixed computed arithmetic mass dominates all growing K(L), D(L),
and containing boxes B(L), before taking the weighted time limit. -/
theorem boundary_time_zero (N : ℕ) (a : ℕ → ℂ) (F1 F2 : ℝ → ℂ)
    (S : ℝ → ℝ) (hm : Antitone S) (hlo : ∀ x, 0 ≤ S x) (hhi : ∀ x, S x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), S x = 1) (hright : ∀ x, 1 ≤ x → S x = 0)
    (M T : ℝ) (alpha beta sigma : ℂ) (hM : 0 < M) (hT : 0 < T)
    (hs : sigma ≠ 0) (hab : 0 ≤ (alpha+beta+1).re)
    (K B : ℕ → ℕ) (D : ℕ → Finset ℤ) (hLB : ∀ L, L ≤ B L)
    (phi : ℝ → ℂ) (hphi : Continuous phi) :
    Tendsto (fun L => ∫ t in Set.Icc T (2*T), phi t *
      ∑ p ∈ (range (B L) ×ˢ range (B L)) \ (range L ×ˢ range L),
        field N a F1 F2 S M t alpha beta sigma (K L) (D L) p) atTop (𝓝 0) := by
  apply assembled_integral_zero _ _ _ _ S hm hlo hhi hleft hright M T alpha beta sigma
    hM hT _ _ hs hab K B D hLB phi hphi
  · intro i hi
    exact (mem_Icc.mp (mem_product.mp (mem_product.mp hi).1).2).1
  · intro i hi
    exact (mem_Icc.mp (mem_product.mp hi).2).1

/-- Row-dependent containing boxes and active filters can be retained as
literal masks. Removing a term never increases the pointwise norm budget. -/
def maskedField (N : ℕ) (a : ℕ → ℂ) (F1 F2 : ℝ → ℂ) (S : ℝ → ℝ)
    (M t : ℝ) (alpha beta sigma : ℂ) (K : ℕ) (D : Finset ℤ)
    (keep : ((ℕ × ℕ) × ℕ) → ℕ → ℤ → (ℕ × ℕ) → Prop) (p : ℕ × ℕ) : ℂ := by
  classical
  exact ∑ i ∈ grid N, weight N a F1 F2 alpha beta i *
    ∑ j ∈ range K, ∑ delta ∈ D, if keep i j delta p then
      configuration S ((2:ℝ)^j*M) t i.1.2 i.2 alpha beta sigma delta p else 0

theorem masked_bound (N : ℕ) (a : ℕ → ℂ) (F1 F2 : ℝ → ℂ)
    (S : ℝ → ℝ) (hm : Antitone S) (hlo : ∀ x, 0 ≤ S x) (hhi : ∀ x, S x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), S x = 1) (hright : ∀ x, 1 ≤ x → S x = 0)
    (M T t : ℝ) (alpha beta sigma : ℂ) (hM : 0 < M) (hT : 0 < T)
    (ht : t ∈ Set.Icc T (2*T)) (hs : sigma ≠ 0) (hab : 0 ≤ (alpha+beta+1).re)
    (K : ℕ) (D : Finset ℤ)
    (keep : ((ℕ × ℕ) × ℕ) → ℕ → ℤ → (ℕ × ℕ) → Prop) (p : ℕ × ℕ) :
    ‖maskedField N a F1 F2 S M t alpha beta sigma K D keep p‖ ≤
      mass N a F1 F2 alpha beta sigma T * majorant p := by
  classical
  unfold maskedField mass outerMass
  apply (norm_sum_le _ _).trans
  rw [sum_mul]
  apply sum_le_sum
  intro i hi
  rw [norm_mul,mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (norm_sum_le _ _).trans
  apply (sum_le_sum (fun j _ => norm_sum_le _ _)).trans
  apply le_trans _ (configuration_mass S hm hlo hhi hleft hright M T t i.1.2 i.2
    alpha beta sigma hM hT ht
    (mem_Icc.mp (mem_product.mp (mem_product.mp hi).1).2).1
    (mem_Icc.mp (mem_product.mp hi).2).1 hs hab K D p)
  apply sum_le_sum
  intro j hj
  apply sum_le_sum
  intro delta hd
  split_ifs
  · exact le_rfl
  · simpa only [norm_zero] using
      (norm_nonneg (configuration S ((2:ℝ)^j*M) t i.1.2 i.2 alpha beta sigma delta p))

theorem masked_boundary_time_zero (N : ℕ) (a : ℕ → ℂ) (F1 F2 : ℝ → ℂ)
    (S : ℝ → ℝ) (hm : Antitone S) (hlo : ∀ x, 0 ≤ S x) (hhi : ∀ x, S x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), S x = 1) (hright : ∀ x, 1 ≤ x → S x = 0)
    (M T : ℝ) (alpha beta sigma : ℂ) (hM : 0 < M) (hT : 0 < T)
    (hs : sigma ≠ 0) (hab : 0 ≤ (alpha+beta+1).re)
    (K B : ℕ → ℕ) (D : ℕ → Finset ℤ) (hLB : ∀ L, L ≤ B L)
    (keep : ℕ → ((ℕ × ℕ) × ℕ) → ℕ → ℤ → (ℕ × ℕ) → Prop)
    (phi : ℝ → ℂ) (hphi : Continuous phi) :
    Tendsto (fun L => ∫ t in Set.Icc T (2*T), phi t *
      ∑ p ∈ (range (B L) ×ˢ range (B L)) \ (range L ×ˢ range L),
        maskedField N a F1 F2 S M t alpha beta sigma (K L) (D L) (keep L) p)
      atTop (𝓝 0) := by
  apply integrated_boundary_zero T (mass N a F1 F2 alpha beta sigma T) phi hphi
  intro L t ht
  apply boundary_bound L (B L) (hLB L) _ _
    (by unfold mass outerMass cap PRZZWArithmeticCutoff.decayConstant; positivity)
  exact masked_bound N a F1 F2 S hm hlo hhi hleft hright M T t alpha beta sigma
    hM hT ht hs hab (K L) (D L) (keep L)

#print axioms mass_eq
#print axioms field_bound
#print axioms boundary_time_zero
#print axioms masked_bound
#print axioms masked_boundary_time_zero
end XiPrime8845.PRZZArithmeticBoundaryFamily
