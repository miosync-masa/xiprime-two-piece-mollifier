import PRZZLargeSpatialKernel
import PRZZResolvedComplement

/-! All original four AFE indices and label filters in the large-M
family. The spatial partition is summed pointwise first; its number of
pieces and both sharp arithmetic cutoffs cost no multiplicity. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset Complex Set
namespace XiPrime8845.PRZZLargeSpatialFamily
open PRZZAFEIndices PRZZL1Finite PRZZLargeSpatialKernel
set_option maxHeartbeats 7000000
attribute [local instance] Classical.propDecidable

def mass (c : ℕ → ℂ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 N, ‖c n/(n:ℂ)^(1/2+t*I)‖

theorem row_fibre (L N s : ℕ) (z : Label) (F : ℝ → ℂ)
    (c e : ℕ → ℂ) (a b : ℂ) (t : ℝ) :
    PRZZWRowLimit.row L N F s z c e a b t =
      ∑ i ∈ fibre L N z, PRZZAFEProgression.piece F ((2:ℝ)^s) i.1.1 *
        term c e a b (PRZZActualDirectSum.mainWeight a b) t i.1.1 i.1.2 i.2.1 i.2.2 := by
  exact (PRZZExplicitDomain.fibre_explicit L N z (fun i =>
    PRZZAFEProgression.piece F ((2:ℝ)^s) i.1.1 *
      term c e a b (PRZZActualDirectSum.mainWeight a b) t i.1.1 i.1.2 i.2.1 i.2.2)).symm

theorem retained_fibre (L N : ℕ) (F : ℝ → ℂ) (R : ℕ → Label → Prop)
    (c e : ℕ → ℂ) (a b : ℂ) (t : ℝ) :
    PRZZWRowLimit.retained L N F R c e a b t =
      ∑ s ∈ range (L+2), ∑ i ∈ indices L N,
        if (label i).2.1 ≠ 0 ∧ R s (label i) then
          PRZZAFEProgression.piece F ((2:ℝ)^s) i.1.1 *
            term c e a b (PRZZActualDirectSum.mainWeight a b) t i.1.1 i.1.2 i.2.1 i.2.2 else 0 := by
  unfold PRZZWRowLimit.retained
  apply sum_congr rfl
  intro s hs
  rw [grouped]
  apply sum_congr rfl
  intro z hz
  rw [row_fibre]
  by_cases h : z.2.1 ≠ 0 ∧ R s z
  · rw [if_pos h]
    apply sum_congr rfl
    intro i hi
    have he := (mem_filter.mp hi).2
    rw [he,if_pos h]
  · rw [if_neg h]
    symm
    apply sum_eq_zero
    intro i hi
    rw [(mem_filter.mp hi).2,if_neg h]

theorem retained_large_bound (S : ℝ → ℝ) (hm : Antitone S)
    (hlo : ∀ x, 0 ≤ S x) (hhi : ∀ x, S x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), S x = 1) (hright : ∀ x, 1 ≤ x → S x = 0)
    (L N : ℕ) (c e : ℕ → ℂ) (a b : ℂ)
    (hab : a+b ≠ 0) (ha : 0 ≤ 1/2+a.re) (hb : 0 ≤ 1/2+b.re)
    (T t X : ℝ) (hT : 0 < T) (ht : t ∈ Icc T (2*T)) (hX : 0 < X) :
    ‖PRZZWRowLimit.retained L N (fun y => (S y:ℂ)) (fun s _ => X ≤ (2:ℝ)^s) c e a b t‖ ≤
      (4*constant (a+b)*(T/Real.pi)^4/X^2)*PRZZWeightTail.squareMass^2*mass c N t*mass e N t := by
  rw [retained_fibre]
  apply (norm_sum_le _ _).trans
  apply (sum_le_sum (fun s hs => norm_sum_le _ _)).trans
  have hprune : (∑ s ∈ range (L+2), ∑ i ∈ indices L N,
      ‖if (label i).2.1 ≠ 0 ∧ X ≤ (2:ℝ)^s then
        PRZZAFEProgression.piece (fun y => (S y:ℂ)) ((2:ℝ)^s) i.1.1 *
          term c e a b (PRZZActualDirectSum.mainWeight a b) t i.1.1 i.1.2 i.2.1 i.2.2 else 0‖) ≤
      ∑ i ∈ indices L N, largeMass S (L+2) X i.1.1 *
        ‖term c e a b (PRZZActualDirectSum.mainWeight a b) t i.1.1 i.1.2 i.2.1 i.2.2‖ := by
    rw [sum_comm]
    apply sum_le_sum
    intro i hi
    unfold largeMass
    rw [sum_mul]
    apply sum_le_sum
    intro s hs
    by_cases hgap : (label i).2.1 ≠ 0 <;> by_cases hlarge : X ≤ (2:ℝ)^s <;>
      simp [hgap,hlarge,norm_mul] <;> positivity
  apply hprune.trans
  let C := 4*constant (a+b)*(T/Real.pi)^4/X^2
  have hC : 0 ≤ C := by dsimp [C,constant]; positivity
  have hpoint : ∀ i ∈ indices L N,
      largeMass S (L+2) X i.1.1 *
        ‖term c e a b (PRZZActualDirectSum.mainWeight a b) t i.1.1 i.1.2 i.2.1 i.2.2‖ ≤
      C*(1/(i.1.1:ℝ)^2)*(1/(i.1.2:ℝ)^2)*
        ‖c i.2.1/(i.2.1:ℂ)^(1/2+t*I)‖*‖e i.2.2/(i.2.2:ℂ)^(1/2+t*I)‖ := by
    intro i hi
    have hp := mem_product.mp hi
    have hk := mem_product.mp hp.1
    have hh := large_direct S hm hlo hhi hleft hright a b hab ha hb T t X (L+2)
      i.1.1 i.1.2 hT ht hX (mem_Icc.mp hk.1).1 (mem_Icc.mp hk.2).1
    have he : PRZZActualDirectSum.mainWeight a b = PRZZWArithmeticCutoff.kernel (a+b) := rfl
    rw [term,norm_mul,norm_mul,norm_star,he]
    dsimp [C]
    nlinarith only [mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hh (norm_nonneg (c i.2.1/(i.2.1:ℂ)^(1/2+t*I))))
        (norm_nonneg (e i.2.2/(i.2.2:ℂ)^(1/2+t*I)))]
  apply (sum_le_sum hpoint).trans
  have he : (∑ i ∈ indices L N, C*(1/(i.1.1:ℝ)^2)*(1/(i.1.2:ℝ)^2)*
      ‖c i.2.1/(i.2.1:ℂ)^(1/2+t*I)‖*‖e i.2.2/(i.2.2:ℂ)^(1/2+t*I)‖) =
      C*(∑ m ∈ Icc 1 L, 1/(m:ℝ)^2)*(∑ k ∈ Icc 1 L, 1/(k:ℝ)^2)*mass c N t*mass e N t := by
    simp only [indices,sum_product,mass]
    simp_rw [mul_assoc,← mul_sum,← sum_mul]
  rw [he]
  have hc : 0 ≤ mass c N t := sum_nonneg (fun n hn => norm_nonneg _)
  have he0 : 0 ≤ mass e N t := sum_nonneg (fun n hn => norm_nonneg _)
  have hs0 : 0 ≤ (∑ m ∈ Icc 1 L, 1/(m:ℝ)^2) := by positivity
  have hs := square_sum L
  change _ ≤ C*PRZZWeightTail.squareMass^2*mass c N t*mass e N t
  nlinarith only [mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (mul_le_mul hs hs hs0 (hs0.trans hs)) hC) hc) he0]

#print axioms row_fibre
#print axioms retained_fibre
#print axioms retained_large_bound
end XiPrime8845.PRZZLargeSpatialFamily
