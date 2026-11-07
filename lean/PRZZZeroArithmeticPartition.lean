import PRZZZeroNativeCompletion
import PRZZArithmeticCutoffPartition

/-! Remove the valued arithmetic partition from the completed native
zero collector. The spatial mask and unrestricted signed-gap series
remain unchanged. This identity applies to the genuine dual profile too. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZZeroArithmeticPartition
open PRZZDiagonalAssembly PRZZZeroCompleteCell PRZZMellinSeparation
open PRZZCentralMainAssembly PRZZZeroNativeCompletion
set_option maxHeartbeats 8000000
attribute [local instance] Classical.propDecidable

theorem coefficient_values (a : ℕ → ℂ) (G H : ℝ → ℂ)
    (alpha beta : ℂ) (d u v : ℕ) :
    coefficient a G H alpha beta d u v =
      (G ((d:ℝ)*u)*H ((d:ℝ)*v))*
        coefficient a (fun _ => 1) (fun _ => 1) alpha beta d u v := by
  unfold coefficient
  ring

theorem complete_cover {ι : Type*} (qs : Finset ι) (G H : ι → ℝ → ℂ)
    (N d : ℕ) (T M : ℝ) (a : ℕ → ℂ) (F Phi : ℝ → ℂ) (alpha beta : ℂ)
    (hd : 0 < d)
    (hcover : ∀ n ∈ Icc 1 N, ∀ m ∈ Icc 1 N, (∑ i ∈ qs, G i n*H i m) = 1) :
    (∑ i ∈ qs, complete N d T M a F (G i) (H i) Phi alpha beta) =
      complete N d T M a F (fun _ => 1) (fun _ => 1) Phi alpha beta := by
  unfold complete
  rw [sum_comm]
  apply sum_congr rfl
  intro u hu
  rw [sum_comm]
  apply sum_congr rfl
  intro v hv
  by_cases had : admissible N d u v
  · simp only [if_pos had]
    have he (i : ι) := coefficient_values a (G i) (H i) alpha beta d u v
    simp_rw [he]
    rw [← sum_mul,← sum_mul]
    have hdu : d*u ∈ Icc 1 N := mem_Icc.mpr
      ⟨Nat.mul_pos hd (mem_Icc.mp hu).1,had.2.1⟩
    have hdv : d*v ∈ Icc 1 N := mem_Icc.mpr
      ⟨Nat.mul_pos hd (mem_Icc.mp hv).1,had.2.2⟩
    have hh := hcover (d*u) hdu (d*v) hdv
    push_cast at hh
    rw [hh]
    simp
  · simp [had]

/-- No arithmetic-grid multiplicity remains. In particular no K-dependent
constant is introduced by the exact partition removal. -/
theorem completePart_cover (P Phi : ℝ → ℂ) (K L N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hr : ∀ x, 1 ≤ x → P x = 0)
    (hK : (N:ℝ) ≤ (2:ℝ)^K/2) :
    completePart P Phi K L N a T eps alpha beta =
      ∑ s ∈ (range (L+2)).filter (fun s => (2:ℝ)^s < T^(4:ℝ)),
        ∑ d ∈ Icc 1 N, complete N d T ((2:ℝ)^s) a (PRZZWRowLimit.profile P)
          (fun _ => 1) (fun _ => 1) Phi alpha beta := by
  unfold completePart collect
  rw [sum_comm]
  apply sum_congr rfl
  intro s hs
  rw [sum_comm]
  apply sum_congr rfl
  intro d hd
  apply complete_cover
  · exact (mem_Icc.mp hd).1
  · intro n hn m hm
    exact PRZZArithmeticCutoffPartition.product_unity P K N n m hl hr hn hm hK

theorem model_cover (P Phi : ℝ → ℂ) (L N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hr : ∀ x, 1 ≤ x → P x = 0) :
    completePart P Phi (Nat.log 2 N+2) L N a T eps alpha beta =
      ∑ s ∈ (range (L+2)).filter (fun s => (2:ℝ)^s < T^(4:ℝ)),
        ∑ d ∈ Icc 1 N, complete N d T ((2:ℝ)^s) a (PRZZWRowLimit.profile P)
          (fun _ => 1) (fun _ => 1) Phi alpha beta :=
  completePart_cover P Phi _ L N a T eps alpha beta hl hr
    (PRZZArithmeticCutoffPartition.dyadic_scale_count N)

/-- The dual branch contains the actual Gamma multiplier, not a frozen
or modulus-only surrogate. No regularity premise is needed for this
finite algebraic reconstruction. -/
theorem branch_cover (P Phi : ℝ → ℂ) (L N : ℕ) (a : ℕ → ℂ)
    (T eps : ℝ) (alpha beta : ℂ)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hr : ∀ x, 1 ≤ x → P x = 0) :
    branchPair (fun Phi alpha beta => completePart P Phi (Nat.log 2 N+2) L N a T eps alpha beta)
      Phi T alpha beta =
    branchPair (fun Phi alpha beta =>
      ∑ s ∈ (range (L+2)).filter (fun s => (2:ℝ)^s < T^(4:ℝ)),
        ∑ d ∈ Icc 1 N, complete N d T ((2:ℝ)^s) a (PRZZWRowLimit.profile P)
          (fun _ => 1) (fun _ => 1) Phi alpha beta) Phi T alpha beta := by
  unfold branchPair
  dsimp only
  rw [model_cover P Phi L N a T eps alpha beta hl hr,
    model_cover P _ L N a T eps (-beta) (-alpha) hl hr]

#print axioms coefficient_values
#print axioms complete_cover
#print axioms completePart_cover
#print axioms model_cover
#print axioms branch_cover
end XiPrime8845.PRZZZeroArithmeticPartition
