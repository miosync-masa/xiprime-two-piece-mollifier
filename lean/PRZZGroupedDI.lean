import PRZZGroupedConvolution

/-! A genuinely boxed convolution with a retained smooth product weight
is exactly a Mellin-coupled DI sum. Factor envelopes remain explicit.
This interface does not replace the original sharp product cutoff by a box. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset ArithmeticFunction
namespace XiPrime8845.PRZZGroupedDI
open PRZZGroupedConvolution PRZZKloostermanInputs PRZZMellinSeparation
set_option maxHeartbeats 2000000

def grouped (C U : ℝ) (E F rho : ℕ) (r nu : ℕ → ℂ)
    (f g : ArithmeticFunction ℂ) (Phi : ℝ → ℂ) (kappa : ℝ) : ℂ :=
  ∑ c ∈ (Icc 1 ⌊C⌋₊).filter (fun c => c.Coprime rho), ∑ a ∈ Icc 1 ⌊U⌋₊,
    ∑ n ∈ Icc 1 (E*F),
      (if n.Coprime c then r c*nu a*
        e ((a:ℝ)*inverseResidue c (rho*n)/c)*Phi (kappa*n) else 0)*
        (PRZZGroupedConvolution.box E f*PRZZGroupedConvolution.box F g) n

theorem grouped_eq (C U : ℝ) (E F rho : ℕ) (hE : 0 < E) (hF : 0 < F)
    (r nu : ℕ → ℂ) (f g : ArithmeticFunction ℂ) (Phi : ℝ → ℂ) (kappa : ℝ) :
    grouped C U E F rho r nu f g Phi kappa =
      PRZZMellinTypeII.coupled C F U E rho r g nu f Phi kappa := by
  unfold grouped
  simp_rw [boxed_weighted E F hE hF]
  rw [PRZZMellinTypeII.coupled,PRZZMellinTypeII.sum_indices]
  simp only [Nat.floor_natCast,sum_filter]
  apply sum_congr rfl
  intro c hc
  split_ifs with hr
  · simp only [Nat.coprime_mul_iff_right]
    simp_rw [sum_comm (s := Icc 1 E) (t := Icc 1 F)]
    rw [sum_comm]
    apply sum_congr rfl
    intro m hm
    by_cases hmc : m.Coprime c
    · rw [if_pos ⟨hr,hmc.symm⟩]
      simp_rw [Nat.coprime_mul_iff_left]
      apply sum_congr rfl
      intro a ha
      apply sum_congr rfl
      intro n hn
      by_cases hnc : n.Coprime c <;>
        simp [PRZZMellinTypeII.coefficient,hnc,Nat.cast_mul,mul_assoc] <;>
          ring_nf <;> split_ifs <;> simp_all
    · simp [Nat.coprime_mul_iff_left,hmc,show ¬c.Coprime m from fun h => hmc h.symm]
  · simp [hr,Nat.coprime_mul_iff_right]

/-- DI after exact convolution reindexing and smooth Mellin separation.
The constant is uniform in the scale of the product cutoff. -/
theorem grouped_bound (hDI : DeshouillersIwaniecLemma1) (ε : ℝ) (hε : 0 < ε)
    (Phi : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support Phi ⊆ Set.Icc a b) (hf : ContDiff ℝ ∞ Phi) :
    ∃ K : ℝ, 0 < K ∧ ∀ C U : ℝ, 1 ≤ C → 1 ≤ U → ∀ E F rho : ℕ,
      0 < E → 0 < F → 1 ≤ rho → ∀ R S P Q : ℝ, 0 ≤ R → 0 ≤ S → 0 < P → 0 < Q →
      ∀ (r nu : ℕ → ℂ) (f g : ArithmeticFunction ℂ),
      (∀ c ∈ Icc 1 ⌊C⌋₊, ‖r c‖ ≤ R) → (∀ n ∈ Icc 1 F, ‖g n‖ ≤ S) →
      (∀ u ∈ Icc 1 ⌊U⌋₊, ‖nu u‖ ≤ P) → (∀ n ∈ Icc 1 E, ‖f n‖ ≤ Q) →
      ∀ M kappa : ℝ, 0 < M → 0 < kappa →
      ‖grouped C U E F rho r nu f g (scaledCutoff Phi M) kappa‖ ≤
        K*(R*S*(P*Q)*diBound ε C F U E rho) := by
  obtain ⟨K,hK,h⟩ := PRZZSmoothMellin.coupled_bound_smooth hDI ε hε Phi a b ha hs hf
  refine ⟨K,hK,?_⟩
  intro C U hC hU E F rho hE hF hrho R S P Q hR hS hP hQ r nu f g hr hg hn hff M kappa hM hk
  rw [grouped_eq C U E F rho hE hF]
  exact h C F U E hC (by exact_mod_cast hF) hU (by exact_mod_cast hE) rho hrho
    R S P Q hR hS hP hQ r g nu f hr (by simpa using hg) hn (by simpa using hff) M kappa hM hk

#print axioms grouped_eq
#print axioms grouped_bound
end XiPrime8845.PRZZGroupedDI
