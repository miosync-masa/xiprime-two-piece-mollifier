import PRZZSourceLattice

/-! Uniform sharp-cutoff removal on a bounded spatial-scale family.
The bound precedes every row and its coefficients. Scales M>X are not
covered by this lemma and still require a summable large-scale envelope. -/
noncomputable section
open scoped BigOperators
open Set
namespace XiPrime8845.PRZZSourceWindowCutoff
set_option maxHeartbeats 2000000

theorem endpoints (N X M : ℝ) (L u v : ℕ)
    (hN : 1 ≤ N) (hM : 0 < M) (hMX : M ≤ X)
    (hu : (u:ℝ) ≤ N) (hv : 0 < v) (hL : 4*N*X ≤ L) :
    3*M ≤ L ∧ (13/4:ℝ)*M*u ≤ (L:ℝ)*v := by
  have hX : 0 < X := hM.trans_le hMX
  have hNX : X ≤ N*X := by nlinarith
  have hprod : M*(u:ℝ) ≤ X*N := mul_le_mul hMX hu (by positivity) hX.le
  have hv1 : (1:ℝ) ≤ v := by exact_mod_cast hv
  constructor
  · nlinarith
  · have hLv : (L:ℝ) ≤ (L:ℝ)*v := by nlinarith
    nlinarith

/-- The entire explicit boundary sum is zero, uniformly over all rows
with M<=X and u<=N. There is no restriction on how many rows are selected. -/
theorem boundary_zero (L B : ℕ) (N X : ℝ)
    (F : ℝ → ℂ) (M t : ℝ) (z : PRZZAStar.Index) (alpha beta sigma : ℂ)
    (hN : 1 ≤ N) (hM : 0 < M) (hMX : M ≤ X)
    (hu : 0 < z.1.1) (huN : (z.1.1:ℝ) ≤ N) (hv : 0 < z.1.2)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hdelta : |(z.2.1:ℝ)| ≤ M*z.1.1/4) (hL : 4*N*X ≤ L) :
    (∑ p ∈ ((Finset.Icc (1:ℤ) B) ×ˢ (Finset.Icc (1:ℤ) B)) \
        ((Finset.Icc (1:ℤ) L) ×ˢ (Finset.Icc (1:ℤ) L)),
      if p.1*z.1.1-p.2*z.1.2= -z.2.1 then
        PRZZSourceLattice.source F M z alpha beta sigma t p.1 else 0) = 0 := by
  obtain ⟨he,hk⟩ := endpoints N X M L z.1.1 z.1.2 hN hM hMX huN hv hL
  apply Finset.sum_eq_zero
  intro p hp
  split_ifs with hg
  · by_contra hf
    rcases PRZZSourceLattice.boundary_scale L B p F M t z alpha beta sigma
      hM hu hv hsF hdelta hp hg hf with hh | hh
    · exact (not_lt_of_ge he) hh
    · exact (not_lt_of_ge hk) hh
  · rfl

#print axioms endpoints
#print axioms boundary_zero
end XiPrime8845.PRZZSourceWindowCutoff
