import PRZZCoupledAFE
import PRZZCoefficientPolarization

/-! Exact coefficient-free kernel of the actual Gamma diagonal main term.
The primitive d,u,v representation is retained rather than assuming its
gcd simplification. Equality with gcdKernel or smallness of the kernel
defect is NOT asserted here. The time window is also retained explicitly. -/
noncomputable section
open Complex MeasureTheory Finset
open scoped BigOperators
namespace XiPrime8845.PRZZDiagonalKernel
open PRZZCoefficientPolarization PRZZDiagonalAssembly PRZZPowerJets
set_option maxHeartbeats 3000000

def atom (p q : ℕ) (c : ℂ) (n m : ℕ) : ℂ :=
  if p=n ∧ q=m then c else 0

theorem atom_pairing (N p q : ℕ) (c : ℂ) (a b : ℕ → ℂ)
    (hp : p ∈ Icc 1 N) (hq : q ∈ Icc 1 N) :
    arithmeticPairing N (atom p q c) a b = a p*star (b q)*c := by
  classical
  simp only [arithmeticPairing,atom,mul_ite,mul_zero]
  rw [Finset.sum_eq_single p]
  · rw [Finset.sum_eq_single q]
    · simp
    · intro m hm hmq
      simp [Ne.symm hmq]
    · intro hq'
      exact (hq' hq).elim
  · intro n hn hnp
    simp [Ne.symm hnp]
  · intro hp'
    exact (hp' hp).elim

theorem sum_kernel {ι : Type*} (s : Finset ι) (N : ℕ)
    (K : ι → ℕ → ℕ → ℂ) (a b : ℕ → ℂ) :
    arithmeticPairing N (fun n m => ∑ i ∈ s, K i n m) a b =
      ∑ i ∈ s, arithmeticPairing N (K i) a b := by
  classical
  unfold arithmeticPairing
  simp only [mul_sum]
  calc
    _ = ∑ n ∈ Icc 1 N, ∑ i ∈ s, ∑ m ∈ Icc 1 N, a n*star (b m)*K i n m := by
      apply sum_congr rfl; intro n hn
      rw [sum_comm]
    _ = _ := by rw [sum_comm]

/-- With n=d*u and m=d*v, u carries beta and v carries alpha.
This orientation must be reconciled with the public gcdKernel convention;
the defect must not be described as a Gamma-only error before doing so. -/
def primitiveKernel (N : ℕ) (alpha beta : ℂ) (n m : ℕ) : ℂ := by
  classical
  exact ∑ d ∈ Icc 1 N, ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N,
    if admissible N d u v then
      atom (d*u) (d*v)
        (power 1 d*power (1+beta) u*power (1+alpha) v*
          riemannZeta (1+(alpha+beta))) n m else 0

theorem main_eq (N : ℕ) (a : ℕ → ℂ) (alpha beta : ℂ) :
    main N a (fun _ => 1) (fun _ => 1) alpha beta =
      arithmeticPairing N (primitiveKernel N alpha beta) a a := by
  classical
  unfold primitiveKernel
  rw [sum_kernel]
  apply Eq.symm
  unfold main
  apply sum_congr rfl; intro d hd
  rw [sum_kernel]
  apply sum_congr rfl; intro u hu
  rw [sum_kernel]
  apply sum_congr rfl; intro v hv
  by_cases h : admissible N d u v
  · simp only [if_pos h]
    rw [atom_pairing N (d*u) (d*v) _ a a
      (mem_Icc.mpr ⟨Nat.mul_pos (mem_Icc.mp hd).1 (mem_Icc.mp hu).1,h.2.1⟩)
      (mem_Icc.mpr ⟨Nat.mul_pos (mem_Icc.mp hd).1 (mem_Icc.mp hv).1,h.2.2⟩)]
    simp only [coefficient,one_mul]
    ring
  · simp [h,arithmeticPairing]

/-- Gamma multiplier and both actual time integrals are retained. -/
def diagonalKernel (N : ℕ) (alpha beta : ℂ) (T : ℝ) (phi : ℝ → ℂ)
    (n m : ℕ) : ℂ :=
  (∫ t in Set.Icc T (2*T), phi t)*primitiveKernel N alpha beta n m +
    (∫ t in Set.Icc T (2*T), phi t*PRZZAFEDual.dualMultiplier alpha beta t)*
      primitiveKernel N (-beta) (-alpha) n m

theorem diagonalMain_eq (N : ℕ) (a : ℕ → ℂ) (alpha beta : ℂ)
    (T : ℝ) (phi : ℝ → ℂ) :
    PRZZCoupledAFE.diagonalMain N a alpha beta T phi =
      arithmeticPairing N (diagonalKernel N alpha beta T phi) a a := by
  rw [PRZZCoupledAFE.diagonalMain,main_eq,main_eq]
  simp only [arithmeticPairing,diagonalKernel,mul_add,mul_sum,← sum_add_distrib]
  apply sum_congr rfl; intro n hn
  apply sum_congr rfl; intro m hm
  ring

/-- Separates the two analytic obligations without discarding either one. -/
theorem error_split (N : ℕ) (a : ℕ → ℂ) (alpha beta : ℂ)
    (T : ℝ) (phi : ℝ → ℂ) (M : ℂ) (K : ℕ → ℕ → ℂ) :
    M-arithmeticPairing N K a a =
      (M-PRZZCoupledAFE.diagonalMain N a alpha beta T phi) +
        arithmeticPairing N (fun n m => diagonalKernel N alpha beta T phi n m-K n m) a a := by
  rw [diagonalMain_eq]
  simp only [arithmeticPairing,mul_sub,Finset.sum_sub_distrib]
  ring

/-- The internal mixed bridge uses the density-oriented kernel. No
printed-orientation mixed asymptotic or general-profile axiom is used. -/
theorem density_error_split (N : ℕ) (a b : ℕ → ℂ) (T : ℝ)
    (Phi : ℝ → ℝ) (A B M : ℂ) :
    let Kdiag := diagonalKernel N (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T
      (fun t => (Phi (t/T):ℂ))
    M-arithmeticPairing N (densityGcdKernel T Phi A B) a b =
      (M-arithmeticPairing N Kdiag a b) +
        arithmeticPairing N (fun n m => Kdiag n m-densityGcdKernel T Phi A B n m) a b := by
  dsimp only
  simp only [arithmeticPairing,mul_sub,Finset.sum_sub_distrib]
  ring

/-- Entrywise kernel error keeps its actual arithmetic coefficient mass. -/
theorem defect_bound (N : ℕ) (a b : ℕ → ℂ) (K L : ℕ → ℕ → ℂ)
    (B : ℕ → ℕ → ℝ)
    (h : ∀ n ∈ Icc 1 N, ∀ m ∈ Icc 1 N, ‖K n m-L n m‖ ≤ B n m) :
    ‖arithmeticPairing N (fun n m => K n m-L n m) a b‖ ≤
      ∑ n ∈ Icc 1 N, ∑ m ∈ Icc 1 N, ‖a n‖*‖b m‖*B n m := by
  unfold arithmeticPairing
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro n hn
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro m hm
  simp only [norm_mul,norm_star]
  exact mul_le_mul_of_nonneg_left (h n hn m hm) (by positivity)

#print axioms atom_pairing
#print axioms sum_kernel
#print axioms main_eq
#print axioms diagonalMain_eq
#print axioms error_split
#print axioms density_error_split
#print axioms defect_bound
end XiPrime8845.PRZZDiagonalKernel
