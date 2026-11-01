import PRZZDyadicArithmetic
import PRZZSharpGrouped

/-! Support boxes supplied by the actual finite dyadic restrictions.
The upper group box is the product of the individual upper endpoints;
its factor 2 per coordinate is retained, not silently replaced by 1. -/
noncomputable section
open scoped BigOperators
open Finset ArithmeticFunction
namespace XiPrime8845.PRZZDyadicSupport
open PRZZDyadicArithmetic
set_option maxHeartbeats 2000000

theorem mul_support (f g : ArithmeticFunction ℂ) (l u L U n : ℕ)
    (hf : ∀ n, f n ≠ 0 → l ≤ n ∧ n ≤ u)
    (hg : ∀ n, g n ≠ 0 → L ≤ n ∧ n ≤ U)
    (hn : (f*g) n ≠ 0) : l*L ≤ n ∧ n ≤ u*U := by
  by_contra h
  apply hn
  rw [mul_apply]
  apply sum_eq_zero
  intro p hp
  by_cases hfp : f p.1 = 0
  · simp [hfp]
  by_cases hgp : g p.2 = 0
  · simp [hgp]
  have he := (Nat.mem_divisorsAntidiagonal.mp hp).1
  exact (h ⟨he ▸ Nat.mul_le_mul (hf _ hfp).1 (hg _ hgp).1,
    he ▸ Nat.mul_le_mul (hf _ hfp).2 (hg _ hgp).2⟩).elim

theorem restrict_support (N k : ℕ) (f : ArithmeticFunction ℂ) (n : ℕ)
    (hn : restrict N k f n ≠ 0) : 2^k ≤ n ∧ n ≤ 2^(k+1) := by
  have hm : n ∈ PRZZDyadic.cell N k := by
    by_contra h
    exact hn (by simp [PRZZDyadicArithmetic.restrict,h])
  have h := (PRZZDyadic.mem_cell N k n).mp hm
  exact ⟨h.2.1,h.2.2.le⟩

def dyadicGroup (N : ℕ) (fs : List (ArithmeticFunction ℂ × ℕ)) : ArithmeticFunction ℂ :=
  (fs.map (fun p => restrict N p.2 p.1)).prod

/-- Nonzero grouped coefficients stay in their product box, including
the empty group (the Dirichlet convolution identity at n=1). -/
theorem group_support (N : ℕ) (fs : List (ArithmeticFunction ℂ × ℕ)) (n : ℕ)
    (hn : dyadicGroup N fs n ≠ 0) :
    2^(fs.map Prod.snd).sum ≤ n ∧ n ≤ 2^((fs.map Prod.snd).sum+fs.length) := by
  induction fs generalizing n with
  | nil =>
    have h : n = 1 := by
      by_contra h
      exact hn (by simp [dyadicGroup,one_apply,h])
    simp [h]
  | cons p fs ih =>
    have hh := mul_support (restrict N p.2 p.1) (dyadicGroup N fs)
      (2^p.2) (2^(p.2+1)) (2^(fs.map Prod.snd).sum)
      (2^((fs.map Prod.snd).sum+fs.length)) n (restrict_support N p.2 p.1) ih hn
    simpa [← pow_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

theorem upper_box_factor (fs : List (ArithmeticFunction ℂ × ℕ)) :
    (2:ℕ)^((fs.map Prod.snd).sum+fs.length) =
      2^fs.length*2^(fs.map Prod.snd).sum := by rw [pow_add,mul_comm]

#print axioms mul_support
/-- Shrink both DI boxes using supplied support, without altering the
sharp product test or either coprimality filter. -/
theorem sharp_shrink (N E F : ℕ) (hE : E ≤ N) (hF : F ≤ N)
    (C U : ℝ) (rho : ℕ) (r beta nu alpha : ℕ → ℂ)
    (ha : ∀ n, E < n → alpha n = 0) (hb : ∀ n, F < n → beta n = 0) :
    PRZZSharpDI.sharpBlock N C N U N rho r beta nu alpha =
      PRZZSharpDI.sharpBlock N C F U E rho r beta nu alpha := by
  unfold PRZZSharpDI.sharpBlock
  simp only [Nat.floor_natCast,sum_filter]
  apply sum_congr rfl
  intro c hc
  trans ∑ d ∈ Icc 1 F, if c.Coprime (rho*d) then
    ∑ u ∈ Icc 1 ⌊U⌋₊, ∑ v ∈ Icc 1 N,
      if v.Coprime c then
        if v*d ≤ N then r c*beta d*(nu u*alpha v)*
          PRZZKloostermanInputs.e ((u:ℝ)*PRZZKloostermanInputs.inverseResidue c (rho*v*d)/c)
        else 0
      else 0
    else 0
  · symm
    apply sum_subset (Icc_subset_Icc le_rfl hF)
    intro d hd hnot
    have hz := hb d (by
      by_contra h
      exact hnot (mem_Icc.mpr ⟨(mem_Icc.mp hd).1,by omega⟩))
    simp [hz]
  · apply sum_congr rfl
    intro d hd
    split_ifs with hcd
    · apply sum_congr rfl
      intro u hu
      symm
      apply sum_subset (Icc_subset_Icc le_rfl hE)
      intro v hv hnot
      have hz := ha v (by
        by_contra h
        exact hnot (mem_Icc.mpr ⟨(mem_Icc.mp hv).1,by omega⟩))
      simp [hz]
    · rfl

/-- The actual dyadic masks supply the small DI boxes. Their sizes are
products of upper endpoints, and ef<=N is still inside sharpBlock. -/
theorem dyadic_grouped_eq (N : ℕ) (left right : List (ArithmeticFunction ℂ × ℕ))
    (hE : 2^((left.map Prod.snd).sum+left.length) ≤ N)
    (hF : 2^((right.map Prod.snd).sum+right.length) ≤ N)
    (C U : ℝ) (rho : ℕ) (r nu : ℕ → ℂ) :
    PRZZSharpGrouped.grouped N C U rho r nu (dyadicGroup N left) (dyadicGroup N right) =
      PRZZSharpDI.sharpBlock N C (2^((right.map Prod.snd).sum+right.length):ℕ)
        U (2^((left.map Prod.snd).sum+left.length):ℕ)
        rho r (dyadicGroup N right) nu (dyadicGroup N left) := by
  rw [PRZZSharpGrouped.grouped_eq]
  apply sharp_shrink N _ _ hE hF
  · intro n hn
    by_contra hz
    exact (not_le_of_gt hn) (group_support N left n hz).2
  · intro n hn
    by_contra hz
    exact (not_le_of_gt hn) (group_support N right n hz).2

#print axioms sharp_shrink
#print axioms dyadic_grouped_eq
#print axioms restrict_support
#print axioms group_support
#print axioms upper_box_factor
end XiPrime8845.PRZZDyadicSupport
