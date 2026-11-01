import PRZZSupportedSource
import PRZZGroupedSeven

/-! The extra coprimality with d is a multiplicative zero extension on
the two convolution groups. It is never deleted from a DI estimate. -/
noncomputable section
open scoped BigOperators
open Finset ArithmeticFunction
namespace XiPrime8845.PRZZResidualCoprime
open PRZZKloostermanInputs PRZZSharpGrouped PRZZGroupedConvolution
set_option maxHeartbeats 2000000

def restrict (d : ℕ) (f : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if d.Coprime n then f n else 0, by simp⟩

theorem restrict_mul (d : ℕ) (f g : ArithmeticFunction ℂ) :
    restrict d (f*g) = restrict d f*restrict d g := by
  ext n
  change (if d.Coprime n then (f*g) n else 0) = _
  rw [mul_apply,mul_apply]
  by_cases hc : d.Coprime n
  · rw [if_pos hc]
    apply sum_congr rfl
    intro z hz
    have he := (Nat.mem_divisorsAntidiagonal.mp hz).1
    rw [← he,Nat.coprime_mul_iff_right] at hc
    change f z.1*g z.2 = (if d.Coprime z.1 then f z.1 else 0)*
      (if d.Coprime z.2 then g z.2 else 0)
    rw [if_pos hc.1,if_pos hc.2]
  · rw [if_neg hc]
    symm
    apply sum_eq_zero
    intro z hz
    have he := (Nat.mem_divisorsAntidiagonal.mp hz).1
    have hh : ¬ (d.Coprime z.1 ∧ d.Coprime z.2) := by
      simpa only [← he,Nat.coprime_mul_iff_right] using hc
    by_cases h1 : d.Coprime z.1 <;> by_cases h2 : d.Coprime z.2 <;>
      simp_all [restrict]

theorem restrict_norm (d n : ℕ) (f : ArithmeticFunction ℂ) :
    ‖restrict d f n‖ ≤ ‖f n‖ := by
  change ‖if d.Coprime n then f n else 0‖ ≤ _
  split_ifs <;> simp

/-- Applies to the literal residual weight, including dyadic masks and
the inverse-residue phase. The sharp d*h*e*f constraint is retained. -/
theorem weighted_residual (N d h : ℕ) (f g : ArithmeticFunction ℂ) (w : ℕ → ℂ) :
    (∑ n ∈ Icc 1 N, if d.Coprime n ∧ d*(h*n) ≤ N then
      (f*g) n*w n else 0) =
      ∑ e ∈ Icc 1 N, ∑ m ∈ Icc 1 N,
        if e*m ≤ N then
          (if d*(h*(e*m)) ≤ N then w (e*m) else 0)*restrict d f e*restrict d g m
        else 0 := by
  rw [← weighted_convolution N (restrict d f) (restrict d g)
    (fun n => if d*(h*n) ≤ N then w n else 0)]
  rw [← restrict_mul]
  apply sum_congr rfl
  intro n hn
  change (if d.Coprime n ∧ d*(h*n) ≤ N then (f*g) n*w n else 0) =
    (if d*(h*n) ≤ N then w n else 0)*(if d.Coprime n then (f*g) n else 0)
  split_ifs <;> simp_all [mul_comm]

/-- A genuine grouped DI sum with both original coprimality conditions.
The h condition remains on the modulus; d is absorbed only as zero masks. -/
theorem grouped_restricted (N d : ℕ) (V A : ℝ) (h : ℕ) (r nu : ℕ → ℂ)
    (f g : ArithmeticFunction ℂ) :
    (∑ c ∈ (Icc 1 ⌊V⌋₊).filter (fun c => c.Coprime h), ∑ a ∈ Icc 1 ⌊A⌋₊,
      ∑ n ∈ Icc 1 N, if d.Coprime n ∧ n.Coprime c then
        r c*nu a*e ((a:ℝ)*inverseResidue c (h*n)/c)*(f*g) n else 0) =
      PRZZSharpDI.sharpBlock N V N A N h r (restrict d g) nu (restrict d f) := by
  rw [← grouped_eq,grouped]
  simp_rw [← restrict_mul]
  apply sum_congr rfl
  intro c hc
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro n hn
  change (if d.Coprime n ∧ n.Coprime c then
    r c*nu a*e ((a:ℝ)*inverseResidue c (h*n)/c)*(f*g) n else 0) =
    (if n.Coprime c then r c*nu a*e ((a:ℝ)*inverseResidue c (h*n)/c) else 0)*
      (if d.Coprime n then (f*g) n else 0)
  split_ifs <;> simp_all

#print axioms restrict_mul
#print axioms restrict_norm
#print axioms weighted_residual
#print axioms grouped_restricted
end XiPrime8845.PRZZResidualCoprime
