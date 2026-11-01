/-
The divisor-pair bijection proof below is adapted from Mathlib's
ArithmeticFunction.IsMultiplicative.mul in ArithmeticFunction/Defs.lean.
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license; see Mathlib's LICENSE.
-/
import PRZZCoprimeAllocation

/-! Exact coprime reindexing of the original finite convolution.
The bijection retains all divisor pairs, including units. No analytic
estimate, cutoff change, or assertion about A* is used. -/
noncomputable section
open scoped BigOperators
open ArithmeticFunction Finset Nat
namespace XiPrime8845.PRZZConvolutionSplit
open PRZZCoprimeAllocation PRZZLambda PRZZGCoefficient
set_option maxHeartbeats 2000000

/-- The same divisor-pair bijection underlying multiplicativity, applied
to an arbitrary summand rather than to multiplicative functions. -/
theorem sum_coprime {R : Type*} [AddCommMonoid R] (m n : ℕ)
    (cop : m.Coprime n) (F : ℕ → ℕ → R) :
    (∑ z ∈ (m*n).divisorsAntidiagonal, F z.1 z.2) =
      ∑ a ∈ m.divisorsAntidiagonal, ∑ b ∈ n.divisorsAntidiagonal,
        F (a.1*b.1) (a.2*b.2) := by
  rw [← sum_product']
  symm
  apply sum_nbij fun ((i,j),k,l) => (i*k,j*l)
  · rintro ⟨⟨a1,a2⟩,⟨b1,b2⟩⟩ h
    simp only [mem_divisorsAntidiagonal,Ne,mem_product] at h
    rcases h with ⟨⟨rfl,ha⟩,⟨rfl,hb⟩⟩
    simp only [mem_divisorsAntidiagonal,mul_eq_zero,Ne]
    constructor
    · ring
    rw [mul_eq_zero] at *
    exact not_or_intro ha hb
  · simp only [Set.InjOn,mem_coe,mem_divisorsAntidiagonal,mem_product,Prod.mk_inj]
    rintro ⟨⟨a1,a2⟩,⟨b1,b2⟩⟩ ⟨⟨rfl,ha⟩,⟨rfl,hb⟩⟩ ⟨⟨c1,c2⟩,⟨d1,d2⟩⟩ hcd h
    ext
    · trans Nat.gcd (a1*a2) (a1*b1)
      · rw [Nat.gcd_mul_left,cop.coprime_mul_left.coprime_mul_right_right.gcd_eq_one,mul_one]
      · rw [← hcd.1.1,← hcd.2.1] at cop
        rw [← hcd.1.1,h.1,Nat.gcd_mul_left,cop.coprime_mul_left.coprime_mul_right_right.gcd_eq_one,mul_one]
    · trans Nat.gcd (a1*a2) (a2*b2)
      · rw [mul_comm,Nat.gcd_mul_left,cop.coprime_mul_right.coprime_mul_left_right.gcd_eq_one,mul_one]
      · rw [← hcd.1.1,← hcd.2.1] at cop
        rw [← hcd.1.1,h.2,mul_comm,Nat.gcd_mul_left,cop.coprime_mul_right.coprime_mul_left_right.gcd_eq_one,mul_one]
    · trans Nat.gcd (b1*b2) (a1*b1)
      · rw [mul_comm,Nat.gcd_mul_right,cop.coprime_mul_right.coprime_mul_left_right.symm.gcd_eq_one,one_mul]
      · rw [← hcd.1.1,← hcd.2.1] at cop
        rw [← hcd.2.1,h.1,mul_comm c1 d1,Nat.gcd_mul_left,cop.coprime_mul_right.coprime_mul_left_right.symm.gcd_eq_one,mul_one]
    · trans Nat.gcd (b1*b2) (a2*b2)
      · rw [Nat.gcd_mul_right,cop.coprime_mul_left.coprime_mul_right_right.symm.gcd_eq_one,one_mul]
      · rw [← hcd.1.1,← hcd.2.1] at cop
        rw [← hcd.2.1,h.2,Nat.gcd_mul_right,cop.coprime_mul_left.coprime_mul_right_right.symm.gcd_eq_one,one_mul]
  · simp only [Set.SurjOn,Set.subset_def,mem_coe,mem_divisorsAntidiagonal,mem_product,Set.mem_image]
    rintro ⟨b1,b2⟩ h
    use ((b1.gcd m,b2.gcd m),(b1.gcd n,b2.gcd n))
    rw [← cop.gcd_mul _,← cop.gcd_mul _,← h.1,gcd_mul_gcd_of_coprime_of_mul_eq_mul cop h.1,
      gcd_mul_gcd_of_coprime_of_mul_eq_mul cop.symm _]
    · rw [Ne,_root_.mul_eq_zero,not_or] at h
      simp [h.2.1,h.2.2]
    rw [mul_comm n m,h.1]
  · intros; rfl

theorem convolution_coprime (f g : ArithmeticFunction ℝ) (m n : ℕ) (hc : m.Coprime n) :
    (f*g) (m*n) = ∑ a ∈ m.divisorsAntidiagonal, ∑ b ∈ n.divisorsAntidiagonal,
      f (a.1*b.1)*g (a.2*b.2) := by
  rw [mul_apply]
  exact sum_coprime m n hc (fun x y => f x*g y)

/-- One exact induction step for the original coefficient: the new
weighted prime-power factor is allocated to one side, with unit factors
explicit. The other coefficient remains its literal convolution value. -/
theorem coefficient_cons_coprime (j : ℕ) (js : List ℕ) (m n : ℕ) (hc : m.Coprime n) :
    coefficient (j::js) (m*n) =
      ∑ a ∈ m.divisorsAntidiagonal, ∑ b ∈ n.divisorsAntidiagonal,
        coefficient js (a.1*b.1)*
          (weightedLambda j a.2*(1 : ArithmeticFunction ℝ) b.2+
            (1 : ArithmeticFunction ℝ) a.2*weightedLambda j b.2) := by
  rw [coefficient,convolution_coprime _ _ m n hc]
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro b hb
  have ha' := (mem_divisorsAntidiagonal.mp ha).1
  have hb' := (mem_divisorsAntidiagonal.mp hb).1
  have hc' : a.2.Coprime b.2 := by
    rw [← ha',← hb'] at hc
    exact hc.coprime_mul_left.coprime_mul_left_right
  rw [weightedLambda_mul_coprime j a.2 b.2 hc']

#print axioms sum_coprime
#print axioms convolution_coprime
#print axioms coefficient_cons_coprime

private theorem sum_unit (F : ℕ → ℝ) (hF : F 0 = 0) (n : ℕ) :
    (∑ b ∈ n.divisorsAntidiagonal, F b.1*(1 : ArithmeticFunction ℝ) b.2) = F n := by
  let f : ArithmeticFunction ℝ := ⟨F,hF⟩
  change (f*1) n = f n
  rw [mul_one]

/-- Unit-factor collapse gives the exact two-way recurrence on coprime
arguments. This is an identity for the original coefficient, not a bound. -/
theorem coefficient_cons_split (j : ℕ) (js : List ℕ) (m n : ℕ) (hc : m.Coprime n) :
    coefficient (j::js) (m*n) =
      (∑ a ∈ m.divisorsAntidiagonal, coefficient js (a.1*n)*weightedLambda j a.2)+
      (∑ b ∈ n.divisorsAntidiagonal, coefficient js (m*b.1)*weightedLambda j b.2) := by
  rw [coefficient_cons_coprime j js m n hc]
  simp_rw [mul_add]
  rw [sum_congr rfl (fun a _ => sum_add_distrib),sum_add_distrib]
  congr 1
  · apply sum_congr rfl
    intro a ha
    calc
      _ = (∑ b ∈ n.divisorsAntidiagonal,
          coefficient js (a.1*b.1)*(1 : ArithmeticFunction ℝ) b.2)*weightedLambda j a.2 := by
        rw [sum_mul]; apply sum_congr rfl; intros; ring
      _ = _ := by rw [sum_unit (fun t => coefficient js (a.1*t)) (by simp) n]
  · rw [sum_comm]
    apply sum_congr rfl
    intro b hb
    calc
      _ = (∑ a ∈ m.divisorsAntidiagonal,
          coefficient js (a.1*b.1)*(1 : ArithmeticFunction ℝ) a.2)*weightedLambda j b.2 := by
        rw [sum_mul]; apply sum_congr rfl; intros; ring
      _ = _ := by rw [sum_unit (fun t => coefficient js (t*b.1)) (by simp) m]

#print axioms coefficient_cons_split
end XiPrime8845.PRZZConvolutionSplit
