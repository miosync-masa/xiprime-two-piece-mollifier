import PRZZMobiusHeathBrown
import PRZZWeightedHeathBrown
import PRZZCoefficientSeparation
import PRZZAStarRectangles

/-! Heath-Brown substitution in the entire original coefficient, including
the leading Mobius factor. Equality is local below the proved cutoff;
the original d*n restrictions make that locality sufficient in A*.
This does not remove the coupled product cutoff after grouping factors. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.zeta
open ArithmeticFunction Finset
namespace XiPrime8845.PRZZFullHeathBrown
open PRZZ PRZZLambda PRZZHeathBrown PRZZWeightedHeathBrown PRZZGCoefficient
set_option maxHeartbeats 2000000

def muExpansion (y K : ℕ) : ArithmeticFunction ℝ :=
  ∑ j ∈ range K, (-1 : ArithmeticFunction ℝ)^j*(K.choose (j+1):ArithmeticFunction ℝ)*
    truncatedMu y^(j+1)*(ζ : ArithmeticFunction ℝ)^j

def lambdaExpansion (y K J : ℕ) : ArithmeticFunction ℝ :=
  ∑ j ∈ range K, ((-1:ℝ)^j*(K.choose (j+1):ℝ)) • expand J (factors y j)

def fullExpansion (y K : ℕ) : List ℕ → ArithmeticFunction ℝ
  | [] => muExpansion y K
  | j::js => fullExpansion y K js * lambdaExpansion y K j

theorem fullExpansion_product (y K : ℕ) (js : List ℕ) :
    fullExpansion y K js = muExpansion y K*(js.map (lambdaExpansion y K)).prod := by
  induction js with
  | nil => simp [fullExpansion]
  | cons j js ih => simp only [fullExpansion,List.map_cons,List.prod_cons,ih]; ring

theorem convolution_congr_below {R : Type*} [Semiring R]
    (f g f' g' : ArithmeticFunction R) (M n : ℕ)
    (hf : ∀ m < M, f m = f' m) (hg : ∀ m < M, g m = g' m) (hn : n < M) :
    (f*g) n = (f'*g') n := by
  rw [mul_apply,mul_apply]
  apply sum_congr rfl
  intro p hp
  have he := (Nat.mem_divisorsAntidiagonal.mp hp).1
  have h1 : p.1 ≤ n := by
    rw [← he]
    exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hp))
  have h2 : p.2 ≤ n := by
    rw [← he,mul_comm]
    exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hp))
  rw [hf _ (h1.trans_lt hn),hg _ (h2.trans_lt hn)]

theorem coefficient_eq_fullExpansion (y K : ℕ) (js : List ℕ) (n : ℕ)
    (hn : n < (y+1)^K) : coefficient js n = fullExpansion y K js n := by
  induction js generalizing n with
  | nil => exact PRZZMobiusHeathBrown.moebius_binomial y K n hn
  | cons j js ih =>
    apply convolution_congr_below _ _ _ _ ((y+1)^K) n
      (fun m hm => ih m hm) _ hn
    intro m hm
    exact heathBrown_weighted j y K m hm

/-- A cutoff-local change of coefficients leaves every original rectangle
unchanged, including the conjugated second coefficient. -/
theorem rectangle_congr_coeff (N d j l : ℕ) (a b : ℕ → ℂ)
    (F1 F2 FM : ℝ → ℂ) (α β : ℂ) (x t : ℝ) (k : ℤ)
    (hab : ∀ n ≤ N, a n = b n) :
    PRZZAStarRectangles.rectangle N d j l a F1 F2 FM α β x t k =
      PRZZAStarRectangles.rectangle N d j l b F1 F2 FM α β x t k := by
  unfold PRZZAStarRectangles.rectangle
  apply sum_congr rfl
  intro n1 hn1
  apply sum_congr rfl
  intro n2 hn2
  split_ifs with hc
  · simp only [PRZZAStarNu.pairCoeff,hab _ hc.2.1,hab _ hc.2.2]
  · rfl

theorem rectangle_heathBrown (N d j l y K : ℕ) (js : List ℕ)
    (hcut : N < (y+1)^K) (F1 F2 FM : ℝ → ℂ) (α β : ℂ) (x t : ℝ) (k : ℤ) :
    PRZZAStarRectangles.rectangle N d j l (fun n => (coefficient js n:ℂ)) F1 F2 FM α β x t k =
      PRZZAStarRectangles.rectangle N d j l (fun n => (fullExpansion y K js n:ℂ))
        F1 F2 FM α β x t k := by
  apply rectangle_congr_coeff
  intro n hn
  rw [coefficient_eq_fullExpansion y K js n (hn.trans_lt hcut)]

/-- The original cutoff N itself supplies the short-factor length;
there is no unproved cutoff-range hypothesis left in this adapter. -/
theorem rectangle_heathBrown_root (N d j l K : ℕ) (js : List ℕ) (hK : 0 < K)
    (F1 F2 FM : ℝ → ℂ) (α β : ℂ) (x t : ℝ) (k : ℤ) :
    PRZZAStarRectangles.rectangle N d j l (fun n => (coefficient js n:ℂ)) F1 F2 FM α β x t k =
      PRZZAStarRectangles.rectangle N d j l
        (fun n => (fullExpansion ⌊Real.rpow (N:ℝ) (K:ℝ)⁻¹⌋₊ K js n:ℂ))
        F1 F2 FM α β x t k :=
  rectangle_heathBrown N d j l _ K js
    (root_cutoff_range (N:ℝ) (Nat.cast_nonneg _) K hK N le_rfl) F1 F2 FM α β x t k

#print axioms fullExpansion_product
#print axioms convolution_congr_below
#print axioms coefficient_eq_fullExpansion
#print axioms rectangle_congr_coeff
#print axioms rectangle_heathBrown
#print axioms rectangle_heathBrown_root
end XiPrime8845.PRZZFullHeathBrown
