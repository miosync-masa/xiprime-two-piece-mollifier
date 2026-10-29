import FengArithmetic
import ConreyCoefficientBridge

/-! Exact ordered Conrey/Feng components of the original coefficient sums.
These are finite identities; K20, K02 and K22 uniform limits remain to be proved. -/
noncomputable section
open scoped BigOperators
namespace XiPrime8845.FengCoefficientBridge
open PRZZ GcdDecomposition
set_option maxHeartbeats 1000000

def fengProfile (P : Polynomial ℝ) : Profiles := ⟨0,P⟩

theorem coefficient_split (P : Profiles) (θ T : ℝ) (n : ℕ) :
    coefficient P θ T n =
      coefficient (ConreyCoefficientBridge.profile P.conrey) θ T n +
      coefficient (fengProfile P.feng) θ T n := by
  unfold coefficient ConreyCoefficientBridge.profile fengProfile
  split_ifs <;> simp

theorem feng_coefficient (P : Polynomial ℝ) (θ T : ℝ) (n : ℕ) :
    coefficient (fengProfile P) θ T n =
      if 1 ≤ n ∧ (n:ℝ) ≤ length θ T then
        ((fengArithmetic n * P.eval (Real.log (length θ T/n)/Real.log (length θ T)) /
          (Real.log (length θ T))^2 : ℝ):ℂ) else 0 := by
  simp [coefficient,fengProfile]

theorem coefficient_star (P : Profiles) (θ T : ℝ) (n : ℕ) :
    star (coefficient P θ T n) = coefficient P θ T n := by
  unfold coefficient
  split_ifs <;> simp

theorem arithmeticSum_add_left (a c b : ℕ → ℂ) (N : ℕ) (α β : ℂ) :
    arithmeticSum (a+c) b N α β = arithmeticSum a b N α β + arithmeticSum c b N α β := by
  simp only [arithmeticSum,Pi.add_apply,add_mul,add_div,Finset.sum_add_distrib]

theorem arithmeticSum_add_right (a b c : ℕ → ℂ) (N : ℕ) (α β : ℂ) :
    arithmeticSum a (b+c) N α β = arithmeticSum a b N α β + arithmeticSum a c N α β := by
  simp only [arithmeticSum,Pi.add_apply,star_add,mul_add,add_mul,add_div,Finset.sum_add_distrib]

/-- Ordered 00 + 20 + 02 + 22: cross terms have not been identified or doubled. -/
theorem scaledArithmetic_four (P Q : Profiles) (θ T : ℝ) (A B : ℂ) :
    scaledArithmetic P Q θ T A B =
      scaledArithmetic (ConreyCoefficientBridge.profile P.conrey)
        (ConreyCoefficientBridge.profile Q.conrey) θ T A B +
      scaledArithmetic (fengProfile P.feng) (ConreyCoefficientBridge.profile Q.conrey) θ T A B +
      scaledArithmetic (ConreyCoefficientBridge.profile P.conrey) (fengProfile Q.feng) θ T A B +
      scaledArithmetic (fengProfile P.feng) (fengProfile Q.feng) θ T A B := by
  have hp : coefficient P θ T = coefficient (ConreyCoefficientBridge.profile P.conrey) θ T +
      coefficient (fengProfile P.feng) θ T := funext (coefficient_split P θ T)
  have hq : coefficient Q θ T = coefficient (ConreyCoefficientBridge.profile Q.conrey) θ T +
      coefficient (fengProfile Q.feng) θ T := funext (coefficient_split Q θ T)
  unfold scaledArithmetic
  rw [hp,hq,arithmeticSum_add_left,arithmeticSum_add_right,arithmeticSum_add_right]
  ring

/-- The same exact four-way splitting for the literal PRZZ gcd main term. -/
theorem gcdMainTerm_four (P Q : Profiles) (θ T : ℝ) (Phi : ℝ → ℝ) (A B : ℂ) :
    gcdMainTerm P Q θ T Phi A B =
      gcdMainTerm (ConreyCoefficientBridge.profile P.conrey)
        (ConreyCoefficientBridge.profile Q.conrey) θ T Phi A B +
      gcdMainTerm (fengProfile P.feng) (ConreyCoefficientBridge.profile Q.conrey) θ T Phi A B +
      gcdMainTerm (ConreyCoefficientBridge.profile P.conrey) (fengProfile Q.feng) θ T Phi A B +
      gcdMainTerm (fengProfile P.feng) (fengProfile Q.feng) θ T Phi A B := by
  unfold gcdMainTerm
  simp only [coefficient_split P θ T,coefficient_split Q θ T,star_add,
    add_mul,mul_add,add_div,Finset.sum_add_distrib]
  ring

def inner (P : Profiles) (θ T : ℝ) (g : ℕ) (A : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (cutoff θ T/g), coefficient P θ T (g*n)/(n:ℂ)^(1+A/(Real.log T:ℂ))

/-- Valid also for Feng profiles: coefficients at g*n are NOT factorized. -/
theorem scaledArithmetic_diagonal (P Q : Profiles) (θ T : ℝ) (A B : ℂ) :
    scaledArithmetic P Q θ T A B = (Real.log T:ℂ) *
      ∑ g ∈ Finset.Icc 1 (cutoff θ T),
        ElementaryGcd.generalizedTotient (1+A/(Real.log T:ℂ)+B/(Real.log T:ℂ)) g /
          (g:ℂ)^(2+A/(Real.log T:ℂ)+B/(Real.log T:ℂ)) *
        inner P θ T g A * inner Q θ T g B := by
  rw [scaledArithmetic,ElementaryGcd.arithmeticSum_diagonal_quotient]
  simp only [coefficient_star,inner]

#print axioms coefficient_split
#print axioms feng_coefficient
#print axioms coefficient_star
#print axioms arithmeticSum_add_left
#print axioms arithmeticSum_add_right
#print axioms scaledArithmetic_four
#print axioms gcdMainTerm_four
#print axioms scaledArithmetic_diagonal
end XiPrime8845.FengCoefficientBridge
