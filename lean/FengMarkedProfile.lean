import FengSharedInterior

/-! Exact arithmetic/profile separation for the retained shared main term.
No asymptotic for the marked totient measure is assumed or asserted. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Finset
namespace XiPrime8845.FengMarkedProfile
open FengSharedTail FengSharedInterior CoprimeEulerCompletion SupportTail
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

def primeMoment (g : ℕ) : ℂ :=
  ∑ p ∈ g.primeFactors, (Real.log p:ℂ)^2 * (μ (g/p^(g.factorization p)):ℂ)

theorem mark_eq_moment (g : ℕ) (L : ℝ) : mark g L = primeMoment g/(L:ℂ)^2 := by
  simp only [mark,primeMoment,sum_div]
  apply sum_congr rfl; intros; ring

/-- Repeated prime powers are retained: this moment does not vanish merely
because mu(p^k)=0 for k>=2. -/
theorem primeMoment_prime_pow (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    primeMoment (p^k) = (Real.log p:ℂ)^2 := by
  rw [primeMoment,Nat.primeFactors_prime_pow hk.ne' hp,sum_singleton,
    Nat.ordCompl_self_pow hp]
  simp

theorem main_profile (L : ℝ) (g : ℕ) (u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) :
    main L g u θ P A = mark g L * (eulerMass g 0:ℂ) * BetaKernel.D 1 A θ u P := by
  simp only [main,zeroEulerMain,ShiftedMobius.mainTerm,BetaKernel.D,↓reduceIte]
  ring

/-- There is no mu(g)^2 prefactor here: the shared block already contains
mu of the p-free part. Non-squarefree g remain in this exact weight. -/
theorem zero_main_weight (L : ℝ) (g : ℕ) (hg : g ≠ 0) (u θ : ℝ)
    (P G : Polynomial ℂ) (A B : ℂ) :
    (g.totient:ℂ)/(g:ℂ)^2 * main L g u θ P A * main L g u θ G B =
      (mark g L)^2/(g.totient:ℂ) * (BetaKernel.D 1 A θ u P * BetaKernel.D 1 B θ u G) := by
  have hg0 : (g:ℂ) ≠ 0 := by exact_mod_cast hg
  have ht0 : (g.totient:ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_eq_zero.not.mpr hg)
  rw [main_profile,main_profile,TotientWeight.eulerMass_zero g hg]
  push_cast
  field_simp

def markedProfileSum (L U : ℝ) (H : ℝ → ℂ) : ℂ :=
  (∑ g ∈ Ioc 0 (CoprimeEndpoint.cutoff L U),
    (primeMoment g)^2/((L:ℂ)^4*(g.totient:ℂ)) * H (LogProfileSum.coordinate L U g))/(L:ℂ)

theorem main_sum_profile (L U θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) :
    (∑ g ∈ Ioc 0 (CoprimeEndpoint.cutoff L U), (g.totient:ℂ)/(g:ℂ)^2 *
      main L g (LogProfileSum.coordinate L U g) θ P A *
      main L g (LogProfileSum.coordinate L U g) θ G B)/(L:ℂ) =
    markedProfileSum L U (fun u => BetaKernel.D 1 A θ u P * BetaKernel.D 1 B θ u G) := by
  unfold markedProfileSum
  congr 1
  apply sum_congr rfl
  intro g hg
  rw [zero_main_weight L g (by have := (mem_Ioc.mp hg).1; omega),mark_eq_moment]
  ring

/-- The same-prime diagonal survives alongside the ordered distinct-prime
sum. Neither is suppressed when identifying the limiting profile measure. -/
theorem primeMoment_square (g : ℕ) :
    (primeMoment g)^2 =
      (∑ p ∈ g.primeFactors, (Real.log p:ℂ)^4*(μ (g/p^(g.factorization p)):ℂ)^2) +
      ∑ p ∈ g.primeFactors, ∑ q ∈ g.primeFactors.erase p,
        (Real.log p:ℂ)^2*(Real.log q:ℂ)^2 *
          (μ (g/p^(g.factorization p)):ℂ)*(μ (g/q^(g.factorization q)):ℂ) := by
  rw [primeMoment,pow_two,mul_sum]
  trans ∑ p ∈ g.primeFactors,
    ((Real.log p:ℂ)^4*(μ (g/p^(g.factorization p)):ℂ)^2 +
      ∑ q ∈ g.primeFactors.erase p, (Real.log p:ℂ)^2*(Real.log q:ℂ)^2 *
        (μ (g/p^(g.factorization p)):ℂ)*(μ (g/q^(g.factorization q)):ℂ))
  · apply sum_congr rfl
    intro p hp
    rw [← Finset.add_sum_erase _ _ hp,add_mul,sum_mul]
    congr 1
    · ring
    · apply sum_congr rfl; intros; ring
  · exact sum_add_distrib

#print axioms mark_eq_moment
#print axioms primeMoment_prime_pow
#print axioms main_profile
#print axioms zero_main_weight
#print axioms main_sum_profile
#print axioms primeMoment_square
end XiPrime8845.FengMarkedProfile
