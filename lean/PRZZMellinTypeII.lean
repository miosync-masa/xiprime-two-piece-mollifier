import PRZZTypeII
import PRZZMellinSeparation

/-! Literal finite Type II sum with a coupled cutoff F(kappa*e*f).
Mellin inversion, finite interchange, and DI are composed, retaining the
Mellin L1 cost. The analytic DI proposition and fixed-cutoff convergence
are explicit inputs, not new axioms or a claimed A* estimate. -/
noncomputable section
open scoped BigOperators
open Finset MeasureTheory Complex
namespace XiPrime8845.PRZZMellinTypeII
open PRZZTypeII PRZZMellinSeparation PRZZKloostermanInputs
set_option maxHeartbeats 1500000

abbrev Index := (ℕ × ℕ) × (ℕ × ℕ)

def indices (C D U V : ℝ) (rho : ℕ) : Finset Index :=
  ((Icc 1 ⌊C⌋₊ ×ˢ Icc 1 ⌊D⌋₊) ×ˢ (Icc 1 ⌊U⌋₊ ×ˢ Icc 1 ⌊V⌋₊)).filter
    (fun q => q.1.1.Coprime (rho*q.1.2) ∧ q.2.2.Coprime q.1.1)

theorem sum_indices (C D U V : ℝ) (rho : ℕ) (f : Index → ℂ) :
    (∑ q ∈ indices C D U V rho, f q) =
      ∑ c ∈ Icc 1 ⌊C⌋₊, ∑ d ∈ (Icc 1 ⌊D⌋₊).filter (fun d => c.Coprime (rho*d)),
        ∑ u ∈ Icc 1 ⌊U⌋₊, ∑ v ∈ (Icc 1 ⌊V⌋₊).filter (fun v => v.Coprime c), f ((c,d),(u,v)) := by
  simp only [indices,sum_filter,sum_product]
  apply sum_congr rfl
  intro c hc
  apply sum_congr rfl
  intro d hd
  simp only [ite_and]
  by_cases h : c.Coprime (rho*d)
  · rw [if_pos h]
    apply sum_congr rfl
    intro u hu
    apply sum_congr rfl
    intro v hv
    exact if_pos h
  · rw [if_neg h]
    apply sum_eq_zero
    intro u hu
    apply sum_eq_zero
    intro v hv
    exact if_neg h

def coefficient (rho : ℕ) (r beta nu alpha : ℕ → ℂ) (q : Index) : ℂ :=
  r q.1.1*beta q.1.2*(nu q.2.1*alpha q.2.2)*
    e ((q.2.1:ℝ)*inverseResidue q.1.1 (rho*q.2.2*q.1.2)/q.1.1)

def coupled (C D U V : ℝ) (rho : ℕ) (r beta nu alpha : ℕ → ℂ)
    (F : ℝ → ℂ) (kappa : ℝ) : ℂ :=
  ∑ q ∈ indices C D U V rho, coefficient rho r beta nu alpha q*F (kappa*q.2.2*q.1.2)

def twisted (C D U V : ℝ) (rho : ℕ) (r beta nu alpha : ℕ → ℂ) (t : ℝ) : ℂ :=
  block C D U V rho r (fun n => beta n*twist n t) nu (fun n => alpha n*twist n t)

theorem separated_sum (C D U V : ℝ) (rho : ℕ) (r beta nu alpha : ℕ → ℂ) (t : ℝ) :
    (∑ q ∈ indices C D U V rho,
      coefficient rho r beta nu alpha q*twist q.2.2 t*twist q.1.2 t) =
      twisted C D U V rho r beta nu alpha t := by
  rw [sum_indices]
  unfold twisted block
  apply sum_congr rfl
  intro c hc
  apply sum_congr rfl
  intro d hd
  rw [mul_sum]
  apply sum_congr rfl
  intro u hu
  rw [mul_sum]
  apply sum_congr rfl
  intro v hv
  dsimp [coefficient]
  ring

theorem twisted_continuous (C D U V : ℝ) (rho : ℕ) (r beta nu alpha : ℕ → ℂ) :
    Continuous (twisted C D U V rho r beta nu alpha) := by
  unfold twisted block
  apply continuous_finsetSum
  intro c hc
  apply continuous_finsetSum
  intro d hd
  have hdp : (0:ℝ) < d := by exact_mod_cast (mem_Icc.mp (mem_filter.mp hd).1).1
  have ht := twist_continuous d hdp
  apply Continuous.mul (by fun_prop)
  apply continuous_finsetSum
  intro u hu
  apply continuous_finsetSum
  intro v hv
  have hvp : (0:ℝ) < v := by exact_mod_cast (mem_Icc.mp (mem_filter.mp hv).1).1
  have ht' := twist_continuous v hvp
  fun_prop

theorem coupled_eq_integral (C D U V : ℝ) (rho : ℕ) (r beta nu alpha : ℕ → ℂ)
    (F : ℝ → ℂ) (kappa : ℝ) (hk : 0 < kappa) (hc : Continuous F)
    (hf : MellinConvergent F 0) (hF : VerticalIntegrable (mellin F) 0) :
    coupled C D U V rho r beta nu alpha F kappa =
      (1/(2*Real.pi):ℂ)*(∫ t : ℝ, mellin F (t*I)*twist kappa t*
        twisted C D U V rho r beta nu alpha t) := by
  have hx : ∀ q ∈ indices C D U V rho, (0:ℝ) < q.2.2 := by
    intro q hq
    have h := (mem_product.mp (mem_product.mp (mem_filter.mp hq).1).2).2
    exact_mod_cast (mem_Icc.mp h).1
  have hy : ∀ q ∈ indices C D U V rho, (0:ℝ) < q.1.2 := by
    intro q hq
    have h := (mem_product.mp (mem_product.mp (mem_filter.mp hq).1).1).2
    exact_mod_cast (mem_Icc.mp h).1
  simpa only [coupled,separated_sum] using
    sum_separate (indices C D U V rho) (coefficient rho r beta nu alpha)
      (fun q => (q.2.2:ℝ)) (fun q => (q.1.2:ℝ)) kappa hk hx hy F hf hF (fun _ _ => hc.continuousAt)

/-- DI is uniform in the Mellin ordinate because the twists have norm one. -/
theorem coupled_bound (hDI : DeshouillersIwaniecLemma1) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ C D U V : ℝ, 1 ≤ C → 1 ≤ D → 1 ≤ U → 1 ≤ V →
      ∀ rho : ℕ, 1 ≤ rho → ∀ R S P Q : ℝ, 0 ≤ R → 0 ≤ S → 0 < P → 0 < Q →
      ∀ r beta nu alpha : ℕ → ℂ,
      (∀ c ∈ Icc 1 ⌊C⌋₊, ‖r c‖ ≤ R) → (∀ d ∈ Icc 1 ⌊D⌋₊, ‖beta d‖ ≤ S) →
      (∀ u ∈ Icc 1 ⌊U⌋₊, ‖nu u‖ ≤ P) → (∀ v ∈ Icc 1 ⌊V⌋₊, ‖alpha v‖ ≤ Q) →
      ∀ F : ℝ → ℂ, Continuous F → MellinConvergent F 0 → VerticalIntegrable (mellin F) 0 →
      ∀ kappa : ℝ, 0 < kappa →
      ‖coupled C D U V rho r beta nu alpha F kappa‖ ≤
        (1/(2*Real.pi))*(R*S*(P*Q)*K*diBound ε C D U V rho)*
          (∫ t : ℝ, ‖mellin F (t*I)‖) := by
  obtain ⟨K,hK,h⟩ := block_bound hDI ε hε
  refine ⟨K,hK,?_⟩
  intro C D U V hC hD hU hV rho hrho R S P Q hR hS hP hQ r beta nu alpha hr hb hn ha F hc hf hF kappa hk
  rw [coupled_eq_integral C D U V rho r beta nu alpha F kappa hk hc hf hF]
  apply integral_budget F hF kappa _ hk _ (twisted_continuous C D U V rho r beta nu alpha).aestronglyMeasurable
  intro t
  apply h C D U V hC hD hU hV rho hrho R S P Q hR hS hP hQ _ _ _ _ hr _ hn
  · intro d hd
    rw [norm_mul,twist_norm _ _ (by exact_mod_cast (mem_Icc.mp hd).1),mul_one]
    exact ha d hd
  · intro v hv
    rw [norm_mul,twist_norm _ _ (by exact_mod_cast (mem_Icc.mp hv).1),mul_one]
    exact hb v hv

#print axioms sum_indices
#print axioms separated_sum
#print axioms twisted_continuous
#print axioms coupled_eq_integral
#print axioms coupled_bound
end XiPrime8845.PRZZMellinTypeII
