import PRZZGCoefficient
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Uniform subpower control of the supported-number Euler product.
The decay exponent and the modulus exponent are independent. Constants
are selected before the modulus, cutoff, and finite set of h values. -/
noncomputable section
open scoped BigOperators
open Finset Filter Topology
namespace XiPrime8845.PRZZEulerSubpower
set_option maxHeartbeats 2000000

theorem local_eventually (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, (1-x^(-ε))⁻¹ ≤ x^η := by
  filter_upwards [(tendsto_rpow_neg_atTop hε).eventually
    (gt_mem_nhds (show (0:ℝ) < 1/2 by norm_num)),
    (tendsto_rpow_atTop hη).eventually (eventually_ge_atTop (2:ℝ))] with x hx hy
  have hi : (1-x^(-ε))⁻¹ ≤ 2 := by
    rw [inv_eq_one_div,div_le_iff₀ (by linarith : 0 < 1-x^(-ε))]
    linarith
  exact hi.trans hy

theorem eulerMass_subpower (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 1 ≤ d →
      SupportTail.eulerMass d (1-ε) ≤ C*(d:ℝ)^η := by
  classical
  obtain ⟨b,hb⟩ := eventually_atTop.mp (local_eventually ε η hε hη)
  obtain ⟨N,hN⟩ := exists_nat_gt b
  let f : ℕ → ℝ := fun p => (1-(p:ℝ)^(-ε))⁻¹
  let c : ℕ → ℝ := fun p => max 1 (f p)
  let C := ∏ p ∈ range N, c p
  have hc (p : ℕ) : 1 ≤ c p := le_max_left _ _
  have hC : 0 < C := prod_pos (fun p _ => lt_of_lt_of_le zero_lt_one (hc p))
  refine ⟨C,hC,?_⟩
  intro d hd
  have hf (p : ℕ) (hp : p ∈ d.primeFactors) : 0 ≤ f p := by
    apply inv_nonneg.mpr
    have hh := Real.rpow_lt_one_of_one_lt_of_neg
      (show (1:ℝ) < p by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt)
      (show -ε < 0 by linarith)
    linarith
  have hp (p : ℕ) (hpd : p ∈ d.primeFactors) :
      f p ≤ (if p < N then c p else 1)*(p:ℝ)^η := by
    have hpow : 1 ≤ (p:ℝ)^η := Real.one_le_rpow
      (by exact_mod_cast (Nat.prime_of_mem_primeFactors hpd).one_lt.le) hη.le
    split_ifs with hlt
    · exact (le_max_right _ _).trans
        (le_mul_of_one_le_right (zero_le_one.trans (hc p)) hpow)
    · simpa only [one_mul] using hb p (hN.le.trans (by exact_mod_cast Nat.le_of_not_gt hlt))
  have hsmall : (∏ p ∈ d.primeFactors, if p < N then c p else 1) ≤ C := by
    rw [← prod_filter]
    exact prod_le_prod_of_subset_of_one_le
      (fun p hp => mem_range.mpr (mem_filter.mp hp).2)
      (fun p _ => zero_le_one.trans (hc p)) (fun p _ _ => hc p)
  have hrad : (∏ p ∈ d.primeFactors, (p:ℝ)^η) ≤ (d:ℝ)^η := by
    rw [Real.finsetProd_rpow]
    · apply Real.rpow_le_rpow (by positivity) _ hη.le
      have hdvd : (∏ p ∈ d.primeFactors, p) ∣ d :=
        prod_primes_dvd d (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime)
          (fun p hp => Nat.dvd_of_mem_primeFactors hp)
      simpa only [Nat.cast_prod] using
        (show ((∏ p ∈ d.primeFactors, p : ℕ):ℝ) ≤ d by
          exact_mod_cast Nat.le_of_dvd (by omega : 0 < d) hdvd)
    · intros; positivity
  calc
    SupportTail.eulerMass d (1-ε) = ∏ p ∈ d.primeFactors, f p := by
      simp only [SupportTail.eulerMass,f,show 1-ε-1 = -ε by ring]
    _ ≤ ∏ p ∈ d.primeFactors, (if p < N then c p else 1)*(p:ℝ)^η := prod_le_prod hf hp
    _ = (∏ p ∈ d.primeFactors, if p < N then c p else 1)*
        (∏ p ∈ d.primeFactors, (p:ℝ)^η) := prod_mul_distrib
    _ ≤ C*(d:ℝ)^η := mul_le_mul hsmall hrad (by positivity) hC.le

#print axioms local_eventually
#print axioms eulerMass_subpower

/-- Uniform in the arithmetic coefficient, cutoff and supported finite set;
only the two positive exponents determine the Euler-product constant. -/
theorem sourceG_average_subpower (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (js : List ℕ) (k : ℕ) (sigma : ℝ) (d n : ℕ),
      sigma ≤ 0 → 1 ≤ d → 1 ≤ n → ∀ s : Finset ℕ,
      (∀ h ∈ s, 1 ≤ h ∧ d*h ≤ n ∧ SmoothMobius.supported d h) →
      (∑ h ∈ s, |PRZZGCoefficient.sourceG js k sigma d h|/(h:ℝ)^ε) ≤
        (Real.log n)^(k+PRZZGCoefficient.degree js)*(C*(d:ℝ)^η) := by
  obtain ⟨C,hC,h⟩ := eulerMass_subpower ε η hε hη
  refine ⟨C,hC,?_⟩
  intro js k sigma d n hσ hd hn s hs
  exact (PRZZGCoefficient.sourceG_average js k sigma ε d n hσ hε hd hn s hs).trans
    (mul_le_mul_of_nonneg_left (h d hd)
      (pow_nonneg (Real.log_nonneg (by exact_mod_cast hn)) _))

/-- The seven-term h sum loses only an arbitrarily small modulus power.
This does not assert identification with the original integral A*. -/
theorem sourceG_seven_subpower (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (js : List ℕ) (k : ℕ) (sigma : ℝ) (d n : ℕ),
      sigma ≤ 0 → 1 ≤ d → 1 ≤ n → ∀ (s : Finset ℕ) (X A V : ℝ) (E : ℕ → ℝ),
      0 < X → 0 ≤ A → 0 ≤ V →
      (∀ h ∈ s, 1 ≤ h ∧ d*h ≤ n ∧ SmoothMobius.supported d h) →
      (∀ h ∈ s, (X/(h:ℝ))^(1/4:ℝ) ≤ E h ∧ E h ≤ (X/(h:ℝ))^(1/2:ℝ)) →
      (∑ h ∈ s, |PRZZGCoefficient.sourceG js k sigma d h| *
        PRZZDISeven.seven h (E h) A (X/h) V) ≤
      PRZZDISeven.envelope X A V*
        ((Real.log n)^(k+PRZZGCoefficient.degree js)*(C*(d:ℝ)^η)) := by
  obtain ⟨C,hC,h⟩ := eulerMass_subpower (3/8) η (by norm_num) hη
  refine ⟨C,hC,?_⟩
  intro js k sigma d n hσ hd hn s X A V E hX hA hV hs hE
  apply (PRZZGCoefficient.sourceG_seven_average js k sigma d n hσ hd hn s
    X A V E hX hA hV hs hE).trans
  apply mul_le_mul_of_nonneg_left _ (by unfold PRZZDISeven.envelope; positivity)
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Real.log_nonneg (by exact_mod_cast hn)) _)
  have hh := h d hd
  norm_num at hh
  exact hh

#print axioms sourceG_average_subpower
#print axioms sourceG_seven_subpower
end XiPrime8845.PRZZEulerSubpower
