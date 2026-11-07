import PRZZFiniteFreezeBudget
import PRZZIntegratedDefect

/-! Substitute the actual normalized arithmetic prefactors into the
optimized finite freezing budget. The last theorem combines this computed
budget with the literal zeta-to-W defect integral. It does not identify
the full post-Poisson remainder with that budget, or assert a new AFE
decomposition equality. -/
noncomputable section
open scoped BigOperators
open Set Complex MeasureTheory Filter
namespace XiPrime8845.PRZZFreezeErrorBudget
open PRZZFiniteFreezeBudget PRZZActiveFreezeBudget PRZZPrefactorMass
set_option maxHeartbeats 6000000

def weightedMass (js : List ℕ) (N K : ℕ) (T M Q V eps eH : ℝ)
    (F G : ℝ → ℂ) (alpha beta : ℂ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, ∑ j ∈ Finset.range (Nat.log 2 N+1),
    ∑ l ∈ Finset.range (Nat.log 2 N+1), ∑ k ∈ Finset.range K,
      sourceCost T ((2:ℝ)^k*M) eps j l*
        mass N d j l (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^k*M) Q eps)
          (PRZZSourceCutoffs.poissonCutoff d T ((2:ℝ)^k*M) V eH)
          (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
          (PRZZMellinSeparation.scaledCutoff F Q) (PRZZMellinSeparation.scaledCutoff G V)
          alpha beta

/-- No coefficient-mass estimate is an input: the valued cutoffs,
complex shifts and inverse-residue phase are the literal prefactor. -/
theorem weighted_mass_le (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G) :
    ∃ C : ℝ, 0 < C ∧ ∀ (js : List ℕ) (N K : ℕ) (T M Q V S eps eH : ℝ) (alpha beta : ℂ),
      1 ≤ N → (N:ℝ) ≤ T → 0 < T → 0 < Real.log T → 0 ≤ S →
      |alpha.re| ≤ S/Real.log T → |beta.re| ≤ S/Real.log T →
      weightedMass js N K T M Q V eps eH F G alpha beta ≤
        C*Real.exp (2*S)*(Real.log N)^(2*PRZZGCoefficient.degree js)*
          budget N K T M Q V eps eH
            (PRZZMellinSeparation.scaledCutoff F Q) (PRZZMellinSeparation.scaledCutoff G V) := by
  obtain ⟨C,hC,hh⟩ := active_row_bound F G hF hG hcF hcG
  refine ⟨C,hC,?_⟩
  intro js N K T M Q V S eps eH alpha beta hN hNT hT hL hS ha hb
  unfold weightedMass budget
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l hl
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  exact hh js N d j l _ _ T ((2:ℝ)^k*M) Q V S eps alpha beta
    hN (Finset.mem_Icc.mp hd).1 hNT hT hL hS ha hb

/-- All finite spatial scales, gcd divisors, dyadic coordinates, signed
frequencies and actual arithmetic coefficients fit in the published target.
The only height slack spent is the explicit 7*eps+eH plus logarithms. -/
theorem weighted_absorbed (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hsG : Function.support G ⊆ Icc (1/2:ℝ) 3)
    (js : List ℕ) (S r eps eH delta : ℝ) (hS : 0 ≤ S) (hr : 0 < r)
    (heps : 0 ≤ eps) (hmargin : 7*eps+eH < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N K : ℕ) (T M Q V : ℝ) (alpha beta : ℂ),
      1 ≤ N → 1 ≤ T → 1 ≤ Real.log T → (N:ℝ) ≤ T^(4/7:ℝ) →
      0 < M → 0 < Q → 0 < V →
      |alpha.re| ≤ S/Real.log T → |beta.re| ≤ S/Real.log T →
      (1+(Real.log T)^2/r^2)*T*weightedMass js N K T M Q V eps eH F G alpha beta ≤
        C*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,hmass⟩ := weighted_mass_le F G hF hG hcF hcG
  obtain ⟨D,hD,hbudget⟩ := budget_absorbed (2*PRZZGCoefficient.degree js) eps eH r delta heps hr hmargin
  refine ⟨C*Real.exp (2*S)*D,by positivity,?_⟩
  intro N K T M Q V alpha beta hN hT hL hscale hM hQ hV ha hb
  have ht : 0 < T := by linarith
  have hNT : (N:ℝ) ≤ T := hscale.trans (by
    simpa using Real.rpow_le_rpow_of_exponent_le hT (by norm_num : (4/7:ℝ) ≤ 1))
  have hh := hmass js N K T M Q V S eps eH alpha beta hN hNT ht (by linarith) hS ha hb
  have hg := hbudget N K T M Q V _ _ hN hT hL hscale hM hQ hV
    (PRZZFreezeScales.scaled_support F Q hQ hsF) (PRZZFreezeScales.scaled_support G V hV hsG)
  have h1 := mul_le_mul_of_nonneg_left hh (show 0 ≤ (1+(Real.log T)^2/r^2)*T by positivity)
  have h2 := mul_le_mul_of_nonneg_left hg (show 0 ≤ C*Real.exp (2*S) by positivity)
  apply h1.trans
  convert h2 using 1 <;> ring

theorem scaled_real_bound (A : ℂ) (S L : ℝ) (hL : 0 < L) (hA : ‖A‖ ≤ S) :
    |(A/(L:ℂ)).re| ≤ S/L := by
  rw [Complex.div_ofReal_re,abs_div,abs_of_pos hL]
  exact div_le_div_of_nonneg_right ((Complex.abs_re_le_norm A).trans hA) hL.le

/-- A single computed error budget: the original AFE replacement/residue
defect integral plus the optimized, fully weighted finite freezing charge.
This is deliberately a budget inequality, not an unproved identification
of a Poisson central sum with A*. -/
theorem replacement_and_freezing_budget
    (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hsG : Function.support G ⊆ Icc (1/2:ℝ) 3)
    (js : List ℕ) (S r eps eH delta : ℝ) (hS : 0 ≤ S) (hr : 0 < r)
    (heps : 0 ≤ eps) (hdelta : 0 < delta) (hmargin : 7*eps+eH < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ → ∀ N K : ℕ,
      1 ≤ N → (N:ℝ) ≤ T^(4/7:ℝ) → ∀ M Q V : ℝ,
      0 < M → 0 < Q → 0 < V → ∀ (phi : ℝ → ℂ) (P : ℝ),
      Continuous phi → 0 ≤ P → (∀ t ∈ Icc T (2*T), ‖phi t‖ ≤ P) →
      ‖∫ t in Icc T (2*T), PRZZMollifiedTime.mollifierWeight phi
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) N t *
        PRZZIntegratedDefect.defect (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t‖ +
      P*(1+(Real.log T)^2/r^2)*T*
        weightedMass js N K T M Q V eps eH F G (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) ≤
          C*P*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨Cr,hCr,hrb⟩ := PRZZIntegratedDefect.scaled_target js S r delta hS hr hdelta
  obtain ⟨Cw,hCw,hwb⟩ := weighted_absorbed F G hF hG hcF hcG hsF hsG js S r eps eH delta
    hS hr heps hmargin
  refine ⟨Cr+Cw,by positivity,?_⟩
  filter_upwards [hrb,eventually_ge_atTop (Real.exp 1)] with T hre hTe
  have hT : 1 ≤ T := by have hh := Real.add_one_le_exp (1:ℝ); linarith
  have hL : 1 ≤ Real.log T := by
    have hh := Real.log_le_log (Real.exp_pos 1) hTe
    simpa using hh
  intro A B hA hB hsep N K hN hscale M Q V hM hQ hV phi P hphi hP hp
  have hNT : (N:ℝ) ≤ T := hscale.trans (by
    simpa using Real.rpow_le_rpow_of_exponent_le hT (by norm_num : (4/7:ℝ) ≤ 1))
  have h1 := hre A B hA hB hsep N hN hNT phi P hphi hP hp
  have h2 := hwb N K T M Q V _ _ hN hT hL hscale hM hQ hV
    (scaled_real_bound A S (Real.log T) (by linarith) hA)
    (scaled_real_bound B S (Real.log T) (by linarith) hB)
  have h2' : P*(1+(Real.log T)^2/r^2)*T*
      weightedMass js N K T M Q V eps eH F G (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) ≤
      Cw*P*T^delta*PRZZOptimalPowers.target N T := by
    calc
      _ = P*((1+(Real.log T)^2/r^2)*T*
          weightedMass js N K T M Q V eps eH F G (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) := by ring
      _ ≤ P*(Cw*T^delta*PRZZOptimalPowers.target N T) := mul_le_mul_of_nonneg_left h2 hP
      _ = _ := by ring
  calc
    _ ≤ Cr*P*T^delta*PRZZOptimalPowers.target N T+Cw*P*T^delta*PRZZOptimalPowers.target N T :=
      add_le_add h1 h2'
    _ = _ := by ring

#print axioms weighted_mass_le
#print axioms weighted_absorbed
#print axioms scaled_real_bound
#print axioms replacement_and_freezing_budget
end XiPrime8845.PRZZFreezeErrorBudget
