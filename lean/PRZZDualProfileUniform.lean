import PRZZDualJetTransfer
import PRZZCentralGridWeilDI

/-! Height-uniform jets of the GENUINE dual time profile. Composition
with T*x cancels the T^-n Gamma jet cost before the cutoff is multiplied.
Constants precede T, shifts and x. -/
noncomputable section
open scoped BigOperators ContDiff Topology
open Complex Finset Set Filter MeasureTheory
namespace XiPrime8845.PRZZDualProfileUniform
set_option maxHeartbeats 8000000

theorem rescaled_jet (a b : ℂ) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4)
    (n : ℕ) (T x : ℝ) :
    iteratedDeriv n (fun y => PRZZAFEDual.dualMultiplier a b (T*y)) x =
      (T^n:ℝ) • iteratedDeriv n (PRZZAFEDual.dualMultiplier a b) (T*x) := by
  exact congrFun (iteratedDeriv_comp_const_smul
    ((PRZZDualSmooth.multiplier_contDiff a b ha hb).of_le
      (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))) T) x

theorem rescaled_uniform (S : ℝ) (hS : 0 ≤ S) :
    ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ, ‖A‖ ≤ S → ‖B‖ ≤ S → ∀ n : ℕ,
      ∀ x ∈ Icc (1:ℝ) 2,
      ‖iteratedDeriv n (fun y => PRZZAFEDual.dualMultiplier
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) (T*y)) x‖ ≤
        Real.exp (2*S+7)*PRZZDualJetTransfer.constant n := by
  filter_upwards [PRZZDualJetTransfer.scaled_cap S hS,
    PRZZScaledReplacement.shifts_eventually S (1/4) (by norm_num),
    eventually_ge_atTop (4:ℝ)] with T hcap hsmall hT
  intro A B hA hB n x hx
  rw [rescaled_jet _ _ (hsmall.2 A hA) (hsmall.2 B hB),norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (by linarith : 0 ≤ T) n)]
  have hh := hcap A B hA hB n (T*x) (by constructor <;> nlinarith [hx.1,hx.2])
  have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ T^n by positivity)
  exact hm.trans_eq (by field_simp)

theorem dual_support (Phi : ℝ → ℂ) (T : ℝ) (a b : ℂ)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2) (n : ℕ) :
    tsupport (iteratedDeriv n (PRZZKeptLiteral.dualProfile Phi T a b)) ⊆ Icc (1:ℝ) 2 := by
  have hs : tsupport (PRZZKeptLiteral.dualProfile Phi T a b) ⊆ Icc (1:ℝ) 2 := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    exact hsPhi (fun hz => hx (by simp [PRZZKeptLiteral.dualProfile,hz]))
  induction n with
  | zero => exact hs
  | succ n ih => rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans ih

/-- Global all-order bounds, including the support boundary. This is a
single sequence of constants and a single height threshold for all n. -/
theorem profile_uniform (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hcPhi : HasCompactSupport Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (S : ℝ) (hS : 0 ≤ S) :
    ∃ U : ℕ → ℝ, (∀ n, 0 ≤ U n) ∧ ∀ᶠ T : ℝ in atTop,
      ∀ A B : ℂ, ‖A‖ ≤ S → ‖B‖ ≤ S → ∀ n : ℕ, ∀ x : ℝ,
      ‖iteratedDeriv n (PRZZKeptLiteral.dualProfile Phi T
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) x‖ ≤ U n := by
  choose C hC hc using PRZZCutoffJets.ordinary_uniform Phi hPhi hcPhi
  let U := fun n => PRZZFullWeightJets.convolution C
    (fun j => Real.exp (2*S+7)*PRZZDualJetTransfer.constant j) n
  have hU (n : ℕ) : 0 ≤ U n := by
    unfold U PRZZFullWeightJets.convolution
    exact sum_nonneg (fun i hi => mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (hC i))
      (mul_nonneg (Real.exp_pos _).le (PRZZDualJetTransfer.constant_nonneg _)))
  refine ⟨U,hU,?_⟩
  filter_upwards [rescaled_uniform S hS,
    PRZZScaledReplacement.shifts_eventually S (1/4) (by norm_num)] with T hgamma hsmall
  intro A B hA hB n x
  by_cases hx : x ∈ Icc (1:ℝ) 2
  · have hg : ContDiff ℝ ∞ (fun y : ℝ => PRZZAFEDual.dualMultiplier
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) (T*y)) :=
      (PRZZDualSmooth.multiplier_contDiff _ _ (hsmall.2 A hA) (hsmall.2 B hB)).comp
      (contDiff_const.mul contDiff_id)
    unfold PRZZKeptLiteral.dualProfile
    rw [iteratedDeriv_fun_mul (hPhi.contDiffAt.of_le (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤)))
      (hg.contDiffAt.of_le (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤)))]
    apply (norm_sum_le _ _).trans
    unfold U PRZZFullWeightJets.convolution
    apply sum_le_sum
    intro i hi
    simp only [norm_mul,Complex.norm_natCast]
    have hp : ‖iteratedDeriv i Phi x‖ ≤ C i := by
      have he : PRZZMellinSeparation.scaledCutoff Phi 1 = Phi := by
        funext y
        simp [PRZZMellinSeparation.scaledCutoff]
      simpa only [he,one_pow,div_one] using hc i 1 x (by norm_num)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _))
      (hgamma A B hA hB (n-i) x hx) (norm_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (hC i))
  · have hz : iteratedDeriv n (PRZZKeptLiteral.dualProfile Phi T
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) x = 0 := by
      by_contra hh
      exact hx (dual_support Phi T _ _ hsPhi n (subset_closure hh))
    rw [hz,norm_zero]
    exact hU n

#print axioms rescaled_jet
#print axioms rescaled_uniform
#print axioms dual_support
#print axioms profile_uniform
end XiPrime8845.PRZZDualProfileUniform
