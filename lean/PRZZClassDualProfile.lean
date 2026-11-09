import PRZZClassPoisson
import PRZZDualProfileUniform

/-! The genuine Gamma-multiplied time cutoff belongs to one quantitative
Mellin class before height and the bounded logarithmic shift family.
This supplies dual time masses, not negative spatial-frequency bounds. -/
noncomputable section
open scoped ContDiff
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZClassDualProfile
set_option maxHeartbeats 8000000

theorem dual_member (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hcPhi : HasCompactSupport Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (S : ℝ) (hS : 0 ≤ S) :
    ∃ jets : ℕ → ℝ, (∀ n, 0 ≤ jets n) ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S → PRZZProfileMellin.Member (Real.log 2) jets
        (PRZZKeptLiteral.dualProfile Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) := by
  obtain ⟨U,hU,h⟩ := PRZZDualProfileUniform.profile_uniform Phi hPhi hcPhi hsPhi S hS
  refine ⟨fun n => 2^n*U n,fun n => mul_nonneg (by positivity) (hU n),?_⟩
  filter_upwards [h,PRZZScaledReplacement.shifts_eventually S (1/4) (by norm_num)] with T h hsmall
  intro A B hA hB
  let f := PRZZKeptLiteral.dualProfile Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))
  have hs : Function.support f ⊆ Icc (1:ℝ) 2 := by
    intro x hx
    exact hsPhi (fun hz => hx (by simp [f,PRZZKeptLiteral.dualProfile,hz]))
  refine ⟨?_,⟨1,2,by norm_num,by norm_num,hs,by simp⟩,?_⟩
  · exact hPhi.mul ((PRZZDualSmooth.multiplier_contDiff _ _ (hsmall.2 A hA) (hsmall.2 B hB)).comp
      (contDiff_const.mul contDiff_id))
  · intro n x
    by_cases hx : x ∈ Icc (1:ℝ) 2
    · rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith [hx.1] : 0 < x)]
      exact mul_le_mul (pow_le_pow_left₀ (by linarith [hx.1]) hx.2 n) (h A B hA hB n x)
        (norm_nonneg _) (by positivity)
    · have hz : iteratedDeriv n f x = 0 := by
        by_contra hh
        exact hx (PRZZDualProfileUniform.dual_support Phi T _ _ hsPhi n (subset_closure hh))
      rw [hz,mul_zero,norm_zero]
      exact mul_nonneg (by positivity) (hU n)

/-- A single class contains both branches, including the real Gamma
multiplier, with constants selected before height and the two shifts. -/
theorem common_members (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hcPhi : HasCompactSupport Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (S : ℝ) (hS : 0 ≤ S) :
    ∃ jets : ℕ → ℝ, (∀ n, 0 ≤ jets n) ∧ PRZZProfileMellin.Member (Real.log 6) jets Phi ∧
      ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ, ‖A‖ ≤ S → ‖B‖ ≤ S →
        PRZZProfileMellin.Member (Real.log 6) jets
          (PRZZKeptLiteral.dualProfile Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) := by
  obtain ⟨J,hJ,hdual⟩ := dual_member Phi hPhi hcPhi hsPhi S hS
  have hs : Function.support Phi ⊆ Icc (1/2:ℝ) 3 := by
    intro x hx; have hh := hsPhi hx; constructor <;> linarith [hh.1,hh.2]
  obtain ⟨I,hI,hplain⟩ := PRZZClassPoisson.spatial_members Phi hPhi hs
  have hw : Real.log 2 ≤ Real.log 6 := Real.log_le_log (by norm_num) (by norm_num)
  refine ⟨fun n => I n+J n,fun n => add_nonneg (hI n) (hJ n),?_,?_⟩
  · have hp := hplain 1 (by norm_num)
    have he : PRZZMellinSeparation.scaledCutoff Phi 1 = Phi := by
      funext x; simp [PRZZMellinSeparation.scaledCutoff]
    rw [he] at hp
    exact PRZZClassPoisson.member_mono _ _ _ _ le_rfl (fun n => by linarith [hJ n]) Phi hp
  · filter_upwards [hdual] with T hdual
    intro A B hA hB
    exact PRZZClassPoisson.member_mono _ _ _ _ hw (fun n => by linarith [hI n]) _ (hdual A B hA hB)

theorem common_mass (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hcPhi : HasCompactSupport Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (S : ℝ) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 < C ∧ (∫ t : ℝ, (1+|t|)*‖mellin Phi (t*I)‖) ≤ C ∧
      ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ, ‖A‖ ≤ S → ‖B‖ ≤ S →
        (∫ t : ℝ, (1+|t|)*‖mellin
          (PRZZKeptLiteral.dualProfile Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) (t*I)‖) ≤ C := by
  obtain ⟨jets,hj,hplain,hdual⟩ := common_members Phi hPhi hcPhi hsPhi S hS
  have hcap := PRZZProfileMellin.massCap_nonneg (Real.log 6) (Real.log_nonneg (by norm_num)) jets hj
  refine ⟨PRZZProfileMellin.massCap (Real.log 6) jets+1,by positivity,?_,?_⟩
  · exact (PRZZProfileMellin.member_mass _ jets hj Phi hplain).trans (by linarith)
  · filter_upwards [hdual] with T hdual
    intro A B hA hB
    exact (PRZZProfileMellin.member_mass _ jets hj _ (hdual A B hA hB)).trans (by linarith)

#print axioms dual_member
#print axioms common_members
#print axioms common_mass
end XiPrime8845.PRZZClassDualProfile
