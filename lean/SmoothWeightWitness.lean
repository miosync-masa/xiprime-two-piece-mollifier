import PRZZInterface
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! Nonvacuity of the corrected C-infinity smoothing interface.
The plateau is fixed before the height tends to infinity. All results here
are independent of the external PRZZ estimate. -/
noncomputable section
open MeasureTheory
namespace XiPrime8845.SmoothWeightWitness

/-- Fixed smooth weights satisfy the derivative growth condition in PRZZ.
The constant depends on Phi and j, not on T or x. This is not uniform over
families whose smoothing width tends to zero with T. -/
theorem derivative_log_bound (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, Real.exp 1 ≤ T → ∀ x : ℝ,
      ‖iteratedDeriv j Phi x‖ ≤ C * (Real.log T)^j := by
  have hs : HasCompactSupport Phi :=
    isCompact_Icc.of_isClosed_subset isClosed_closure (closure_minimal hPhi.2 isClosed_Icc)
  have hsj : ∀ k : ℕ, HasCompactSupport (iteratedDeriv k Phi) := by
    intro k
    induction k with
    | zero => simpa using hs
    | succ k hk => simpa only [iteratedDeriv_succ] using hk.deriv
  obtain ⟨C, hC⟩ := (hsj j).exists_bound_of_continuous
    (hPhi.1.continuous_iteratedDeriv j (by
      exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top)))
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro T hT x
  have ht : 0 < T := (Real.exp_pos 1).trans_le hT
  have hl : 1 ≤ Real.log T := (Real.le_log_iff_exp_le ht).mpr hT
  exact (hC x).trans ((le_max_left C 1).trans
    (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hl)))

def plateau : ContDiffBump (3/2 : ℝ) :=
  ⟨1/4, 1/2, by norm_num, by norm_num⟩

theorem plateau_smooth : PRZZ.SmoothWeight plateau := by
  refine ⟨plateau.contDiff, ?_⟩
  rw [plateau.support_eq]
  intro x hx
  have hh : |x-3/2| < (1/2 : ℝ) := by simpa [Real.dist_eq, plateau] using hx
  rw [abs_lt] at hh
  exact ⟨by linarith, by linarith⟩

theorem plateau_one (x : ℝ) (hx : x ∈ Set.Icc (5/4 : ℝ) (7/4)) :
    plateau x = 1 := by
  apply plateau.one_of_mem_closedBall
  change dist x (3/2 : ℝ) ≤ 1/4
  rw [Real.dist_eq, abs_le]
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem plateau_nonneg (x : ℝ) : 0 ≤ plateau x := plateau.nonneg

theorem plateau_le_one (x : ℝ) : plateau x ≤ 1 := plateau.le_one

theorem plateau_mass_bounds :
    (1/2 : ℝ) ≤ ∫ x in Set.Icc (1 : ℝ) 2, plateau x ∧
    (∫ x in Set.Icc (1 : ℝ) 2, plateau x) ≤ 1 := by
  have hi : IntegrableOn plateau (Set.Icc (1 : ℝ) 2) :=
    plateau.continuous.continuousOn.integrableOn_compact isCompact_Icc
  constructor
  · have hs : Set.Icc (5/4 : ℝ) (7/4) ⊆ Set.Icc (1 : ℝ) 2 := by
      intro x hx; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hm := setIntegral_mono_set hi
      (Filter.Eventually.of_forall (fun x => plateau_nonneg x))
      (Filter.Eventually.of_forall hs)
    have he : (∫ x in Set.Icc (5/4 : ℝ) (7/4), plateau x) = 1/2 := by
      rw [setIntegral_congr_fun measurableSet_Icc plateau_one]
      norm_num
    exact he ▸ hm
  · have hm := setIntegral_mono_on hi
      (show IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc (1 : ℝ) 2) from
        integrableOn_const (hs := by simp))
      measurableSet_Icc (fun x _ => plateau_le_one x)
    norm_num at hm ⊢
    exact hm

theorem positive_mass_witness :
    ∃ Phi : ℝ → ℝ, PRZZ.SmoothWeight Phi ∧ (∀ x, 0 ≤ Phi x) ∧
      0 < ∫ x in Set.Icc (1 : ℝ) 2, Phi x :=
  ⟨plateau, plateau_smooth, plateau_nonneg,
    lt_of_lt_of_le (by norm_num) plateau_mass_bounds.1⟩

#print axioms plateau_smooth
#print axioms plateau_one
#print axioms plateau_nonneg
#print axioms plateau_le_one
#print axioms plateau_mass_bounds
#print axioms positive_mass_witness
#print axioms derivative_log_bound
end XiPrime8845.SmoothWeightWitness
