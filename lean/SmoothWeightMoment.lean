import SmoothWeightWitness
import WuMomentTransfer

/-! A concrete, nonvacuous instance of both moment bounds. Existence and
positive mass of the weight use no analytic axiom. The moment bounds still
depend on the single, explicitly named external PRZZ estimate. -/
noncomputable section
open Filter Topology
namespace XiPrime8845.SmoothWeightMoment
open SmoothWeightWitness WitnessMomentBound WuMomentTransfer

theorem plateau_mass_pos : 0 < mass plateau :=
  lt_of_lt_of_le (by norm_num) plateau_mass_bounds.1

theorem plateau_u_moment_bound :
    (0.8845 : ℝ) < 1-Real.log countingCap/NumericalGate.R ∧
      ∀ᶠ T : ℝ in atTop, 1 < T ∧
        0 ≤ normalizedMoment plateau T ∧ normalizedMoment plateau T < countingCap :=
  witness_moment_bound plateau plateau_smooth plateau_nonneg plateau_mass_pos

theorem plateau_v_moment_bound :
    (0.8845 : ℝ) < 1-Real.log countingCap/NumericalGate.R ∧
      ∀ᶠ T : ℝ in atTop, 1 < T ∧
        0 ≤ normalizedVMoment plateau T ∧ normalizedVMoment plateau T < countingCap :=
  v_moment_bound plateau plateau_smooth plateau_nonneg plateau_mass_pos

#print axioms plateau_mass_pos
#print axioms plateau_u_moment_bound
#print axioms plateau_v_moment_bound
end XiPrime8845.SmoothWeightMoment
