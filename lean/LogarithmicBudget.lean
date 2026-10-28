import FixedCertificate

/-! The numerical margin in the logarithmic units used by Wu's method.
No phase count, Littlewood identity, or zero-proportion bound is assumed here.
The positivity of a putative moment is an explicit hypothesis, not inferred
from an upper bound on the real part of the finite functional. -/
noncomputable section
namespace XiPrime8845.LogarithmicBudget
open NumericalGate

def certifiedCap : ℝ := 1.128201
def budget : ℝ := 1 - Real.log certifiedCap / R

theorem actual_le_cap : actual.re ≤ certifiedCap := FixedCertificate.actual_upper

theorem cap_pos : 0 < certifiedCap := by norm_num [certifiedCap]

theorem cap_lt_target : certifiedCap < target := by
  have h := target_lower
  norm_num [certifiedCap] at ⊢
  linarith

/-- A fixed positive margin, not merely an eventual strict inequality for counts. -/
theorem budget_gt_target : (0.8845 : ℝ) < budget := by
  have hR : 0 < R := by norm_num [R]
  have hlog : Real.log certifiedCap < R * (1 - 0.8845) :=
    (Real.log_lt_iff_lt_exp cap_pos).mpr cap_lt_target
  have hdiv : Real.log certifiedCap / R < 1 - 0.8845 :=
    (div_lt_iff₀ hR).mpr (by nlinarith)
  unfold budget
  linarith

/-- Any positive moment bounded by the certified cap inherits the SAME margin. -/
theorem budget_le_of_moment_le_cap (M : ℝ) (hM : 0 < M) (hcap : M ≤ certifiedCap) :
    budget ≤ 1 - Real.log M / R := by
  have hlog := Real.log_le_log hM hcap
  have hdiv := div_le_div_of_nonneg_right hlog (show 0 ≤ R by norm_num [R])
  unfold budget
  linarith

theorem positive_moment_gate (M : ℝ) (hM : 0 < M) (hcap : M ≤ actual.re) :
    (0.8845 : ℝ) < 1 - Real.log M / R :=
  budget_gt_target.trans_le (budget_le_of_moment_le_cap M hM (hcap.trans actual_le_cap))

#print axioms actual_le_cap
#print axioms cap_pos
#print axioms cap_lt_target
#print axioms budget_gt_target
#print axioms budget_le_of_moment_le_cap
#print axioms positive_moment_gate
end XiPrime8845.LogarithmicBudget
