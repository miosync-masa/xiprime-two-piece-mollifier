import PRZZMaskedSource
import PRZZSourceAbsorption

/-! The two sharp-cutoff jumps and smooth variation share a height-uniform
subpower budget, linear in the Mellin variable. No row identity is assumed. -/
noncomputable section
open scoped ContDiff
namespace XiPrime8845.PRZZMaskedAbsorption
open PRZZSourceEnvelope PRZZTypeIWeights PRZZMellinSeparation
set_option maxHeartbeats 2000000

theorem source_absorbed (F0 : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0)
    (hc : HasCompactSupport F0) (J : ℕ) (eps S Z : ℝ)
    (heps : 0 < eps) (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ T N kappa a F sigma : ℝ, ∀ alpha w : ℂ, ∀ j H lo hi : ℕ,
      1 < T → 0 < F → F ≤ a → 1 ≤ a → a+H ≤ T → (H:ℝ) ≤ 2*F →
      sigma ≤ 1/2 → 0 ≤ w.re → |alpha.re| ≤ S/Real.log T →
      |sigma|+1/2+‖alpha‖ ≤ Z → j ≤ J →
      PRZZTypeI.variation (PRZZMaskedVariation.mask lo hi
        (fun k => sourceWeight (exponent sigma alpha w) j kappa (scaledCutoff F0 N) (a+k))) H ≤
      C*(1+‖w‖)*T^eps := by
  obtain ⟨C0,C1,C2,h0,h1,h2,hv⟩ := PRZZMaskedSource.source_uniform F0 hf hc
  obtain ⟨B,hB,hb⟩ := PRZZSourceAbsorption.budget_absorbed J eps C0 C1 S (Z+1)
    heps h0 h1 (by positivity)
  obtain ⟨D,hD,hd⟩ := PRZZSourceAbsorption.finite_log_powers J eps heps
  refine ⟨B+2*Real.exp S*D*C2,by positivity,?_⟩
  intro T N kappa a F sigma alpha w j H lo hi hT hF hFa ha haT hH hs hw halpha hz hj
  apply (hv T S N kappa a F sigma alpha w j H lo hi hT hS hF hFa ha haT hH hs hw halpha).trans
  have hb' := hb T hT _ w j hj (PRZZSourceAbsorption.exponent_norm sigma Z alpha w hz)
  have ht : 0 ≤ T^eps := Real.rpow_nonneg (by linarith) _
  have hh : 2*(Real.exp S*(Real.log T)^j*C2) ≤
      (2*Real.exp S*D*C2)*(1+‖w‖)*T^eps := by
    calc
      _ ≤ 2*(Real.exp S*(D*T^eps)*C2) := by gcongr; exact hd T hT.le j hj
      _ ≤ _ := by nlinarith [norm_nonneg w, mul_nonneg (by positivity : 0 ≤ 2*Real.exp S*D*C2) ht]
  exact (add_le_add hb' hh).trans_eq (by ring)

#print axioms source_absorbed
end XiPrime8845.PRZZMaskedAbsorption
