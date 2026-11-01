import PRZZMaskedVariation
import PRZZSourceEnvelope

/-! Height-uniform smooth source envelopes survive sharp interval masks.
Constants depend on the fixed cutoff, before height, scale and endpoints.
This is a sourceWeight supplier, not an identification of every HB row. -/
noncomputable section
open scoped BigOperators ContDiff
open Set
namespace XiPrime8845.PRZZMaskedSource
open PRZZMaskedVariation PRZZSourceEnvelope PRZZTypeIWeights PRZZMellinSeparation
set_option maxHeartbeats 2000000

theorem source_uniform (F0 : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0)
    (hc : HasCompactSupport F0) :
    ∃ C0 C1 C2 : ℝ, 0 ≤ C0 ∧ 0 ≤ C1 ∧ 0 ≤ C2 ∧
      ∀ T S N kappa a F sigma : ℝ, ∀ alpha w : ℂ, ∀ j H lo hi : ℕ,
      1 < T → 0 ≤ S → 0 < F → F ≤ a → 1 ≤ a → a+H ≤ T → (H:ℝ) ≤ 2*F →
      sigma ≤ 1/2 → 0 ≤ w.re → |alpha.re| ≤ S/Real.log T →
      PRZZTypeI.variation (mask lo hi
        (fun k => sourceWeight (exponent sigma alpha w) j kappa (scaledCutoff F0 N) (a+k))) H ≤
      budget C0 C1 S T (exponent sigma alpha w) j+2*(Real.exp S*(Real.log T)^j*C2) := by
  obtain ⟨C0,C1,h0,h1,hv⟩ := source_variation_uniform F0 hf hc
  obtain ⟨C2,C3,h2,h3,hcut⟩ := PRZZSmoothWeights.cutoff_bounds F0 hf hc
  refine ⟨C0,C1,C2,h0,h1,h2,?_⟩
  intro T S N kappa a F sigma alpha w j H lo hi hT hS hF hFa ha haT hH hs hw halpha
  have hL : 0 ≤ Real.log T := (Real.log_pos hT).le
  apply mask_of_variation lo hi H _ (Real.exp S*(Real.log T)^j*C2) _ (by positivity) _
    (hv T S N kappa a F sigma alpha w j H hT hS hF hFa ha haT hH hs hw halpha)
  intro k hk
  have hkR : (k:ℝ) ≤ H := by exact_mod_cast hk
  have hx : a+k ∈ Icc 1 T := ⟨by have := Nat.cast_nonneg (α := ℝ) k; linarith, by linarith⟩
  have he := power_log T S (a+k) (exponent sigma alpha w) hT hS hx
    (exponent_re sigma S T alpha w hs hw halpha)
  unfold sourceWeight
  simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul (mul_le_mul he.1
    (pow_le_pow_left₀ (abs_nonneg _) he.2 j) (by positivity) (Real.exp_pos S).le)
    (hcut N (kappa*(a+k))).1 (norm_nonneg _) (by positivity)

#print axioms source_uniform
end XiPrime8845.PRZZMaskedSource
