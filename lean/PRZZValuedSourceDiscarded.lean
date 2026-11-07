import PRZZValuedCutoffs
import PRZZWindowTailTime

/-! Source geometry and actual cutoff amplitudes supplied simultaneously
for the discarded exact-phase sum. Both kernel shift reflections are
allowed. A time-dependent dual Gamma multiplier is not silently frozen. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Set MeasureTheory Filter
namespace XiPrime8845.PRZZValuedSourceDiscarded
open PRZZMellinSeparation PRZZDiscardedOuter
set_option maxHeartbeats 5000000

def error (F G H : ℝ → ℂ) (P : ℝ → ℝ) (js : List ℕ) (N K : ℕ)
    (T M Q V d eps : ℝ) (A B : ℂ) (s : ℕ → ℕ → Finset (ℕ × ℕ)) : ℂ :=
  tailError F js N T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))
    ((A+B)/(Real.log T:ℂ)) s (fun u v p =>
      (scaledCutoff G Q (d*u)*scaledCutoff H V (d*v))*
        sourceMask P (scaledCutoff G Q) K T M Q d eps u v p)

theorem scaled_negligible (F G H : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hcF : HasCompactSupport F) (hsF : Function.support F ⊆ Icc (1:ℝ) 2)
    (hG : Continuous G) (hH : Continuous H) (hcG : HasCompactSupport G) (hcH : HasCompactSupport H)
    (hsG : Function.support G ⊆ Icc (1/2:ℝ) 3)
    (js : List ℕ) (S r eps power : ℝ) (hr : 0 < r) (he : 0 < eps) (he1 : eps ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (N K : ℕ) (M Q V d : ℝ) (A B : ℂ) (P : ℝ → ℝ)
        (s : ℕ → ℕ → Finset (ℕ × ℕ)),
      1 ≤ N → (N:ℝ) ≤ T → 0 < M → 0 < Q → 0 < d →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      Antitone P → (∀ x, 0 ≤ P x) → (∀ x, P x ≤ 1) →
      (∀ x ≤ (1/2:ℝ), P x = 1) → (∀ x, 1 ≤ x → P x = 0) →
      ‖error F G H P js N K T M Q V d eps A B s‖ ≤ C*T^(-power) := by
  obtain ⟨C,hC,h⟩ := PRZZValuedCutoffs.valued_negligible F G H hF hcF hsF
    hG hH hcG hcH js eps power r he hr
  refine ⟨C,hC,?_⟩
  filter_upwards [PRZZScaledReplacement.shifts_eventually S (1/4) (by norm_num),
    eventually_ge_atTop (Real.exp 1)] with T hsmall hlarge
  have hT : 1 < T := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by norm_num)) hlarge
  have hlog : 1 ≤ Real.log T := by
    have hh := Real.log_le_log (Real.exp_pos 1) hlarge
    simpa using hh
  intro N K M Q V d A B P s hN hNT hM hQ hd hA hB hsep hm hlo hhi hleft hright
  have ha := (Complex.abs_re_le_norm (A/(Real.log T:ℂ))).trans (hsmall.2 A hA)
  have hb := (Complex.abs_re_le_norm (B/(Real.log T:ℂ))).trans (hsmall.2 B hB)
  have hg := source_geometry P (scaledCutoff G Q) hm hlo hhi hleft hright N K T M Q d eps
    (by linarith) hM hQ hd
    (Real.one_le_rpow hT.le (by linarith))
    (PRZZWindowTailTime.scaled_support G Q hQ hsG) s
  exact h N A B _ _ T Q V d hN hNT hT hlog hsep
    (by linarith [(abs_le.mp ha).1]) (by linarith [(abs_le.mp hb).1]) s _ hg

#print axioms scaled_negligible
end XiPrime8845.PRZZValuedSourceDiscarded
