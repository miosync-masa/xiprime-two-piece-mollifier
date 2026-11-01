import PRZZSourceEnvelope
import PRZZGAbsorption

/-! Height-uniform absorption of the actual Type I source budget.
The derivative order ranges over a fixed finite set. Constants precede T,
the Mellin variable and all arithmetic parameters. Contour bounds remain
explicit; Weil is a proposition argument, not a new axiom. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset
namespace XiPrime8845.PRZZSourceAbsorption
open PRZZSourceEnvelope PRZZTypeI PRZZTypeIWeights PRZZMellinSeparation
set_option maxHeartbeats 2000000

theorem finite_log_powers (J : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ∀ j ≤ J,
      (Real.log T)^j ≤ C*T^eps := by
  choose c hc hb using fun j => PRZZGAbsorption.log_pow_bound j eps heps
  refine ⟨∑ j ∈ range (J+1), c j, ?_, ?_⟩
  · exact sum_pos (fun j _ => hc j) (by simp)
  intro T hT j hj
  exact (hb j T hT).trans (mul_le_mul_of_nonneg_right
    (single_le_sum (fun k _ => (hc k).le) (mem_range.mpr (by omega)))
    (Real.rpow_nonneg (by linarith) _))

theorem exponent_norm (sigma A : ℝ) (alpha w : ℂ)
    (ha : |sigma|+1/2+‖alpha‖ ≤ A) :
    ‖exponent sigma alpha w‖ ≤ (A+1)*(1+‖w‖) := by
  have hn : ‖exponent sigma alpha w‖ ≤ |sigma|+1/2+‖alpha‖+‖w‖ := by
    calc
      _ ≤ ‖((sigma:ℂ)-1/2-alpha)‖+‖w‖ := norm_sub_le _ _
      _ ≤ (‖(sigma:ℂ)‖+‖(1:ℂ)/2‖)+‖alpha‖+‖w‖ := by
        gcongr
        exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ = _ := by simp
  have hA : 0 ≤ A := by linarith [abs_nonneg sigma, norm_nonneg alpha]
  nlinarith [norm_nonneg w]

theorem budget_absorbed (J : ℕ) (eps C0 C1 S Z : ℝ)
    (heps : 0 < eps) (h0 : 0 ≤ C0) (h1 : 0 ≤ C1) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 < T → ∀ z w : ℂ, ∀ j ≤ J,
      ‖z‖ ≤ Z*(1+‖w‖) → budget C0 C1 S T z j ≤ C*(1+‖w‖)*T^eps := by
  obtain ⟨D,hD,hd⟩ := finite_log_powers J eps heps
  let C := Real.exp S*D*C0+2*(Real.exp S*((Z*D+(J:ℝ)*D)*C0+D*C1))+1
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro T hT z w j hj hz
  have ht : 0 ≤ T^eps := Real.rpow_nonneg (by linarith) _
  have hw : 1 ≤ 1+‖w‖ := by linarith [norm_nonneg w]
  have hjr : (j:ℝ) ≤ J := by exact_mod_cast hj
  have hp := hd T hT.le j hj
  have hprev := hd T hT.le (j-1) (by omega)
  have hp' : (Real.log T)^j ≤ D*((1+‖w‖)*T^eps) := by
    calc
      _ ≤ D*T^eps := hp
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_mul_of_one_le_left ht hw) hD.le
  have hprev' : (Real.log T)^(j-1) ≤ D*((1+‖w‖)*T^eps) := by
    calc
      _ ≤ D*T^eps := hprev
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_mul_of_one_le_left ht hw) hD.le
  have hzp : ‖z‖*(Real.log T)^j ≤ (Z*D)*((1+‖w‖)*T^eps) := by
    calc
      _ ≤ (Z*(1+‖w‖))*(D*T^eps) := mul_le_mul hz hp
        (pow_nonneg (Real.log_pos hT).le _) (by positivity)
      _ = _ := by ring
  have hjp : (j:ℝ)*(Real.log T)^(j-1) ≤ ((J:ℝ)*D)*((1+‖w‖)*T^eps) := by
    calc
      _ ≤ (J:ℝ)*(D*((1+‖w‖)*T^eps)) := mul_le_mul hjr hprev'
        (pow_nonneg (Real.log_pos hT).le _) (Nat.cast_nonneg _)
      _ = _ := by ring
  unfold budget
  calc
    _ ≤ Real.exp S*(D*((1+‖w‖)*T^eps))*C0+
        2*(Real.exp S*((Z*D*((1+‖w‖)*T^eps)+(J:ℝ)*D*((1+‖w‖)*T^eps))*C0+
          D*((1+‖w‖)*T^eps)*C1)) := by gcongr
    _ ≤ C*(1+‖w‖)*T^eps := by dsimp [C]; nlinarith [mul_nonneg (by positivity : 0 ≤ 1+‖w‖) ht]

/-- One constant covers all source orders through J and all admissible
arithmetic intervals, with the actual exponent and cutoff retained. -/
theorem source_weil_absorbed (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (eps eta S A : ℝ) (J : ℕ) (heps : 0 < eps) (heta : 0 < eta)
    (hS : 0 ≤ S) (hA : 0 ≤ A)
    (F0 : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0) :
    ∃ C : ℝ, 0 < C ∧ ∀ T N kappa F sigma : ℝ, ∀ alpha w : ℂ,
      ∀ j H M q : ℕ, ∀ b : ℤ,
      1 < T → 0 < F → F ≤ (M:ℝ)+1 → (M:ℝ)+1+H ≤ T → (H:ℝ) ≤ 2*F →
      sigma ≤ 1/2 → 0 ≤ w.re → |alpha.re| ≤ S/Real.log T →
      |sigma|+1/2+‖alpha‖ ≤ A → j ≤ J → 1 ≤ q →
      ‖weightedSum q b M H (fun k => sourceWeight (exponent sigma alpha w) j kappa
        (scaledCutoff F0 N) ((M:ℝ)+1+k))‖ ≤
        C*(1+‖w‖)*T^eta*(q:ℝ)^(1/2+eps)*(b.natAbs.gcd q)*(1+(H:ℝ)/q) := by
  obtain ⟨K,C0,C1,hK,h0,h1,h⟩ := source_weil hWeil eps heps F0 hf hc
  obtain ⟨D,hD,hd⟩ := budget_absorbed J eta C0 C1 S (A+1) heta h0 h1 (by positivity)
  refine ⟨K*D,mul_pos hK hD,?_⟩
  intro T N kappa F sigma alpha w j H M q b hT hF hFM hMT hH hs hw ha hnorm hj hq
  apply (h T S N kappa F sigma alpha w j H M q b hT hS hF hFM hMT hH hs hw ha hq).trans
  have hb := hd T hT _ w j hj (exponent_norm sigma A alpha w hnorm)
  have hp : 0 ≤ K*(q:ℝ)^(1/2+eps)*(b.natAbs.gcd q)*(1+(H:ℝ)/q) :=
    mul_nonneg (mul_nonneg (mul_nonneg hK.le (Real.rpow_nonneg (Nat.cast_nonneg q) _))
      (Nat.cast_nonneg _)) (add_nonneg zero_le_one (div_nonneg (Nat.cast_nonneg H) (Nat.cast_nonneg q)))
  exact (mul_le_mul_of_nonneg_left hb hp).trans_eq (by ring)

#print axioms source_weil_absorbed
#print axioms finite_log_powers
#print axioms exponent_norm
#print axioms budget_absorbed
end XiPrime8845.PRZZSourceAbsorption
