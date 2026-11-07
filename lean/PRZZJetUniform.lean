import PRZZEnvelopeMass

/-! Uniform shift coefficients and explicit phase-polynomial exponents.
The polynomial degree is retained; no optimized tail exponent is asserted. -/
noncomputable section
open scoped BigOperators
namespace XiPrime8845.PRZZJetUniform
open PRZZFullWeightJets PRZZEnvelopeMass
set_option maxHeartbeats 2000000

theorem power_coeff (z : ℂ) (Z : ℝ) (hZ : 0 ≤ Z) (hz : ‖z‖ ≤ Z) (n : ℕ) :
    ‖PRZZPowerJets.coeff z n‖ ≤ (Z+n)^n := by
  induction n with
  | zero => simp [PRZZPowerJets.coeff]
  | succ n ih =>
    rw [PRZZPowerJets.coeff,norm_mul]
    have hh : ‖-z-(n:ℂ)‖ ≤ Z+n := by
      exact (norm_sub_le _ _).trans (by simpa using add_le_add_right hz (n:ℝ))
    calc
      _ ≤ (Z+n)^n*(Z+n) := mul_le_mul ih hh (norm_nonneg _) (by positivity)
      _ ≤ (Z+(n+1:ℕ))^n*(Z+(n+1:ℕ)) := by push_cast; gcongr <;> linarith
      _ = _ := by rw [pow_succ]

theorem phase_polynomial (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    PRZZReciprocalJets.envelope n R ≤
      PRZZReciprocalJets.envelope n 1*(1+R)^(PRZZReciprocalJets.polys n).natDegree := by
  unfold PRZZReciprocalJets.envelope
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i ≤ (PRZZReciprocalJets.polys n).natDegree :=
    Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hi)
  simp only [one_pow,mul_one]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact (pow_le_pow_left₀ hR (by linarith : R ≤ 1+R) i).trans
    (pow_le_pow_right₀ (by linarith : 1 ≤ 1+R) hi')

/-- The singular shift cost for the actual logarithmically scaled family. -/
theorem shift_cost (D E r L : ℝ) (A B : ℂ) (hE : 0 ≤ E)
    (hr : 0 < r) (hL : L ≠ 0) (hsep : r ≤ ‖A+B‖) :
    D+E/‖(A+B)/(L:ℂ)‖^2 ≤ D+E*L^2/r^2 := by
  have hab : 0 < ‖A+B‖ := hr.trans_le hsep
  rw [norm_div,div_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  have he : E/(‖A+B‖^2/L^2) = E*L^2/‖A+B‖^2 := by field_simp
  rw [he]
  gcongr

def uniformCap (C D E : ℕ → ℝ) (a k M R Z P s : ℝ) (n : ℕ) : ℝ :=
  convolution (convolution (convolution C (fun i => (Z+i)^i*Real.exp P))
    (fun i => PRZZReciprocalJets.envelope i 1*(1+R)^(PRZZReciprocalJets.polys i).natDegree))
    (fun i => (D i+E i*s)*(k*(M/2)^2)^(-a)) n

theorem cap_uniform (C D E : ℕ → ℝ) (a k M R L Z P s : ℝ) (z sigma : ℂ) (n : ℕ)
    (hc : ∀ i, 0 ≤ C i ∧ 0 ≤ D i ∧ 0 ≤ E i) (hk : 0 ≤ k) (hR : 0 ≤ R)
    (hZ : 0 ≤ Z) (hz : ‖z‖ ≤ Z) (hP : ‖z‖*L ≤ P) (hs : 1/‖sigma‖^2 ≤ s) :
    cap C D E a k M R L z sigma n ≤ uniformCap C D E a k M R Z P s n := by
  unfold cap uniformCap
  apply convolution_mono
  · apply convolution_nonneg
    · exact convolution_nonneg _ _ (fun i => (hc i).1) (fun i => by positivity)
    · exact fun i => PRZZReciprocalJets.envelope_nonneg i R hR
  · intro i; obtain ⟨hd,he⟩ := (hc i).2; positivity
  · intro i
    apply convolution_mono
    · exact convolution_nonneg _ _ (fun i => (hc i).1) (fun i => by positivity)
    · exact fun i => PRZZReciprocalJets.envelope_nonneg i R hR
    · intro j
      apply convolution_mono _ _ _ _ (fun i => (hc i).1) (fun i => by positivity) (fun i => le_rfl)
      intro i
      exact mul_le_mul (power_coeff z Z hZ hz i) (Real.exp_le_exp.mpr hP)
        (Real.exp_nonneg _) (by positivity)
    · exact fun i => phase_polynomial i R hR
  · intro i
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hh := mul_le_mul_of_nonneg_left hs (hc i).2.2
    simpa [div_eq_mul_inv] using add_le_add_left hh (D i)

#print axioms cap_uniform
#print axioms power_coeff
#print axioms phase_polynomial
#print axioms shift_cost
end XiPrime8845.PRZZJetUniform
