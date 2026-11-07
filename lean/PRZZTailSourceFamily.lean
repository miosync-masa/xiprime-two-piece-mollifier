import PRZZZeroPhaseBudget

/-! Uniform suppliers on an explicit source parameter domain. All indices
and times are quantified after the constants. Membership of the full
original arithmetic family in this domain is not asserted here. -/
noncomputable section
namespace XiPrime8845.PRZZTailSourceFamily
set_option maxHeartbeats 2000000

theorem quadratic_scale (T M u v t : ℝ) (hT : 4 ≤ T)
    (hM : 1 ≤ M) (hu : 1 ≤ u) (hv : 0 < v) (hvT : v ≤ T)
    (ht : 0 < t) (htT : t ≤ 2*T) :
    T^(-(3:ℝ)) ≤ (2*Real.pi*u/(t*v))*(M/2)^2 := by
  have hT0 : 0 < T := by linarith
  have hden : t*v ≤ 2*T^2 := by nlinarith [mul_le_mul htT hvT hv.le (by positivity : 0 ≤ 2*T)]
  have hnum : 1 ≤ 2*Real.pi*u*(M/2)^2 := by
    have hm : 1 ≤ M^2 := one_le_pow₀ hM
    have hpi := Real.pi_gt_three
    nlinarith [mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ 2*Real.pi)]
  rw [Real.rpow_neg hT0.le,Real.rpow_ofNat]
  calc
    _ ≤ 1/(2*T^2) := by
      rw [inv_eq_one_div]
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith [sq_nonneg T]
    _ ≤ (2*Real.pi*u*(M/2)^2)/(t*v) := by
      apply div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = _ := by ring

theorem modulus_scale (T M q : ℝ) (hM : 1 ≤ M) (hq : 0 ≤ q) (hqT : q ≤ T) :
    q/M ≤ T^(1:ℝ) := by
  rw [Real.rpow_one]
  exact (div_le_self hq hM).trans hqT

theorem window_log (T M : ℝ) (hM : 1 ≤ M) (hMT : M ≤ T)
    (hlog : 1 ≤ Real.log T) :
    |Real.log (M/2)|+|Real.log (3*M)| ≤
      (2+Real.log 2+Real.log 3)*Real.log T := by
  have hM0 : 0 < M := by linarith
  have hm : 0 ≤ Real.log M := Real.log_nonneg hM
  have hmt := Real.log_le_log hM0 hMT
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  rw [Real.log_div hM0.ne' (by norm_num),Real.log_mul (by norm_num) hM0.ne']
  have hab := abs_sub (Real.log M) (Real.log 2)
  rw [abs_of_nonneg hm,abs_of_nonneg h2] at hab
  rw [abs_of_nonneg (add_nonneg h3 hm)]
  nlinarith

theorem shift_envelopes (T M S r : ℝ) (A B : ℂ)
    (hlog : 1 ≤ Real.log T) (hM : 1 ≤ M) (hMT : M ≤ T)
    (hA : ‖A‖ ≤ S) (hr : 0 < r) (hsep : r ≤ ‖A+B‖) :
    ‖A/(Real.log T:ℂ)‖ ≤ S ∧
    ‖A/(Real.log T:ℂ)‖*(|Real.log (M/2)|+|Real.log (3*M)|) ≤
      S*(2+Real.log 2+Real.log 3) ∧
    1/‖(A+B)/(Real.log T:ℂ)‖^2 ≤ (Real.log T)^2/r^2 := by
  have hL : 0 < Real.log T := by linarith
  have hS : 0 ≤ S := (norm_nonneg _).trans hA
  have he : ‖A/(Real.log T:ℂ)‖ = ‖A‖/Real.log T := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
  refine ⟨?_,?_,?_⟩
  · rw [he]; exact (div_le_self (norm_nonneg _) hlog).trans hA
  · rw [he]
    calc
      _ ≤ (S/Real.log T)*((2+Real.log 2+Real.log 3)*Real.log T) := by
        gcongr
        exact window_log T M hM hMT hlog
      _ = _ := by field_simp
  · simpa using PRZZJetUniform.shift_cost 0 1 r (Real.log T) A B
      (by norm_num) hr hL.ne' hsep

/-- The actual zero-phase cap, with logarithmic shifts and the source
quadratic argument, is substituted into the cutoff gain. No separate
polynomial cap or local scale comparison is assumed. -/
theorem source_absorbed (C D E : ℕ → ℝ) (a S r eD eH A : ℝ)
    (hc : ∀ i, 0 ≤ C i ∧ 0 ≤ D i ∧ 0 ≤ E i) (ha : 0 ≤ a)
    (hS : 0 ≤ S) (hr : 0 < r) (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ n : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ d T M Q q h u v t : ℝ, ∀ alpha beta : ℂ,
      0 < d → 4 ≤ T → 1 ≤ Real.log T → 1 ≤ M → M ≤ T →
      0 < Q → 0 ≤ q → q ≤ T → q ≤ 3*Q/d →
      1 ≤ u → 0 < v → v ≤ T → 0 < t → t ≤ 2*T →
      ‖alpha‖ ≤ S → r ≤ ‖alpha+beta‖ →
      PRZZSourceCutoffs.poissonCutoff d T M Q eH ≤ h →
      PRZZEnvelopeMass.cap C D E a (2*Real.pi*u/(t*v)) M 0
        (|Real.log (M/2)|+|Real.log (3*M)|)
        (alpha/(Real.log T:ℂ)) ((alpha+beta)/(Real.log T:ℂ)) (n+2)*
        (1+8*T^eD)^2*(q/M)*((1+8*T^eD)*q/(M*h))^n ≤ K*T^(-A) := by
  obtain ⟨n,K,hK,h⟩ := PRZZZeroPhaseBudget.absorbed C D E a S
    (S*(2+Real.log 2+Real.log 3)) r 3 1 eD eH A hc ha hS hr heD he
  refine ⟨n,K,hK,?_⟩
  intro d T M Q q hcut u v t alpha beta hd hT hlog hM hMT hQ hq hqT hbox
    hu hv hvT ht htT halpha hsep hcutoff
  have hk : 0 < 2*Real.pi*u/(t*v) := by positivity
  obtain ⟨hz,hP,hs⟩ := shift_envelopes T M S r alpha beta hlog hM hMT halpha hr hsep
  have hc0 := PRZZJetUniform.cap_uniform C D E a (2*Real.pi*u/(t*v)) M 0
    (|Real.log (M/2)|+|Real.log (3*M)|) S (S*(2+Real.log 2+Real.log 3))
    ((Real.log T)^2/r^2) (alpha/(Real.log T:ℂ)) ((alpha+beta)/(Real.log T:ℂ))
    (n+2) hc hk.le (by norm_num) hS hz hP hs
  have hh0 : 0 < hcut := lt_of_lt_of_le
    (by unfold PRZZSourceCutoffs.poissonCutoff; positivity) hcutoff
  apply le_trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc0 (sq_nonneg _))
      (by positivity : 0 ≤ q/M)) (by positivity))
  exact h d T M Q q hcut (2*Real.pi*u/(t*v)) hd (by linarith) (by linarith)
    hQ hq hbox hk hcutoff (quadratic_scale T M u v t hT hM hu hv hvT ht htT)
    (modulus_scale T M q hM hq hqT)

#print axioms source_absorbed
#print axioms quadratic_scale
#print axioms modulus_scale
#print axioms window_log
#print axioms shift_envelopes
end XiPrime8845.PRZZTailSourceFamily
