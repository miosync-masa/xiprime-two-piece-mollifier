import PRZZEulerSubpower

/-! Independent power budgets for logarithms and the supported modulus.
No coefficient separation or original A* integral identity is assumed. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZGAbsorption
open PRZZGCoefficient PRZZEulerSubpower
set_option maxHeartbeats 2000000

theorem log_pow_bound (m : ℕ) (β : ℝ) (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x → (Real.log x)^m ≤ C*x^β := by
  by_cases hm : m = 0
  · subst m
    exact ⟨1,by norm_num,fun x hx => by simpa using Real.one_le_rpow hx hβ.le⟩
  have hm0 : (0:ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  let a := β/(m:ℝ)
  have ha : 0 < a := div_pos hβ hm0
  refine ⟨(a⁻¹)^m,pow_pos (inv_pos.mpr ha) m,?_⟩
  intro x hx
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hh := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx0 a)
  rw [Real.log_rpow hx0] at hh
  have hl : Real.log x ≤ x^a/a := (le_div_iff₀ ha).mpr (by nlinarith)
  calc
    _ ≤ (x^a/a)^m := pow_le_pow_left₀ (Real.log_nonneg hx) hl m
    _ = (a⁻¹)^m*x^β := by
      rw [div_eq_mul_inv,mul_pow,← Real.rpow_mul_natCast hx0.le]
      have he : a*(m:ℝ) = β := by dsimp [a]; field_simp
      rw [he,mul_comm]

/-- All constants precede d,n,s,sigma. Logarithmic and modulus losses
are assigned independent positive exponents beta and eta. -/
theorem sourceG_average_power (js : List ℕ) (k : ℕ) (ε η β : ℝ)
    (hε : 0 < ε) (hη : 0 < η) (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (sigma : ℝ) (d n : ℕ),
      sigma ≤ 0 → 1 ≤ d → 1 ≤ n → ∀ s : Finset ℕ,
      (∀ h ∈ s, 1 ≤ h ∧ d*h ≤ n ∧ SmoothMobius.supported d h) →
      (∑ h ∈ s, |sourceG js k sigma d h|/(h:ℝ)^ε) ≤ C*(d:ℝ)^η*(n:ℝ)^β := by
  obtain ⟨C,hC,h⟩ := sourceG_average_subpower ε η hε hη
  obtain ⟨D,hD,hlog⟩ := log_pow_bound (k+degree js) β hβ
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro sigma d n hσ hd hn s hs
  exact (h js k sigma d n hσ hd hn s hs).trans
    ((mul_le_mul_of_nonneg_right (hlog n (by exact_mod_cast hn))
      (mul_nonneg hC.le (Real.rpow_nonneg (by positivity) _))).trans_eq (by ring))

#print axioms log_pow_bound
#print axioms sourceG_average_power

theorem sourceG_seven_power (js : List ℕ) (k : ℕ) (η β : ℝ)
    (hη : 0 < η) (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (sigma : ℝ) (d n : ℕ),
      sigma ≤ 0 → 1 ≤ d → 1 ≤ n → ∀ (s : Finset ℕ) (X A V : ℝ) (E : ℕ → ℝ),
      0 < X → 0 ≤ A → 0 ≤ V →
      (∀ h ∈ s, 1 ≤ h ∧ d*h ≤ n ∧ SmoothMobius.supported d h) →
      (∀ h ∈ s, (X/(h:ℝ))^(1/4:ℝ) ≤ E h ∧ E h ≤ (X/(h:ℝ))^(1/2:ℝ)) →
      (∑ h ∈ s, |sourceG js k sigma d h| * PRZZDISeven.seven h (E h) A (X/h) V) ≤
        PRZZDISeven.envelope X A V*(C*(d:ℝ)^η*(n:ℝ)^β) := by
  obtain ⟨C,hC,h⟩ := sourceG_seven_subpower η hη
  obtain ⟨D,hD,hlog⟩ := log_pow_bound (k+degree js) β hβ
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro sigma d n hσ hd hn s X A V E hX hA hV hs hE
  apply (h js k sigma d n hσ hd hn s X A V E hX hA hV hs hE).trans
  apply mul_le_mul_of_nonneg_left _ (by unfold PRZZDISeven.envelope; positivity)
  exact (mul_le_mul_of_nonneg_right (hlog n (by exact_mod_cast hn))
    (mul_nonneg hC.le (Real.rpow_nonneg (by positivity) _))).trans_eq (by ring)

#print axioms sourceG_seven_power
end XiPrime8845.PRZZGAbsorption
