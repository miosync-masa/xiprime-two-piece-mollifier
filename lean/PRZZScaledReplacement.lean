import PRZZMeanSquare

/-! Uniform logarithmically scaled shifts in the actual V-W replacement.
The fixed separation r is retained; no uniformity at A+B=0 is asserted.
All constants and height thresholds precede A,B,N and the time weight.
This module estimates the replacement error, not all AFE remainders. -/
noncomputable section
open Complex MeasureTheory Set Filter
namespace XiPrime8845.PRZZScaledReplacement
set_option maxHeartbeats 3000000

theorem shifts_eventually (S eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ T : ℝ in atTop, 1 ≤ Real.log T ∧ ∀ A : ℂ, ‖A‖ ≤ S →
      ‖A/(Real.log T:ℂ)‖ ≤ eta := by
  filter_upwards [Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (max 1 (S/eta)))] with T hT
  have hL : 1 ≤ Real.log T := (le_max_left _ _).trans hT
  refine ⟨hL,?_⟩
  intro A hA
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith)]
  apply (div_le_iff₀ (by linarith : 0 < Real.log T)).mpr
  have hh := (div_le_iff₀ heta).mp ((le_max_right _ _).trans hT)
  nlinarith

/-- Absorb the entire scaled singular factor, including its constant term. -/
theorem singular_absorbed (r a delta : ℝ) (hr : 0 < r) (hmargin : a < delta) :
    ∃ D : ℝ, 0 < D ∧ ∀ T : ℝ, 1 ≤ T → 1 ≤ Real.log T →
      ∀ A B : ℂ, r ≤ ‖A+B‖ →
      (1+32/‖A/(Real.log T:ℂ)+B/(Real.log T:ℂ)‖^2)*T^a ≤ D*T^delta := by
  obtain ⟨C,hC,h⟩ := PRZZOptimalOuter.power_log_absorbed 2 a delta hmargin
  refine ⟨(1+32/r^2)*C,by positivity,?_⟩
  intro T hT hL A B hsep
  have hL0 : Real.log T ≠ 0 := by linarith
  have hab : 0 < ‖A+B‖ := hr.trans_le hsep
  have he : 32/‖A/(Real.log T:ℂ)+B/(Real.log T:ℂ)‖^2 =
      32*(Real.log T)^2/‖A+B‖^2 := by
    rw [← add_div,norm_div,div_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    field_simp
  rw [he]
  have hb : 1+32*(Real.log T)^2/‖A+B‖^2 ≤ (1+32/r^2)*(Real.log T)^2 := by
    have hd : 32*(Real.log T)^2/‖A+B‖^2 ≤ 32*(Real.log T)^2/r^2 := by gcongr
    have hl : 1 ≤ (Real.log T)^2 := by nlinarith
    calc
      _ ≤ (Real.log T)^2+32*(Real.log T)^2/r^2 := add_le_add hl hd
      _ = _ := by ring
  calc
    _ ≤ ((1+32/r^2)*(Real.log T)^2)*T^a :=
      mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg (by linarith) _)
    _ = (1+32/r^2)*(T^a*(Real.log T)^2) := by ring
    _ ≤ (1+32/r^2)*(C*T^delta) := mul_le_mul_of_nonneg_left (h T hT) (by positivity)
    _ = _ := by ring

/-- For every positive loss delta, the fixed shift family has one constant
and one threshold. Both internal exponent margins are supplied here. -/
theorem scaled_target (js : List ℕ) (S r delta : ℝ) (hr : 0 < r) (hd : 0 < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ∀ N : ℕ, 1 ≤ N → (N:ℝ) ≤ T →
      ∀ (phi : ℝ → ℂ) (P : ℝ), Continuous phi → 0 ≤ P →
      (∀ t ∈ Icc T (2*T), ‖phi t‖ ≤ P) →
      ‖∫ t in Icc T (2*T), PRZZMollifiedTime.mollifierWeight phi
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) N t *
        PRZZReplacementIntegral.difference (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t‖ ≤
        C*P*T^delta*PRZZOptimalPowers.target N T := by
  let eta : ℝ := min (1/8) (delta/16)
  have he : 0 < eta := lt_min (by norm_num) (by positivity)
  have he8 : eta ≤ 1/8 := min_le_left _ _
  have hed : eta ≤ delta/16 := min_le_right _ _
  obtain ⟨C,hC,h⟩ := PRZZMeanSquare.replacement_target js (1/2-eta) eta (delta/2)
    (by linarith) (by linarith) he (by linarith) (by linarith)
  obtain ⟨D,hD,habs⟩ := singular_absorbed r (delta/2) delta hr (by linarith)
  refine ⟨C*D,by positivity,?_⟩
  filter_upwards [shifts_eventually S eta he, eventually_ge_atTop (256*Real.pi),
    eventually_ge_atTop (128:ℝ)] with T hsmall hT hT'
  intro A B hA hB hsep N hN hNT phi P hphi hP hp
  have ha := hsmall.2 A hA
  have hb := hsmall.2 B hB
  have hla := (abs_le.mp ((Complex.abs_re_le_norm (A/(Real.log T:ℂ))).trans ha)).1
  have hlb := (abs_le.mp ((Complex.abs_re_le_norm (B/(Real.log T:ℂ))).trans hb)).1
  have hab : A+B ≠ 0 := norm_pos_iff.mp (hr.trans_le hsep)
  have hL : (Real.log T:ℂ) ≠ 0 := by exact_mod_cast (show Real.log T ≠ 0 by linarith [hsmall.1])
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]; exact div_ne_zero hab hL
  have hh := h _ _ (by linarith) (by linarith) hs (by linarith) (by linarith)
    T hT hT' N hN hNT phi P hphi hP hp
  have htarg : 0 ≤ PRZZOptimalPowers.target N T := by unfold PRZZOptimalPowers.target; positivity
  have hz := mul_le_mul_of_nonneg_left (habs T (by linarith) hsmall.1 A B hsep)
    (show 0 ≤ C*P*PRZZOptimalPowers.target N T by positivity)
  apply hh.trans
  convert hz using 1 <;> ring

/-- A fixed compact time cutoff supplies its own envelope, uniformly
under t/T rescaling; no time-weight cap remains as an input. -/
theorem cutoff_target (js : List ℕ) (S r delta : ℝ) (hr : 0 < r) (hd : 0 < delta)
    (F : ℝ → ℂ) (hF : Continuous F) (hsF : HasCompactSupport F) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ∀ N : ℕ, 1 ≤ N → (N:ℝ) ≤ T →
      ‖∫ t in Icc T (2*T), PRZZMollifiedTime.mollifierWeight (fun t => F (t/T))
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) N t *
        PRZZReplacementIntegral.difference (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t‖ ≤
        C*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := scaled_target js S r delta hr hd
  obtain ⟨P,hP⟩ := hsF.exists_bound_of_continuous hF
  refine ⟨C*max P 1,mul_pos hC (lt_of_lt_of_le zero_lt_one (le_max_right _ _)),?_⟩
  filter_upwards [h] with T hT
  intro A B hA hB hsep N hN hNT
  exact hT A B hA hB hsep N hN hNT (fun t => F (t/T)) (max P 1)
    (hF.comp (continuous_id.div_const T)) (by positivity)
    (fun t _ => (hP (t/T)).trans (le_max_left _ _))

#print axioms shifts_eventually
#print axioms singular_absorbed
#print axioms scaled_target
#print axioms cutoff_target
end XiPrime8845.PRZZScaledReplacement
