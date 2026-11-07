import PRZZResidueTime

/-! Uniform absorption of the actual noncentral residue budget. The
dual Gamma series and phase/Poisson errors are not discarded. -/
noncomputable section
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZResidueAbsorption
open PRZZResidueTime
set_option maxHeartbeats 3000000

theorem gaussian_budget (k : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ T : ℝ in atTop, C*T^k*Real.exp (-T^2/4) ≤ 1 := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).const_mul C
  have he : ∀ᶠ T : ℝ in atTop, C*(T^k*Real.exp (-T)) < 1 :=
    h.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [he,eventually_ge_atTop (4:ℝ)] with T he hT
  apply le_trans _ he.le
  calc
    _ ≤ C*T^k*Real.exp (-T) := by gcongr; nlinarith
    _ = _ := by ring

/-- Includes the literal coefficient mass. The threshold precedes both
shifts and N; no residue bound or singular-factor bound is assumed. -/
theorem scalar_absorbed (m : ℕ) (r : ℝ) (hr : 0 < r) :
    ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ, r ≤ ‖A+B‖ → ∀ N : ℕ,
      1 ≤ N → (N:ℝ) ≤ T →
      (4*(N:ℝ)*(Real.log N)^m)*
        timeCost (A/(Real.log T:ℂ)+B/(Real.log T:ℂ)) T ≤ 1 := by
  have h := gaussian_budget (m+7) (1680*(1+64/r^2)) (by positivity)
  filter_upwards [h,eventually_ge_atTop (2:ℝ)] with T h hT
  intro A B hsep N hN hNT
  have hT0 : 0 < T := by linarith
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hln : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg hN1
  have hlog : Real.log (N:ℝ) ≤ T :=
    (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hL : 0 < Real.log T := Real.log_pos (by linarith)
  have hLT : Real.log T ≤ T :=
    (Real.log_le_sub_one_of_pos hT0).trans (by linarith)
  have he : 64*T^2/‖A/(Real.log T:ℂ)+B/(Real.log T:ℂ)‖^2 =
      64*T^2*(Real.log T)^2/‖A+B‖^2 := by
    rw [← add_div,norm_div,div_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    field_simp
  have hs : 1+64*T^2/‖A/(Real.log T:ℂ)+B/(Real.log T:ℂ)‖^2 ≤
      (1+64/r^2)*T^4 := by
    rw [he]
    have h1 : (1:ℝ) ≤ T^4 := one_le_pow₀ (by linarith)
    calc
      _ ≤ T^4+64*T^2*T^2/r^2 := by gcongr
      _ = _ := by ring
  apply le_trans _ h
  unfold timeCost
  have hm : 4*(N:ℝ)*(Real.log N)^m ≤ 4*T*T^m := by gcongr
  have hb := mul_le_mul hm hs (by positivity : 0 ≤ 1+64*T^2/‖A/(Real.log T:ℂ)+B/(Real.log T:ℂ)‖^2)
    (by positivity : 0 ≤ 4*T*T^m)
  have hb' := mul_le_mul_of_nonneg_right hb
    (show 0 ≤ 420*T^2*Real.exp (-T^2/4) by positivity)
  calc
    _ ≤ (4*T*T^m)*((1+64/r^2)*T^4*(420*T^2)*Real.exp (-T^2/4)) := by
      convert hb' using 1 <;> first | rfl | ring
    _ = _ := by rw [pow_add]; ring

/-- The main V-W error and all noncentral residues now share the sharp
target. This is still a difference of two error integrals, not a claim
that the dual, phase and Poisson remainders have already been bounded. -/
theorem combined_target (js : List ℕ) (S r delta : ℝ) (hr : 0 < r) (hd : 0 < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ → ∀ N : ℕ, 1 ≤ N → (N:ℝ) ≤ T →
      ∀ (phi : ℝ → ℂ) (P : ℝ), Continuous phi → 0 ≤ P →
      (∀ t ∈ Icc T (2*T), ‖phi t‖ ≤ P) →
      let a := A/(Real.log T:ℂ)
      let b := B/(Real.log T:ℂ)
      let w := PRZZMollifiedTime.mollifierWeight phi
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) N
      ‖(∫ t in Icc T (2*T), w t*PRZZReplacementIntegral.difference a b t) -
        (∫ t in Icc T (2*T), w t*PRZZContourAFE.noncentralSum a b t)‖ ≤
        C*P*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,R,hC,hR,h⟩ := scaled_combined_explicit js S r delta hr hd
  refine ⟨C+R,by positivity,?_⟩
  filter_upwards [h,scalar_absorbed (2*PRZZGCoefficient.degree js) r hr,
    eventually_ge_atTop (1:ℝ)] with T h hs hT
  intro A B hA hB hsep N hN hNT phi P hphi hP hp
  have hb := hs A B hsep N hN hNT
  have hh := h A B hA hB hsep N hN hNT phi P hphi hP hp
  have ht : 1 ≤ T^delta := Real.one_le_rpow hT hd.le
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hn7 : (1:ℝ) ≤ (N:ℝ)^(7/4:ℝ) := Real.one_le_rpow hn (by norm_num)
  have htar : 1 ≤ PRZZOptimalPowers.target N T := by
    unfold PRZZOptimalPowers.target
    have hz : 0 ≤ T^(1/2:ℝ)*(N:ℝ)^(7/8:ℝ) := by positivity
    linarith
  have he := mul_le_mul_of_nonneg_left hb (show 0 ≤ R*P by positivity)
  have he2 := mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le ht htar)
    (show 0 ≤ R*P by positivity)
  nlinarith

#print axioms gaussian_budget
#print axioms scalar_absorbed
#print axioms combined_target
end XiPrime8845.PRZZResidueAbsorption
