import PRZZWeilDIZeroJoin

/-! Supply the real scaled time mass and absorb the actual Gamma-defect
budget, including coefficient and shift logarithms, into the PRZZ target. -/
noncomputable section
open scoped ContDiff
open Complex MeasureTheory Set
namespace XiPrime8845.PRZZGammaBudgetAbsorption
open PRZZMellinSeparation
set_option maxHeartbeats 8000000

theorem scaled_time_mass (Phi : ℝ → ℂ) (hPhi : Continuous Phi)
    (hcPhi : HasCompactSupport Phi) (T : ℝ) (hT : 0 < T) :
    (∫ t in Icc T (2*T), ‖scaledCutoff Phi T t‖) ≤ T*(∫ y : ℝ, ‖Phi y‖) := by
  have hc : HasCompactSupport (scaledCutoff Phi T) := by
    change HasCompactSupport (fun t => Phi (T⁻¹*t))
    exact hcPhi.comp_homeomorph (Homeomorph.mulLeft₀ T⁻¹ (inv_ne_zero hT.ne'))
  have hi : Integrable (fun t => ‖scaledCutoff Phi T t‖) :=
    ((hPhi.comp (continuous_const.mul continuous_id)).integrable_of_hasCompactSupport hc).norm
  apply (setIntegral_le_integral hi (Filter.Eventually.of_forall (fun t => norm_nonneg _))).trans_eq
  have hh := MeasureTheory.Measure.integral_comp_mul_left (fun y : ℝ => ‖Phi y‖) T⁻¹
  simpa only [scaledCutoff,abs_of_pos (inv_pos.mpr hT),inv_inv,abs_of_pos hT,smul_eq_mul] using hh

def gammaBudget (Phi : ℝ → ℂ) (js : List ℕ) (r : ℝ) (N : ℕ) (T : ℝ) : ℝ :=
  (1+16*(Real.log T)^2/r^2)*(N:ℝ)^(1/4:ℝ)*T^(-(9/8:ℝ))*
    (1+Real.log N)^(2*PRZZGCoefficient.degree js+2)*
      (∫ t in Icc T (2*T), ‖scaledCutoff Phi T t‖)

/-- Fixed time-cutoff mass is evaluated before height; all logarithmic
losses are actually absorbed, leaving a negative height power. -/
theorem gamma_budget_power (Phi : ℝ → ℂ) (hPhi : Continuous Phi)
    (hcPhi : HasCompactSupport Phi) (js : List ℕ) (r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (T : ℝ),
      1 ≤ N → (N:ℝ) ≤ T → 1 ≤ Real.log T →
      gammaBudget Phi js r N T ≤ C*(N:ℝ)^(1/4:ℝ)*T^(-(1/16:ℝ)) := by
  let k := 2*PRZZGCoefficient.degree js+2
  obtain ⟨D,hD,hb⟩ := PRZZOptimalOuter.power_log_absorbed (k+2) (-(1/8)) (-(1/16)) (by norm_num)
  let J := ∫ y : ℝ, ‖Phi y‖
  have hJ : 0 ≤ J := integral_nonneg (fun y => norm_nonneg _)
  let c := (1+16/r^2)*(2:ℝ)^k*J
  have hc : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨c*D+1,by positivity,?_⟩
  intro N T hN hNT hlog
  have hNN : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hT : 1 ≤ T := hNN.trans hNT
  have hT0 : 0 < T := by linarith
  have hN0 : (0:ℝ) < N := by linarith
  have hlN : 0 ≤ Real.log N := Real.log_nonneg hNN
  have hlNT : Real.log N ≤ Real.log T := Real.log_le_log hN0 hNT
  have hsing : 1+16*(Real.log T)^2/r^2 ≤ (1+16/r^2)*(Real.log T)^2 := by
    have hs : (1:ℝ) ≤ (Real.log T)^2 := by nlinarith
    calc
      _ = 1+(16/r^2)*(Real.log T)^2 := by ring
      _ ≤ (Real.log T)^2+(16/r^2)*(Real.log T)^2 := add_le_add hs le_rfl
      _ = _ := by ring
  have hpow : (1+Real.log N)^k ≤ (2*Real.log T)^k := by gcongr; linarith
  have hmass := scaled_time_mass Phi hPhi hcPhi T hT0
  have he : gammaBudget Phi js r N T ≤ c*(N:ℝ)^(1/4:ℝ)*(T^(-(1/8:ℝ))*(Real.log T)^(k+2)) := by
    unfold gammaBudget
    change _ ≤ c*(N:ℝ)^(1/4:ℝ)*(T^(-(1/8:ℝ))*(Real.log T)^(k+2))
    calc
      _ ≤ ((1+16/r^2)*(Real.log T)^2)*(N:ℝ)^(1/4:ℝ)*T^(-(9/8:ℝ))*
          (2*Real.log T)^k*(T*J) := by gcongr
      _ = _ := by
        rw [mul_pow,pow_add]
        have ht : T^(-(9/8:ℝ))*T = T^(-(1/8:ℝ)) := by
          calc
            _ = T^(-(9/8:ℝ))*T^(1:ℝ) := by rw [Real.rpow_one]
            _ = T^(-(9/8:ℝ)+1) := (Real.rpow_add hT0 _ _).symm
            _ = _ := by norm_num
        rw [← ht]
        dsimp [c]
        ring
  have hh := mul_le_mul_of_nonneg_left (hb T hT) (show 0 ≤ c*(N:ℝ)^(1/4:ℝ) by positivity)
  have ht : 0 ≤ (N:ℝ)^(1/4:ℝ)*T^(-(1/16:ℝ)) := by positivity
  nlinarith only [he,hh,ht]

theorem gamma_budget_target (Phi : ℝ → ℂ) (hPhi : Continuous Phi)
    (hcPhi : HasCompactSupport Phi) (js : List ℕ) (r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (T : ℝ),
      1 ≤ N → (N:ℝ) ≤ T → 1 ≤ Real.log T →
      gammaBudget Phi js r N T ≤ C*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,hb⟩ := gamma_budget_power Phi hPhi hcPhi js r hr
  refine ⟨C,hC,?_⟩
  intro N T hN hNT hlog
  have hNN : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hT : 1 ≤ T := hNN.trans hNT
  have hn : (N:ℝ)^(1/4:ℝ) ≤ (N:ℝ)^(7/4:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hNN (by norm_num)
  have ht : T^(-(1/16:ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hT (by norm_num)
  apply (hb N T hN hNT hlog).trans
  unfold PRZZOptimalPowers.target
  have hother : 0 ≤ T^(1/2:ℝ)*(N:ℝ)^(7/8:ℝ) := by positivity
  calc
    _ ≤ C*(N:ℝ)^(1/4:ℝ)*1 := by gcongr
    _ ≤ _ := by nlinarith

#print axioms scaled_time_mass
#print axioms gamma_budget_power
#print axioms gamma_budget_target
end XiPrime8845.PRZZGammaBudgetAbsorption
