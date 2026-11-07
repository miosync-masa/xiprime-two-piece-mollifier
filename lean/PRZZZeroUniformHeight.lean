import PRZZZeroSourceHeight

/-! Uniform shift constants for the ACTUAL zero-frequency time kernel.
All derivative constants precede height, gap and spatial scales. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZZeroUniformHeight
open PRZZZeroGap PRZZTimeAmplitude PRZZCentralFubini
set_option maxHeartbeats 6000000

theorem core_decay_explicit (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hcPhi : HasCompactSupport Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ U V : ℕ → ℝ, (∀ n, 0 ≤ U n ∧ 0 ≤ V n) ∧
      ∀ (n : ℕ) (sigma : ℂ) (T u delta x : ℝ),
      sigma ≠ 0 → 0 < T → 0 < u → delta ≠ 0 → 0 < x →
      ‖core Phi T u sigma delta x‖ ≤
        x^(-(sigma.re+1))*(U n+V n/‖sigma‖^2)*((2*Real.pi*u*x^2)/(2*T))^(-a)*
          T/T^n*(u*x)^n/|delta|^n := by
  obtain ⟨C,D,E,hpos,hm⟩ := mass Phi hPhi hcPhi a ha
  let U := fun n => PRZZFullWeightJets.convolution C D n
  let V := fun n => PRZZFullWeightJets.convolution C E n
  have hU (n : ℕ) : 0 ≤ U n := by
    unfold U PRZZFullWeightJets.convolution
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hpos i).1) (hpos (n-i)).2.1
  have hV (n : ℕ) : 0 ≤ V n := by
    unfold V PRZZFullWeightJets.convolution
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hpos i).1) (hpos (n-i)).2.2
  refine ⟨U,V,fun n => ⟨hU n,hV n⟩,?_⟩
  intro n sigma T u delta x hs hT hu hd hx
  have hk : 0 < 2*Real.pi*u*x^2 := by positivity
  have ho : delta/(u*x) ≠ 0 := div_ne_zero hd (by positivity)
  have hb := PRZZDeltaDecay.oscillatory_bound (amplitude Phi T (2*Real.pi*u*x^2) sigma)
    (smooth Phi hPhi hsPhi T _ sigma hT hk hs) (compact Phi hsPhi T _ sigma hT)
    n (delta/(u*x)) ho
  rw [mass_window Phi hsPhi T _ sigma hT n] at hb
  have hm' := hm n T (2*Real.pi*u*x^2) sigma hT hk hs
  have he : PRZZFullWeightJets.convolution C (fun i => D i+E i/‖sigma‖^2) n =
      U n+V n/‖sigma‖^2 := by
    unfold U V PRZZFullWeightJets.convolution
    rw [Finset.sum_div,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he] at hm'
  have hh := hb.trans (div_le_div_of_nonneg_right hm' (by positivity))
  change _ ≤ (U n+V n/‖sigma‖^2)*((2*Real.pi*u*x^2)/(2*T))^(-a)*T/T^n/|delta/(u*x)|^n at hh
  rw [core,norm_mul,power_norm sigma x hx]
  apply (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq
  rw [abs_div,abs_of_pos (mul_pos hu hx),div_pow]
  field_simp

/-- Explicit logarithmic-shift uniformity for every derivative order.
The entire singular factor is displayed rather than selected after T. -/
theorem core_decay_scaled (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hcPhi : HasCompactSupport Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (a r : ℝ) (ha : 0 < a) (hr : 0 < r) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧ ∀ (n : ℕ) (A B : ℂ) (L T u delta x : ℝ),
      L ≠ 0 → r ≤ ‖A+B‖ → 0 < T → 0 < u → delta ≠ 0 → 0 < x →
      let sigma := (A+B)/(L:ℂ)
      ‖core Phi T u sigma delta x‖ ≤
        x^(-(sigma.re+1))*(C n*(1+L^2/r^2))*((2*Real.pi*u*x^2)/(2*T))^(-a)*
          T/T^n*(u*x)^n/|delta|^n := by
  obtain ⟨U,V,hpos,h⟩ := core_decay_explicit Phi hPhi hcPhi hsPhi a ha
  refine ⟨fun n => U n+V n,fun n => add_nonneg (hpos n).1 (hpos n).2,?_⟩
  intro n A B L T u delta x hL hsep hT hu hd hx
  have hs : (A+B)/(L:ℂ) ≠ 0 := div_ne_zero
    (norm_pos_iff.mp (hr.trans_le hsep)) (by exact_mod_cast hL)
  have hh := h n _ T u delta x hs hT hu hd hx
  have he : V n/‖(A+B)/(L:ℂ)‖^2 = V n*L^2/‖A+B‖^2 := by
    rw [norm_div,div_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    field_simp
  rw [he] at hh
  have hb : U n+V n*L^2/‖A+B‖^2 ≤ (U n+V n)*(1+L^2/r^2) := by
    have hp : V n*L^2/‖A+B‖^2 ≤ V n*L^2/r^2 := by
      have hv := (hpos n).2
      gcongr
    have hu0 := (hpos n).1
    have hv0 := (hpos n).2
    have hq : 0 ≤ L^2/r^2 := div_nonneg (sq_nonneg L) (sq_nonneg r)
    have hp' : V n*L^2/‖A+B‖^2 ≤ V n*(L^2/r^2) := hp.trans_eq (by ring)
    nlinarith [mul_nonneg hu0 hq]
  apply hh.trans
  gcongr

theorem actual_row_gain_uniform (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hcPhi : HasCompactSupport Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (a r : ℝ) (ha : 0 < a) (hr : 0 < r) :
    ∃ U : ℕ → ℝ, (∀ n, 0 ≤ U n) ∧
      ∀ (n : ℕ) (F : ℝ → ℂ) (T M Q d u v delta x eps L : ℝ) (A B : ℂ),
      Function.support F ⊆ Icc (1/2:ℝ) 3 → L ≠ 0 → r ≤ ‖A+B‖ →
      0 < T → 0 < M → 0 < Q → 0 < d → 0 < u → 0 < v → 0 < x → d*u ≤ Q →
      PRZZSourceCutoffs.deltaCutoff T M Q eps/d ≤ |delta| →
      let sigma := (A+B)/(L:ℂ)
      ‖∫ t : ℝ, kernel F Phi (M/v) (u*v) delta T 0 (sigma+1) sigma x t‖ ≤
        ‖F ((M/v)⁻¹*x)‖*(x^(-(sigma.re+1))*(U (n+2)*(1+L^2/r^2))*
          ((2*Real.pi*(u*v)*x^2)/(2*T))^(-a)*T/T^2*(u*v*x)^2/|delta|^2*
            (3*T^(-eps))^n) := by
  obtain ⟨U,hU,hb⟩ := core_decay_scaled Phi hPhi hcPhi hsPhi a r ha hr
  refine ⟨U,hU,?_⟩
  intro n F T M Q d u v delta x eps L A B hF hL hsep hT hM hQ hd hu hv hx huQ hgap
  let sigma := (A+B)/(L:ℂ)
  dsimp only
  have hs : sigma ≠ 0 := div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep)) (by exact_mod_cast hL)
  have hUn := hU (n+2)
  have hc : 0 < PRZZSourceCutoffs.deltaCutoff T M Q eps/d := by
    unfold PRZZSourceCutoffs.deltaCutoff; positivity
  have hd0 : delta ≠ 0 := abs_pos.mp (hc.trans_le hgap)
  rw [kernel_time,norm_mul]
  by_cases hz : F ((M/v)⁻¹*x) = 0
  · rw [hz,norm_zero,zero_mul,zero_mul]
  have hxM : x ≤ 3*(M/v) := (div_le_iff₀ (div_pos hM hv)).mp (by
    simpa only [div_eq_mul_inv,mul_comm] using (hF hz).2)
  have hp := PRZZZeroSourceHeight.source_phase_scale T M Q d u v delta x eps hT hM hQ hd hu hv hx huQ hxM hgap
  have hcore := hb (n+2) A B L T (u*v) delta x hL hsep hT (mul_pos hu hv) hd0 hx
  dsimp only at hcore
  have he : x^(-(sigma.re+1))*(U (n+2)*(1+L^2/r^2))*
      ((2*Real.pi*(u*v)*x^2)/(2*T))^(-a)*T/T^(n+2)*(u*v*x)^(n+2)/|delta|^(n+2) =
      x^(-(sigma.re+1))*(U (n+2)*(1+L^2/r^2))*
        ((2*Real.pi*(u*v)*x^2)/(2*T))^(-a)*T/T^2*(u*v*x)^2/|delta|^2*
          ((u*v*x)/(|delta| * T))^n := by
    simp only [pow_add,mul_pow,div_pow]
    field_simp
    <;> ring
  rw [he] at hcore
  apply (mul_le_mul_of_nonneg_left hcore (norm_nonneg _)).trans
  gcongr

/-- Derivative order is chosen after the desired polynomial rate but
before height. The explicit logarithmic shift loss is included. -/
theorem source_order_uniform (eps rho rate r : ℝ) (heps : 0 < eps) (hr : 0 < r) :
    ∃ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      (1+(Real.log T)^2/r^2)*T^rho*(3*T^(-eps))^n ≤ C*T^(-rate) := by
  obtain ⟨n,D,hD,h⟩ := PRZZZeroSourceHeight.source_tail_order eps (rho+2) rate heps
  refine ⟨n,(1+1/r^2)*D,by positivity,?_⟩
  intro T hT
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hlog0 := Real.log_nonneg hT
  have hlog : Real.log T ≤ T := by linarith [Real.log_le_sub_one_of_pos hT0]
  have hs : 1+(Real.log T)^2/r^2 ≤ (1+1/r^2)*T^2 := by
    have hsq : (Real.log T)^2 ≤ T^2 := sq_le_sq₀ hlog0 hT0.le |>.mpr hlog
    have hh := div_le_div_of_nonneg_right hsq (sq_nonneg r)
    have h1 : 1 ≤ T^2 := one_le_pow₀ hT
    calc
      _ ≤ T^2+T^2/r^2 := add_le_add h1 hh
      _ = _ := by ring
  calc
    _ ≤ ((1+1/r^2)*T^2)*T^rho*(3*T^(-eps))^n := by gcongr
    _ = (1+1/r^2)*(T^(rho+2)*(3*T^(-eps))^n) := by
      rw [Real.rpow_add hT0,Real.rpow_ofNat]
      ring
    _ ≤ (1+1/r^2)*(D*T^(-rate)) := mul_le_mul_of_nonneg_left (h T hT) (by positivity)
    _ = _ := by ring

#print axioms source_order_uniform
#print axioms actual_row_gain_uniform
#print axioms core_decay_scaled
#print axioms core_decay_explicit
end XiPrime8845.PRZZZeroUniformHeight
