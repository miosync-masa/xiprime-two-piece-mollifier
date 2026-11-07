import PRZZZeroUniformHeight
import PRZZZeroGapExchange

/-! Spatial integration of the ACTUAL source-cutoff zero rows.  Constants
precede all scales and shifts.  The polynomial T^5 is deliberately coarse:
arbitrary extra time derivatives pay for it.  This does not identify the
native spatial boundary or the Gamma-weighted dual row with a source row. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZZeroSpatialHeight
open PRZZZeroGap PRZZCentralFubini
set_option maxHeartbeats 6000000

theorem scale_cap (a T p : ℝ) (ha : 0 ≤ a) (ha2 : a ≤ 2)
    (hT : 1 ≤ T) (hp : 1 ≤ p) (hpT : p ≤ T^2) :
    (Real.pi*p/T)^(-a)*T/T^2*p^2 ≤ T^5 := by
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hb : 1/T ≤ Real.pi*p/T := by
    apply div_le_div_of_nonneg_right _ hT0.le
    nlinarith [Real.pi_gt_three]
  have hr : (Real.pi*p/T)^(-a) ≤ T^2 := by
    calc
      _ ≤ (1/T)^(-a) := Real.rpow_le_rpow_of_nonpos (by positivity) hb (by linarith)
      _ = T^a := by rw [one_div,Real.inv_rpow hT0.le,Real.rpow_neg hT0.le]; simp
      _ ≤ T^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le hT ha2
      _ = _ := Real.rpow_two T
  calc
    _ ≤ (T^2)*T/T^2*(T^2)^2 := by gcongr
    _ = _ := by field_simp <;> ring

theorem normalize (sigma : ℂ) (a T p x U : ℝ) (hx : 0 < x) (hT : 0 < T)
    (hp : 0 < p) :
    x^(-(sigma.re+1))*U*((2*Real.pi*p*x^2)/(2*T))^(-a)*T/T^2*(p*x)^2 =
      U*((Real.pi*p/T)^(-a)*T/T^2*p^2)*x^(1-sigma.re-2*a) := by
  have he : (2*Real.pi*p*x^2)/(2*T) = (Real.pi*p/T)*x^2 := by ring
  rw [he,Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_natCast x 2,← Real.rpow_mul hx.le]
  rw [show 1-sigma.re-2*a = -(sigma.re+1)+2*(-a)+2 by ring]
  simp only [Real.rpow_add hx,Real.rpow_two]
  ring

/-- The original spatial cutoff remains with its actual value.  Both
ends of the spatial integral share ONE summable envelope. -/
theorem row_envelope (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hcPhi : HasCompactSupport Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (r : ℝ) (hr : 0 < r) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ (n : ℕ) (F : ℝ → ℂ) (T M Q d u v delta x eps L : ℝ) (A B : ℂ),
      Function.support F ⊆ Icc (1/2:ℝ) 3 →
      (∀ y : ℝ, 0 < y → ‖F y‖ ≤ 1) → L ≠ 0 → r ≤ ‖A+B‖ →
      ‖(A+B)/(L:ℂ)‖ ≤ 1/8 → 1 ≤ T →
      0 < M → 0 < Q → 0 < d → 0 < u → 0 < v → 0 < x →
      1 ≤ u*v → u*v ≤ T^2 → d*u ≤ Q →
      PRZZSourceCutoffs.deltaCutoff T M Q eps/d ≤ |delta| →
      let sigma := (A+B)/(L:ℂ)
      ‖∫ t : ℝ, kernel F Phi (M/v) (u*v) delta T 0 (sigma+1) sigma x t‖ ≤
        C n*(1+L^2/r^2)*T^5*(3*T^(-eps))^n*envelope x/|delta|^2 := by
  obtain ⟨U,hU,hu⟩ := PRZZZeroUniformHeight.actual_row_gain_uniform
    Phi hPhi hcPhi hsPhi (1/4) r (by norm_num) hr
  obtain ⟨V,hV,hv⟩ := PRZZZeroUniformHeight.actual_row_gain_uniform
    Phi hPhi hcPhi hsPhi 2 r (by norm_num) hr
  refine ⟨fun n => U (n+2)+V (n+2),fun n => add_nonneg (hU _) (hV _),?_⟩
  intro n F T M Q d u v delta x eps L A B hF hcap hL hsep hn hT hM hQ hd hu0 hv0 hx hp hpT huQ hgap
  let sigma := (A+B)/(L:ℂ)
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hs := abs_le.mp ((Complex.abs_re_le_norm sigma).trans hn)
  have hfc : ‖F ((M/v)⁻¹*x)‖ ≤ 1 := hcap _ (by positivity)
  have henv := envelope_nonneg x
  have bound (a Z : ℝ) (hZ : 0 ≤ Z) (hZU : Z ≤ U (n+2)+V (n+2)) (ha : 0 ≤ a) (ha2 : a ≤ 2)
      (he : x^(1-sigma.re-2*a) ≤ envelope x)
      (hh : ‖∫ t : ℝ, kernel F Phi (M/v) (u*v) delta T 0 (sigma+1) sigma x t‖ ≤
        ‖F ((M/v)⁻¹*x)‖*(x^(-(sigma.re+1))*(Z*(1+L^2/r^2))*
          ((2*Real.pi*(u*v)*x^2)/(2*T))^(-a)*T/T^2*(u*v*x)^2/|delta|^2*
            (3*T^(-eps))^n)) :
      ‖∫ t : ℝ, kernel F Phi (M/v) (u*v) delta T 0 (sigma+1) sigma x t‖ ≤
        (U (n+2)+V (n+2))*(1+L^2/r^2)*T^5*(3*T^(-eps))^n*envelope x/|delta|^2 := by
    have hnrm := normalize sigma a T (u*v) x (Z*(1+L^2/r^2)) hx hT0 (mul_pos hu0 hv0)
    rw [show x^(-(sigma.re+1))*(Z*(1+L^2/r^2))*
        ((2*Real.pi*(u*v)*x^2)/(2*T))^(-a)*T/T^2*(u*v*x)^2/|delta|^2*
        (3*T^(-eps))^n =
        (x^(-(sigma.re+1))*(Z*(1+L^2/r^2))*
          ((2*Real.pi*(u*v)*x^2)/(2*T))^(-a)*T/T^2*(u*v*x)^2)*
          (3*T^(-eps))^n/|delta|^2 by ring,hnrm] at hh
    apply hh.trans
    calc
      _ ≤ 1*((Z*(1+L^2/r^2))*(T^5)*envelope x*(3*T^(-eps))^n/|delta|^2) := by
        gcongr
        exact scale_cap a T (u*v) ha ha2 hT hp hpT
      _ = Z*(1+L^2/r^2)*T^5*(3*T^(-eps))^n*envelope x/|delta|^2 := by ring
      _ ≤ _ := by
        gcongr
  by_cases hxl : x ≤ 1
  · apply bound (1/4) (U (n+2)) (hU _) (le_add_of_nonneg_right (hV _)) (by norm_num) (by norm_num)
      _ (hu n F T M Q d u v delta x eps L A B hF hL hsep hT0 hM hQ hd hu0 hv0 hx huQ hgap)
    rw [envelope,if_pos hxl]
    exact Real.rpow_le_one hx.le hxl (by linarith [hs.2])
  · apply bound 2 (V (n+2)) (hV _) (le_add_of_nonneg_left (hU _)) (by norm_num) le_rfl
      _ (hv n F T M Q d u v delta x eps L A B hF hL hsep hT0 hM hQ hd hu0 hv0 hx huQ hgap)
    rw [envelope,if_neg hxl]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [hs.1])

/-- Space is integrated AFTER time, using the proven common envelope.
No spatial L1 mass or Fubini equality is assumed. -/
theorem row_integral (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hcPhi : HasCompactSupport Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (r : ℝ) (hr : 0 < r) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ (n : ℕ) (F : ℝ → ℂ) (T M Q d u v delta eps L : ℝ) (A B : ℂ),
      Continuous F → Function.support F ⊆ Icc (1/2:ℝ) 3 →
      (∀ y : ℝ, 0 < y → ‖F y‖ ≤ 1) → L ≠ 0 → r ≤ ‖A+B‖ →
      ‖(A+B)/(L:ℂ)‖ ≤ 1/8 → 1 ≤ T →
      0 < M → 0 < Q → 0 < d → 0 < u → 0 < v →
      1 ≤ u*v → u*v ≤ T^2 → d*u ≤ Q →
      PRZZSourceCutoffs.deltaCutoff T M Q eps/d ≤ |delta| →
      let sigma := (A+B)/(L:ℂ)
      ‖∫ x in Ioi (0:ℝ), ∫ t : ℝ,
        kernel F Phi (M/v) (u*v) delta T 0 (sigma+1) sigma x t‖ ≤
        C n*(1+L^2/r^2)*T^5*(3*T^(-eps))^n/|delta|^2 := by
  obtain ⟨C,hC,hb⟩ := row_envelope Phi hPhi hcPhi hsPhi r hr
  let J := ∫ x in Ioi (0:ℝ), envelope x
  have hJ : 0 ≤ J := integral_nonneg (fun x => envelope_nonneg x)
  refine ⟨fun n => C n*J,fun n => mul_nonneg (hC n) hJ,?_⟩
  intro n F T M Q d u v delta eps L A B hFc hF hcap hL hsep hn hT hM hQ hd hu hv hp hpT huQ hgap
  let sigma := (A+B)/(L:ℂ)
  have hs : sigma ≠ 0 := div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep)) (by exact_mod_cast hL)
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hi := (PRZZZeroGapExchange.row_integrable F Phi hFc hPhi.continuous hF hsPhi
    (M/v) T (u*v) sigma delta (by positivity) hT0 (mul_pos hu hv) hs).integrableOn (s := Ioi (0:ℝ))
  let K := C n*(1+L^2/r^2)*T^5*(3*T^(-eps))^n/|delta|^2
  have hm : IntegrableOn (fun x : ℝ => K*envelope x) (Ioi (0:ℝ)) :=
    envelope_integrable.const_mul K
  have he : (fun x : ℝ => ∫ t : ℝ,
      kernel F Phi (M/v) (u*v) delta T 0 (sigma+1) sigma x t) =
      PRZZZeroGapExchange.row F Phi (M/v) T (u*v) sigma delta := by
    funext x
    exact kernel_time F Phi (M/v) T (u*v) delta x sigma
  dsimp only
  rw [he]
  apply (norm_integral_le_integral_norm _).trans
  have hh := integral_mono_ae hi.norm hm (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hh := hb n F T M Q d u v delta x eps L A B hF hcap hL hsep hn hT hM hQ hd hu hv hx hp hpT huQ hgap
    dsimp only at hh
    rw [kernel_time] at hh
    exact hh.trans_eq (by dsimp [K,PRZZZeroGapExchange.row]; ring))
  apply hh.trans_eq
  rw [integral_const_mul]
  dsimp [K,J]
  ring

#print axioms row_integral
#print axioms scale_cap
#print axioms normalize
#print axioms row_envelope
end XiPrime8845.PRZZZeroSpatialHeight
