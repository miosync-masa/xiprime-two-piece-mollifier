import PRZZZeroNativeTail

/-! Quantitative spatial boundary suppliers for the ACTUAL zero core.
Near zero, time oscillation is used before taking the spatial norm.
These are height-uniform bounds, not fixed-height exhaustion limits. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZZeroBoundaryHeight
open PRZZZeroGap PRZZZeroSpatialHeight
set_option maxHeartbeats 7000000

theorem phase_envelope (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hcPhi : HasCompactSupport Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (r : ℝ) (hr : 0 < r) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ (n : ℕ) (T p delta x L g : ℝ) (A B : ℂ),
      L ≠ 0 → r ≤ ‖A+B‖ → ‖(A+B)/(L:ℂ)‖ ≤ 1/8 →
      1 ≤ T → 1 ≤ p → p ≤ T^2 → delta ≠ 0 → 0 < x → 0 ≤ g →
      p*x/(|delta| *T) ≤ g →
      let sigma := (A+B)/(L:ℂ)
      ‖core Phi T p sigma delta x‖ ≤
        C n*(1+L^2/r^2)*T^5*g^n*envelope x/|delta|^2 := by
  obtain ⟨U,hU,hu⟩ := PRZZZeroUniformHeight.core_decay_scaled Phi hPhi hcPhi hsPhi (1/4) r (by norm_num) hr
  obtain ⟨V,hV,hv⟩ := PRZZZeroUniformHeight.core_decay_scaled Phi hPhi hcPhi hsPhi 2 r (by norm_num) hr
  refine ⟨fun n => U (n+2)+V (n+2),fun n => add_nonneg (hU _) (hV _),?_⟩
  intro n T p delta x L g A B hL hsep hn hT hp hpT hd hx hg hphase
  let sigma := (A+B)/(L:ℂ)
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have henv := envelope_nonneg x
  have hUn := hU (n+2)
  have hVn := hV (n+2)
  have hs := abs_le.mp ((Complex.abs_re_le_norm sigma).trans hn)
  have bound (a Z : ℝ) (hZ : 0 ≤ Z) (hZU : Z ≤ U (n+2)+V (n+2))
      (ha : 0 ≤ a) (ha2 : a ≤ 2) (he : x^(1-sigma.re-2*a) ≤ envelope x)
      (hh : ‖core Phi T p sigma delta x‖ ≤
        x^(-(sigma.re+1))*(Z*(1+L^2/r^2))*((2*Real.pi*p*x^2)/(2*T))^(-a)*
          T/T^(n+2)*(p*x)^(n+2)/|delta|^(n+2)) :
      ‖core Phi T p sigma delta x‖ ≤
        (U (n+2)+V (n+2))*(1+L^2/r^2)*T^5*g^n*envelope x/|delta|^2 := by
    have hrb : x^(-(sigma.re+1))*(Z*(1+L^2/r^2))*((2*Real.pi*p*x^2)/(2*T))^(-a)*
        T/T^(n+2)*(p*x)^(n+2)/|delta|^(n+2) =
        (x^(-(sigma.re+1))*(Z*(1+L^2/r^2))*((2*Real.pi*p*x^2)/(2*T))^(-a)*
          T/T^2*(p*x)^2)*(p*x/(|delta| *T))^n/|delta|^2 := by
      simp only [pow_add,mul_pow,div_pow]
      field_simp
      <;> ring
    rw [hrb,normalize sigma a T p x _ hx hT0 hp0] at hh
    apply hh.trans
    calc
      _ ≤ ((Z*(1+L^2/r^2))*T^5*envelope x)*g^n/|delta|^2 := by
        gcongr
        exact scale_cap a T p ha ha2 hT hp hpT
      _ = Z*(1+L^2/r^2)*T^5*g^n*envelope x/|delta|^2 := by ring
      _ ≤ _ := by gcongr
  by_cases hxl : x ≤ 1
  · apply bound (1/4) (U (n+2)) (hU _) (le_add_of_nonneg_right (hV _))
      (by norm_num) (by norm_num) _
      (hu (n+2) A B L T p delta x hL hsep hT0 hp0 hd hx)
    rw [envelope,if_pos hxl]
    exact Real.rpow_le_one hx.le hxl (by linarith [hs.2])
  · apply bound 2 (V (n+2)) (hV _) (le_add_of_nonneg_left (hU _))
      (by norm_num) le_rfl _
      (hv (n+2) A B L T p delta x hL hsep hT0 hp0 hd hx)
    rw [envelope,if_neg hxl]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [hs.1])

/-- All nonzero low-spatial-boundary values supply the phase condition.
The physical argument is v*x, not x and not the original M. -/
theorem lower_geometry (P : ℝ → ℝ) (hright : ∀ y, 1 ≤ y → P y = 0)
    (T u v x theta : ℝ) (hu : 0 ≤ u) (huT : u ≤ T^theta)
    (hP : P (v*x) ≠ 0) : u*v*x ≤ T^theta := by
  have hx : v*x < 1 := by
    by_contra h
    exact hP (hright _ (le_of_not_gt h))
  nlinarith [mul_le_mul_of_nonneg_left hx.le hu]

theorem lower_core_power (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hcPhi : HasCompactSupport Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (r theta rate : ℝ) (hr : 0 < r) (htheta : theta < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T p delta x : ℝ) (A B : ℂ),
      1 < T → r ≤ ‖A+B‖ → ‖(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 →
      1 ≤ p → p ≤ T^2 → 1 ≤ |delta| → 0 < x → p*x ≤ T^theta →
      ‖core Phi T p ((A+B)/(Real.log T:ℂ)) delta x‖ ≤
        C*T^(-rate)*envelope x/|delta|^2 := by
  obtain ⟨C,hC,hb⟩ := phase_envelope Phi hPhi hcPhi hsPhi r hr
  obtain ⟨n,D,hD,hh⟩ := PRZZZeroUniformHeight.source_order_uniform (1-theta) 5 rate r (by linarith) hr
  have hCn := hC n
  refine ⟨C n*D+1,by positivity,?_⟩
  intro T p delta x A B hT hsep hn hp hpT hd hx hpx
  have hT0 : 0 < T := by linarith
  have hd0 : delta ≠ 0 := abs_pos.mp (by linarith)
  have hphase : p*x/(|delta| *T) ≤ 3*T^(-(1-theta)) := by
    calc
      _ ≤ T^theta/(1*T) := by gcongr
      _ = T^(-(1-theta)) := by
        rw [one_mul,Real.rpow_neg hT0.le,Real.rpow_sub hT0,Real.rpow_one]
        field_simp
      _ ≤ _ := by nlinarith [Real.rpow_nonneg hT0.le (-(1-theta))]
  have hb' := hb n T p delta x (Real.log T) (3*T^(-(1-theta))) A B
    (Real.log_pos hT).ne' hsep hn hT.le hp hpT hd0 hx (by positivity) hphase
  dsimp only at hb'
  have hh' := mul_le_mul_of_nonneg_left (hh T hT.le) hCn
  rw [Real.rpow_ofNat] at hh'
  have hfac : C n*(1+(Real.log T)^2/r^2)*T^5*(3*T^(-(1-theta)))^n ≤
      (C n*D+1)*T^(-rate) := by
    nlinarith [Real.rpow_nonneg hT0.le (-rate)]
  exact hb'.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hfac (envelope_nonneg x)) (sq_nonneg _))

/-- The original upper boundary is measured before the x=m/v change.
No comparison between the original M and the normalized M/v is omitted. -/
theorem upper_geometry (P : ℝ → ℝ) (hleft : ∀ y ≤ (1/2:ℝ), P y = 1)
    (T R v x : ℝ) (hT : 4 ≤ T) (hR : T^4/2 ≤ R) (hv : 0 < v)
    (hvT : v ≤ T) (hx : 0 < x) (hP : 1-P (v*x/R) ≠ 0) : T^2 ≤ x := by
  have hT0 : 0 < T := by linarith
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR
  have harg : 1/2 < v*x/R := by
    by_contra h
    exact hP (by rw [hleft _ (le_of_not_gt h)]; ring)
  have hmul : R/2 < v*x := by linarith [(lt_div_iff₀ hR0).mp harg]
  have hhigh : T^4/4 ≤ v*x := by linarith
  have hscale : 4*T^2 ≤ T^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hT) (sq_nonneg T)]
  have hscale' : 4*T^3 ≤ T^4 := by nlinarith [mul_le_mul_of_nonneg_right hscale hT0.le]
  have hvx := mul_le_mul_of_nonneg_right hvT hx.le
  nlinarith

theorem upper_core_power (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hcPhi : HasCompactSupport Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (r rate : ℝ) (hr : 0 < r) (hrate : 0 ≤ rate) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T p delta x : ℝ) (A B : ℂ),
      1 < T → r ≤ ‖A+B‖ → ‖(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 →
      1 ≤ p → p ≤ T^2 → delta ≠ 0 → T^2 ≤ x →
      ‖core Phi T p ((A+B)/(Real.log T:ℂ)) delta x‖ ≤
        C*T^(-rate)*envelope x/|delta|^2 := by
  let H := rate+7
  have hH : 0 ≤ H := by dsimp [H]; linarith
  obtain ⟨U,hU,hb⟩ := PRZZZeroUniformHeight.core_decay_scaled Phi hPhi hcPhi hsPhi (H+2) r (by linarith) hr
  have hU2 := hU 2
  refine ⟨U 2*(1+1/r^2)+1,by positivity,?_⟩
  intro T p delta x A B hT hsep hn hp hpT hd hxx
  let sigma := (A+B)/(Real.log T:ℂ)
  let q := (2*Real.pi*p*x^2)/(2*T)
  have hT0 : 0 < T := by linarith
  have hp0 : 0 < p := by linarith
  have hT1 : T ≤ T^2 := by nlinarith
  have hx : 0 < x := hT0.trans_le (hT1.trans hxx)
  have hx1 : 1 ≤ x := by linarith
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hqT : T ≤ q := by
    have hpi : 1 ≤ Real.pi*p := by nlinarith [Real.pi_gt_three]
    have hsq : T^2 ≤ x^2 := sq_le_sq₀ hT0.le hx.le |>.mpr (hT1.trans hxx)
    dsimp [q]
    apply (le_div_iff₀ (by positivity : 0 < 2*T)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hpi (sq_nonneg x)]
  have hs := abs_le.mp ((Complex.abs_re_le_norm sigma).trans hn)
  have he : x^(1-sigma.re-2*(2:ℝ)) ≤ envelope x := by
    have hh := Real.rpow_le_rpow_of_exponent_le hx1 (show 1-sigma.re-2*(2:ℝ) ≤ -2 by linarith [hs.1])
    by_cases hxle : x ≤ 1
    · have hxEq : x = 1 := le_antisymm hxle hx1
      simp [hxEq,envelope]
    · simpa only [envelope,if_neg hxle] using hh
  have hSing : 1+(Real.log T)^2/r^2 ≤ (1+1/r^2)*T^2 := by
    have hl : 0 ≤ Real.log T := Real.log_nonneg hT.le
    have hlT : Real.log T ≤ T := by linarith [Real.log_le_sub_one_of_pos hT0]
    have hl2 := (sq_le_sq₀ hl hT0.le).mpr hlT
    have hh := div_le_div_of_nonneg_right hl2 (sq_nonneg r)
    have h1 : 1 ≤ T^2 := one_le_pow₀ hT.le
    calc
      _ ≤ T^2+T^2/r^2 := add_le_add h1 hh
      _ = _ := by ring
  have hh := hb 2 A B (Real.log T) T p delta x (Real.log_pos hT).ne' hsep hT0 hp0 hd hx
  dsimp only at hh
  change _ ≤ x^(-(sigma.re+1))*(U 2*(1+(Real.log T)^2/r^2))*q^(-(H+2))*T/T^2*(p*x)^2/|delta|^2 at hh
  rw [show -(H+2) = (-2:ℝ)+(-H) by ring,Real.rpow_add hq0] at hh
  have hre : x^(-(sigma.re+1))*(U 2*(1+(Real.log T)^2/r^2))*(q^(-2:ℝ)*q^(-H))*T/T^2*(p*x)^2/|delta|^2 =
      (x^(-(sigma.re+1))*(U 2*(1+(Real.log T)^2/r^2))*q^(-2:ℝ)*T/T^2*(p*x)^2)*q^(-H)/|delta|^2 := by ring
  rw [hre] at hh
  have hnrm := normalize sigma 2 T p x (U 2*(1+(Real.log T)^2/r^2)) hx hT0 hp0
  change _ = (U 2*(1+(Real.log T)^2/r^2))*((Real.pi*p/T)^(-2:ℝ)*T/T^2*p^2)*x^(1-sigma.re-2*(2:ℝ)) at hnrm
  rw [hnrm] at hh
  have hqcap : q^(-H) ≤ T^(-H) := Real.rpow_le_rpow_of_nonpos hT0 hqT (by linarith)
  have henv := envelope_nonneg x
  have ht : T^2*T^5*T^(-H) = T^(-rate) := by
    rw [← pow_add,← Real.rpow_natCast T 7,← Real.rpow_add hT0]
    congr 1
    dsimp [H]
    ring
  apply hh.trans
  calc
    _ ≤ (U 2*((1+1/r^2)*T^2))*T^5*envelope x*T^(-H)/|delta|^2 := by
      gcongr
      exact scale_cap 2 T p (by norm_num) le_rfl hT.le hp hpT
    _ = (U 2*(1+1/r^2))*T^(-rate)*envelope x/|delta|^2 := by
      rw [← ht]
      ring
    _ ≤ _ := by gcongr; linarith

theorem lower_integral (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hcPhi : HasCompactSupport Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (r theta rate : ℝ) (hr : 0 < r) (htheta : theta < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ℝ → ℝ) (T u v delta : ℝ) (A B : ℂ),
      (∀ y, 0 ≤ P y) → (∀ y, P y ≤ 1) → (∀ y, 1 ≤ y → P y = 0) →
      1 < T → r ≤ ‖A+B‖ → ‖(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 →
      0 ≤ u → u ≤ T^theta → 1 ≤ u*v → u*v ≤ T^2 → 1 ≤ |delta| →
      ‖∫ x in Ioi (0:ℝ), (P (v*x):ℂ)*core Phi T (u*v) ((A+B)/(Real.log T:ℂ)) delta x‖ ≤
        C*T^(-rate)/|delta|^2 := by
  obtain ⟨C,hC,hb⟩ := lower_core_power Phi hPhi hcPhi hsPhi r theta rate hr htheta
  let J := ∫ x in Ioi (0:ℝ), envelope x
  have hJ : 0 ≤ J := integral_nonneg (fun x => envelope_nonneg x)
  refine ⟨C*J+1,by positivity,?_⟩
  intro P T u v delta A B hlo hhi hright hT hsep hn hu huT hp hpT hd
  let K := C*T^(-rate)/|delta|^2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hg : IntegrableOn (fun x => K*envelope x) (Ioi (0:ℝ)) := envelope_integrable.const_mul K
  apply (norm_integral_le_integral_norm _).trans
  have hh := integral_mono_of_nonneg
    (f := fun x : ℝ => ‖(P (v*x):ℂ)*core Phi T (u*v) ((A+B)/(Real.log T:ℂ)) delta x‖)
    (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) hg (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    by_cases hz : P (v*x) = 0
    · simp only [hz,Complex.ofReal_zero,zero_mul,norm_zero]
      exact mul_nonneg hK (envelope_nonneg x)
    have hb' := hb T (u*v) delta x A B hT hsep hn hp hpT hd hx
      (lower_geometry P hright T u v x theta hu huT hz)
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hlo _)]
    have hnorm := (mul_le_mul_of_nonneg_right (hhi (v*x)) (norm_nonneg
      (core Phi T (u*v) ((A+B)/(Real.log T:ℂ)) delta x))).trans_eq (one_mul _)
    exact (hnorm.trans hb').trans_eq (by dsimp [K] <;> ring))
  apply hh.trans
  rw [integral_const_mul]
  dsimp [K,J]
  have ht : 0 ≤ T^(-rate)/|delta|^2 := by positivity
  ring_nf at ht ⊢
  linarith only [ht]

theorem upper_integral (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hcPhi : HasCompactSupport Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (r rate : ℝ) (hr : 0 < r) (hrate : 0 ≤ rate) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ℝ → ℝ) (T R u v delta : ℝ) (A B : ℂ),
      (∀ y, 0 ≤ P y) → (∀ y, P y ≤ 1) → (∀ y ≤ (1/2:ℝ), P y = 1) →
      4 ≤ T → r ≤ ‖A+B‖ → ‖(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 →
      T^4/2 ≤ R → 0 < v → v ≤ T → 1 ≤ u*v → u*v ≤ T^2 → delta ≠ 0 →
      ‖∫ x in Ioi (0:ℝ), ((1-P (v*x/R):ℝ):ℂ)*
        core Phi T (u*v) ((A+B)/(Real.log T:ℂ)) delta x‖ ≤ C*T^(-rate)/|delta|^2 := by
  obtain ⟨C,hC,hb⟩ := upper_core_power Phi hPhi hcPhi hsPhi r rate hr hrate
  let J := ∫ x in Ioi (0:ℝ), envelope x
  have hJ : 0 ≤ J := integral_nonneg (fun x => envelope_nonneg x)
  refine ⟨C*J+1,by positivity,?_⟩
  intro P T R u v delta A B hlo hhi hleft hT hsep hn hR hv hvT hp hpT hd
  let K := C*T^(-rate)/|delta|^2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hg : IntegrableOn (fun x => K*envelope x) (Ioi (0:ℝ)) := envelope_integrable.const_mul K
  apply (norm_integral_le_integral_norm _).trans
  have hh := integral_mono_of_nonneg
    (f := fun x : ℝ => ‖((1-P (v*x/R):ℝ):ℂ)*core Phi T (u*v) ((A+B)/(Real.log T:ℂ)) delta x‖)
    (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) hg (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    by_cases hz : 1-P (v*x/R) = 0
    · simp only [hz,Complex.ofReal_zero,zero_mul,norm_zero]
      exact mul_nonneg hK (envelope_nonneg x)
    have hb' := hb T (u*v) delta x A B (by linarith) hsep hn hp hpT hd
      (upper_geometry P hleft T R v x hT hR hv hvT hx hz)
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (hhi _))]
    have hcap : 1-P (v*x/R) ≤ 1 := by linarith [hlo (v*x/R)]
    have hnorm := (mul_le_mul_of_nonneg_right hcap (norm_nonneg
      (core Phi T (u*v) ((A+B)/(Real.log T:ℂ)) delta x))).trans_eq (one_mul _)
    exact (hnorm.trans hb').trans_eq (by dsimp [K] <;> ring))
  apply hh.trans
  rw [integral_const_mul]
  dsimp [K,J]
  have ht : 0 ≤ T^(-rate)/|delta|^2 := by positivity
  ring_nf at ht ⊢
  linarith only [ht]

#print axioms lower_integral
#print axioms upper_integral
#print axioms upper_geometry
#print axioms upper_core_power
#print axioms phase_envelope
#print axioms lower_geometry
#print axioms lower_core_power
end XiPrime8845.PRZZZeroBoundaryHeight
