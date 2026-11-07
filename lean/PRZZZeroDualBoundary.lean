import PRZZZeroDualHeight
import PRZZZeroBoundaryHeight
import PRZZZeroBoundarySum

/-! Uniform transfer of the actual Gamma jets to the reflected zero core.
Constants precede height and the bounded logarithmic shift family. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZZeroDualBoundary
open PRZZZeroGap PRZZZeroSpatialHeight
set_option maxHeartbeats 8000000

theorem phase_envelope (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hcPhi : HasCompactSupport Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (S r : ℝ) (hS : 0 ≤ S) (hr : 0 < r) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ, ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖-(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 →
      ∀ (n : ℕ) (p delta x g : ℝ),
      1 ≤ T → 1 ≤ p → p ≤ T^2 → delta ≠ 0 → 0 < x → 0 ≤ g →
      p*x/(|delta| * T) ≤ g →
      let sigma := -(A+B)/(Real.log T:ℂ)
      ‖core (PRZZKeptLiteral.dualProfile Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)))
        T p sigma delta x‖ ≤
        C n*(1+(Real.log T)^2/r^2)*T^5*g^n*envelope x/|delta|^2 := by
  obtain ⟨U,hU,hu⟩ := PRZZZeroDualHeight.core_scaled_uniform Phi hPhi hcPhi hsPhi S r (1/4) hS hr (by norm_num)
  obtain ⟨V,hV,hv⟩ := PRZZZeroDualHeight.core_scaled_uniform Phi hPhi hcPhi hsPhi S r 2 hS hr (by norm_num)
  refine ⟨fun n => U (n+2)+V (n+2),fun n => add_nonneg (hU _) (hV _),?_⟩
  filter_upwards [hu,hv] with T hu hv
  intro A B hA hB hsep hn n p delta x g hT hp hpT hd hx hg hphase
  let sigma := -(A+B)/(Real.log T:ℂ)
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have henv := envelope_nonneg x
  have hUn := hU (n+2)
  have hVn := hV (n+2)
  have hs := abs_le.mp ((Complex.abs_re_le_norm sigma).trans hn)
  have bound (a Z : ℝ) (hZ : 0 ≤ Z) (hZU : Z ≤ U (n+2)+V (n+2))
      (ha : 0 ≤ a) (ha2 : a ≤ 2) (he : x^(1-sigma.re-2*a) ≤ envelope x)
      (hh : ‖core (PRZZKeptLiteral.dualProfile Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) T p sigma delta x‖ ≤
        x^(-(sigma.re+1))*(Z*(1+(Real.log T)^2/r^2))*((2*Real.pi*p*x^2)/(2*T))^(-a)*
          T/T^(n+2)*(p*x)^(n+2)/|delta|^(n+2)) :
      ‖core (PRZZKeptLiteral.dualProfile Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) T p sigma delta x‖ ≤
        (U (n+2)+V (n+2))*(1+(Real.log T)^2/r^2)*T^5*g^n*envelope x/|delta|^2 := by
    have hrb : x^(-(sigma.re+1))*(Z*(1+(Real.log T)^2/r^2))*((2*Real.pi*p*x^2)/(2*T))^(-a)*
        T/T^(n+2)*(p*x)^(n+2)/|delta|^(n+2) =
        (x^(-(sigma.re+1))*(Z*(1+(Real.log T)^2/r^2))*((2*Real.pi*p*x^2)/(2*T))^(-a)*
          T/T^2*(p*x)^2)*(p*x/(|delta| *T))^n/|delta|^2 := by
      simp only [pow_add,mul_pow,div_pow]
      field_simp
      <;> ring
    rw [hrb,normalize sigma a T p x _ hx hT0 hp0] at hh
    apply hh.trans
    calc
      _ ≤ ((Z*(1+(Real.log T)^2/r^2))*T^5*envelope x)*g^n/|delta|^2 := by
        gcongr
        exact scale_cap a T p ha ha2 hT hp hpT
      _ = Z*(1+(Real.log T)^2/r^2)*T^5*g^n*envelope x/|delta|^2 := by ring
      _ ≤ _ := by gcongr
  by_cases hxl : x ≤ 1
  · apply bound (1/4) (U (n+2)) (hU _) (le_add_of_nonneg_right (hV _))
      (by norm_num) (by norm_num) _
      (hu A B hA hB hsep (n+2) p delta x hp0 hd hx)
    rw [envelope,if_pos hxl]
    exact Real.rpow_le_one hx.le hxl (by linarith [hs.2])
  · apply bound 2 (V (n+2)) (hV _) (le_add_of_nonneg_left (hU _))
      (by norm_num) le_rfl _
      (hv A B hA hB hsep (n+2) p delta x hp0 hd hx)
    rw [envelope,if_neg hxl]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [hs.1])

theorem lower_core_power (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hcPhi : HasCompactSupport Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (S r theta rate : ℝ) (hS : 0 ≤ S) (hr : 0 < r) (htheta : theta < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ, ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖-(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 → ∀ p delta x : ℝ, 1 < T →
      1 ≤ p → p ≤ T^2 → 1 ≤ |delta| → 0 < x → p*x ≤ T^theta →
      ‖core (PRZZKeptLiteral.dualProfile Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) T p (-(A+B)/(Real.log T:ℂ)) delta x‖ ≤
        C*T^(-rate)*envelope x/|delta|^2 := by
  obtain ⟨C,hC,hb⟩ := phase_envelope Phi hPhi hcPhi hsPhi S r hS hr
  obtain ⟨n,D,hD,hh⟩ := PRZZZeroUniformHeight.source_order_uniform (1-theta) 5 rate r (by linarith) hr
  have hCn := hC n
  refine ⟨C n*D+1,by positivity,?_⟩
  filter_upwards [hb] with T hb
  intro A B hA hB hsep hn p delta x hT hp hpT hd hx hpx
  have hT0 : 0 < T := by linarith
  have hd0 : delta ≠ 0 := abs_pos.mp (by linarith)
  have hphase : p*x/(|delta| *T) ≤ 3*T^(-(1-theta)) := by
    calc
      _ ≤ T^theta/(1*T) := by gcongr
      _ = T^(-(1-theta)) := by
        rw [one_mul,Real.rpow_neg hT0.le,Real.rpow_sub hT0,Real.rpow_one]
        field_simp
      _ ≤ _ := by nlinarith [Real.rpow_nonneg hT0.le (-(1-theta))]
  have hb' := hb A B hA hB hsep hn n p delta x (3*T^(-(1-theta)))
    hT.le hp hpT hd0 hx (by positivity) hphase
  dsimp only at hb'
  have hh' := mul_le_mul_of_nonneg_left (hh T hT.le) hCn
  rw [Real.rpow_ofNat] at hh'
  have hfac : C n*(1+(Real.log T)^2/r^2)*T^5*(3*T^(-(1-theta)))^n ≤
      (C n*D+1)*T^(-rate) := by
    nlinarith [Real.rpow_nonneg hT0.le (-rate)]
  exact hb'.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hfac (envelope_nonneg x)) (sq_nonneg _))

theorem upper_core_power (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hcPhi : HasCompactSupport Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (S r rate : ℝ) (hS : 0 ≤ S) (hr : 0 < r) (hrate : 0 ≤ rate) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ, ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖-(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 → ∀ p delta x : ℝ, 1 < T →
      1 ≤ p → p ≤ T^2 → delta ≠ 0 → T^2 ≤ x →
      ‖core (PRZZKeptLiteral.dualProfile Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) T p (-(A+B)/(Real.log T:ℂ)) delta x‖ ≤
        C*T^(-rate)*envelope x/|delta|^2 := by
  let H := rate+7
  have hH : 0 ≤ H := by dsimp [H]; linarith
  obtain ⟨U,hU,hb⟩ := PRZZZeroDualHeight.core_scaled_uniform Phi hPhi hcPhi hsPhi S r (H+2) hS hr (by linarith)
  have hU2 := hU 2
  refine ⟨U 2*(1+1/r^2)+1,by positivity,?_⟩
  filter_upwards [hb] with T hb
  intro A B hA hB hsep hn p delta x hT hp hpT hd hxx
  let sigma := -(A+B)/(Real.log T:ℂ)
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
  have hh := hb A B hA hB hsep 2 p delta x hp0 hd hx
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
    (S r theta rate : ℝ) (hS : 0 ≤ S) (hr : 0 < r) (htheta : theta < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ, ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖-(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 → ∀ (P : ℝ → ℝ) (u v delta : ℝ),
      (∀ y, 0 ≤ P y) → (∀ y, P y ≤ 1) → (∀ y, 1 ≤ y → P y = 0) →
      1 < T →
      0 ≤ u → u ≤ T^theta → 1 ≤ u*v → u*v ≤ T^2 → 1 ≤ |delta| →
      ‖∫ x in Ioi (0:ℝ), (P (v*x):ℂ)*core (PRZZKeptLiteral.dualProfile Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) T (u*v) (-(A+B)/(Real.log T:ℂ)) delta x‖ ≤
        C*T^(-rate)/|delta|^2 := by
  obtain ⟨C,hC,hb⟩ := lower_core_power Phi hPhi hcPhi hsPhi S r theta rate hS hr htheta
  let J := ∫ x in Ioi (0:ℝ), envelope x
  have hJ : 0 ≤ J := integral_nonneg (fun x => envelope_nonneg x)
  refine ⟨C*J+1,by positivity,?_⟩
  filter_upwards [hb] with T hb
  intro A B hA hB hsep hn P u v delta hlo hhi hright hT hu huT hp hpT hd
  let K := C*T^(-rate)/|delta|^2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hg : IntegrableOn (fun x => K*envelope x) (Ioi (0:ℝ)) := envelope_integrable.const_mul K
  apply (norm_integral_le_integral_norm _).trans
  have hh := integral_mono_of_nonneg
    (f := fun x : ℝ => ‖(P (v*x):ℂ)*core (PRZZKeptLiteral.dualProfile Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) T (u*v) (-(A+B)/(Real.log T:ℂ)) delta x‖)
    (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) hg (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    by_cases hz : P (v*x) = 0
    · simp only [hz,Complex.ofReal_zero,zero_mul,norm_zero]
      exact mul_nonneg hK (envelope_nonneg x)
    have hb' := hb A B hA hB hsep hn (u*v) delta x hT hp hpT hd hx
      (PRZZZeroBoundaryHeight.lower_geometry P hright T u v x theta hu huT hz)
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hlo _)]
    have hnorm := (mul_le_mul_of_nonneg_right (hhi (v*x)) (norm_nonneg
      (core (PRZZKeptLiteral.dualProfile Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) T (u*v) (-(A+B)/(Real.log T:ℂ)) delta x))).trans_eq (one_mul _)
    exact (hnorm.trans hb').trans_eq (by dsimp [K] <;> ring))
  apply hh.trans
  rw [integral_const_mul]
  dsimp [K,J]
  have ht : 0 ≤ T^(-rate)/|delta|^2 := by positivity
  ring_nf at ht ⊢
  linarith only [ht]

theorem upper_integral (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hcPhi : HasCompactSupport Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (S r rate : ℝ) (hS : 0 ≤ S) (hr : 0 < r) (hrate : 0 ≤ rate) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ, ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖-(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 → ∀ (P : ℝ → ℝ) (R u v delta : ℝ),
      (∀ y, 0 ≤ P y) → (∀ y, P y ≤ 1) → (∀ y ≤ (1/2:ℝ), P y = 1) →
      4 ≤ T →
      T^4/2 ≤ R → 0 < v → v ≤ T → 1 ≤ u*v → u*v ≤ T^2 → delta ≠ 0 →
      ‖∫ x in Ioi (0:ℝ), ((1-P (v*x/R):ℝ):ℂ)*
        core (PRZZKeptLiteral.dualProfile Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) T (u*v) (-(A+B)/(Real.log T:ℂ)) delta x‖ ≤ C*T^(-rate)/|delta|^2 := by
  obtain ⟨C,hC,hb⟩ := upper_core_power Phi hPhi hcPhi hsPhi S r rate hS hr hrate
  let J := ∫ x in Ioi (0:ℝ), envelope x
  have hJ : 0 ≤ J := integral_nonneg (fun x => envelope_nonneg x)
  refine ⟨C*J+1,by positivity,?_⟩
  filter_upwards [hb] with T hb
  intro A B hA hB hsep hn P R u v delta hlo hhi hleft hT hR hv hvT hp hpT hd
  let K := C*T^(-rate)/|delta|^2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hg : IntegrableOn (fun x => K*envelope x) (Ioi (0:ℝ)) := envelope_integrable.const_mul K
  apply (norm_integral_le_integral_norm _).trans
  have hh := integral_mono_of_nonneg
    (f := fun x : ℝ => ‖((1-P (v*x/R):ℝ):ℂ)*core (PRZZKeptLiteral.dualProfile Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) T (u*v) (-(A+B)/(Real.log T:ℂ)) delta x‖)
    (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) hg (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    by_cases hz : 1-P (v*x/R) = 0
    · simp only [hz,Complex.ofReal_zero,zero_mul,norm_zero]
      exact mul_nonneg hK (envelope_nonneg x)
    have hb' := hb A B hA hB hsep hn (u*v) delta x (by linarith) hp hpT hd
      (PRZZZeroBoundaryHeight.upper_geometry P hleft T R v x hT hR hv hvT hx hz)
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (hhi _))]
    have hcap : 1-P (v*x/R) ≤ 1 := by linarith [hlo (v*x/R)]
    have hnorm := (mul_le_mul_of_nonneg_right hcap (norm_nonneg
      (core (PRZZKeptLiteral.dualProfile Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) T (u*v) (-(A+B)/(Real.log T:ℂ)) delta x))).trans_eq (one_mul _)
    exact (hnorm.trans hb').trans_eq (by dsimp [K] <;> ring))
  apply hh.trans
  rw [integral_const_mul]
  dsimp [K,J]
  have ht : 0 ≤ T^(-rate)/|delta|^2 := by positivity
  ring_nf at ht ⊢
  linarith only [ht]

/-- The original strict-M boundary, with the actual Gamma profile and
reflected source shift. Its constant is independent of height and L. -/
theorem native_boundary_power (P : ℝ → ℝ)
    (hP : ContDiff ℝ ∞ (fun y => (P y:ℂ))) (hm : Antitone P)
    (hlo : ∀ y, 0 ≤ P y) (hhi : ∀ y, P y ≤ 1)
    (hl : ∀ y ≤ (1/2:ℝ), P y = 1) (hright : ∀ y, 1 ≤ y → P y = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (S r theta rate : ℝ) (hS : 0 ≤ S) (hr : 0 < r) (htheta : theta < 1) (hrate : 0 ≤ rate) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ → ‖-(A+B)/(Real.log T:ℂ)‖ ≤ 1/8 →
      ∀ (L : ℕ) (u v delta : ℝ), PRZZLiteralExhaustion.spatialLength T ≤ L →
      4 ≤ T → 0 < u → u ≤ T^theta → 0 < v → v ≤ T → 1 ≤ u*v → u*v ≤ T^2 → 1 ≤ |delta| →
      ‖PRZZZeroBoundarySum.row P
        (PRZZKeptLiteral.dualProfile Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)))
          L T u v (-(A+B)/(Real.log T:ℂ)) delta‖ ≤ C*T^(-rate)/|delta|^2 := by
  obtain ⟨C,hC,hloB⟩ := lower_integral Phi hPhi hcPhi hsPhi S r theta rate hS hr htheta
  obtain ⟨D,hD,hhiB⟩ := upper_integral Phi hPhi hcPhi hsPhi S r rate hS hr hrate
  refine ⟨C+D,by positivity,?_⟩
  filter_upwards [hloB,hhiB,PRZZScaledReplacement.shifts_eventually S (1/4) (by norm_num)]
    with T hloB hhiB hsmall
  intro A B hA hB hsep hn L u v delta hL hT hu huT hv hvT hp hpT hd
  have hT0 : 0 < T := by linarith
  have hlog : 0 < Real.log T := Real.log_pos (by linarith)
  have hs : -(A+B)/(Real.log T:ℂ) ≠ 0 := div_ne_zero
    (neg_ne_zero.mpr (norm_pos_iff.mp (hr.trans_le hsep))) (by exact_mod_cast hlog.ne')
  have hd0 : delta ≠ 0 := abs_pos.mp (by linarith)
  have hPc : Continuous P := by
    simpa only [Function.comp_def,Complex.ofReal_re] using Complex.continuous_re.comp hP.continuous
  obtain ⟨hf,hc,hsp⟩ := PRZZZeroDualExhaustion.cutoff_regular Phi hPhi hcPhi hsPhi
    (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) (hsmall.2 A hA) (hsmall.2 B hB) T
  unfold PRZZZeroBoundarySum.row
  rw [PRZZZeroSpatialPrefix.boundary_integral P hPc hm hlo hhi hl hright
    (PRZZKeptLiteral.dualProfile Phi T (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) hf hc hsp L T u v delta _
    hL hT0 hu hv hd0 hs hn]
  have h1 := hloB A B hA hB hsep hn P u v delta hlo hhi hright (by linarith) hu.le huT hp hpT hd
  have hR : T^4/2 ≤ (2:ℝ)^(PRZZZeroSpatialPrefix.firstIndex T) := by
    have hh := PRZZZeroSpatialPrefix.radius T
    rw [Real.rpow_ofNat] at hh
    nlinarith [sq_nonneg (T^2)]
  have h2 := hhiB A B hA hB hsep hn P ((2:ℝ)^(PRZZZeroSpatialPrefix.firstIndex T)) u v delta
    hlo hhi hl hT hR hv hvT hp hpT hd0
  exact ((norm_add_le _ _).trans (add_le_add h1 h2)).trans_eq (by ring)

#print axioms native_boundary_power
#print axioms lower_integral
#print axioms upper_integral
#print axioms lower_core_power
#print axioms upper_core_power
#print axioms phase_envelope
end XiPrime8845.PRZZZeroDualBoundary

