import PRZZSignedCentral
import PRZZTimeAmplitude
import PRZZDeltaDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Absolute gap domination for the actual zero Fourier kernel.
Time integration is performed before the spatial norm. The sourceW
derivative masses are supplied, not assumed. Cosine Mellin evaluation
and the unbounded spatial partition are not asserted in this module. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZZeroGap
open PRZZCentralFubini PRZZTimeAmplitude
set_option maxHeartbeats 5000000

def core (Phi : ℝ → ℂ) (T u : ℝ) (sigma : ℂ) (delta x : ℝ) : ℂ :=
  Complex.exp (-(sigma+1)*(Real.log x:ℂ))*
    ∫ t : ℝ, Complex.exp (I*((t*(delta/(u*x)):ℝ):ℂ))*
      amplitude Phi T (2*Real.pi*u*x^2) sigma t

/-- Exact identification with the previous actual zero Fourier kernel.
The local cutoff is still present with its actual value. -/
theorem kernel_time (F Phi : ℝ → ℂ) (M T u delta x : ℝ) (sigma : ℂ) :
    (∫ t : ℝ, kernel F Phi M u delta T 0 (sigma+1) sigma x t) =
      F (M⁻¹*x)*core Phi T u sigma delta x := by
  rw [core,← integral_const_mul,← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  unfold kernel PRZZFullWeightSmooth.weight amplitude PRZZTimeJets.reciprocal
    PRZZMellinSeparation.scaledCutoff
  have ha : (delta*t/u)/x = t*(delta/(u*x)) := by simp only [div_eq_mul_inv,mul_inv_rev]; ring
  have hb : (2*Real.pi*u/t)*x^2 = (2*Real.pi*u*x^2)/t := by ring
  have hc : T⁻¹*t = t/T := by ring
  simp only [mul_zero,zero_mul,Complex.ofReal_zero,Complex.exp_zero,one_mul,ha,hb,hc]
  ring

theorem power_norm (sigma : ℂ) (x : ℝ) (hx : 0 < x) :
    ‖Complex.exp (-(sigma+1)*(Real.log x:ℂ))‖ = x^(-(sigma.re+1)) := by
  rw [Complex.norm_exp,Real.rpow_def_of_pos hx]
  congr 1
  simp only [mul_re,neg_re,add_re,one_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  ring

/-- Arbitrarily many powers of the actual signed gap, with no derivative
mass premise. Constants are selected before height and spatial scales. -/
theorem core_decay (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hcPhi : HasCompactSupport Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ U : ℕ → ℂ → ℝ, (∀ n sigma, 0 ≤ U n sigma) ∧
      ∀ (n : ℕ) (sigma : ℂ) (T u delta x : ℝ),
      sigma ≠ 0 → 0 < T → 0 < u → delta ≠ 0 → 0 < x →
      ‖core Phi T u sigma delta x‖ ≤
        x^(-(sigma.re+1))*U n sigma*((2*Real.pi*u*x^2)/(2*T))^(-a)*
          T/T^n*(u*x)^n/|delta|^n := by
  obtain ⟨C,D,E,hpos,hm⟩ := mass Phi hPhi hcPhi a ha
  let U := fun (n : ℕ) (sigma : ℂ) => PRZZFullWeightJets.convolution C
    (fun i => D i+E i/‖sigma‖^2) n
  have hU (n : ℕ) (sigma : ℂ) : 0 ≤ U n sigma := by
    unfold U PRZZFullWeightJets.convolution
    exact Finset.sum_nonneg (fun i hi => mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (hpos i).1)
      (add_nonneg (hpos (n-i)).2.1 (div_nonneg (hpos (n-i)).2.2 (sq_nonneg _))))
  refine ⟨U,hU,?_⟩
  intro n sigma T u delta x hs hT hu hd hx
  have hk : 0 < 2*Real.pi*u*x^2 := by positivity
  have ho : delta/(u*x) ≠ 0 := div_ne_zero hd (by positivity)
  have hb := PRZZDeltaDecay.oscillatory_bound (amplitude Phi T (2*Real.pi*u*x^2) sigma)
    (smooth Phi hPhi hsPhi T _ sigma hT hk hs) (compact Phi hsPhi T _ sigma hT)
    n (delta/(u*x)) ho
  rw [mass_window Phi hsPhi T _ sigma hT n] at hb
  have hm' := hm n T (2*Real.pi*u*x^2) sigma hT hk hs
  have hh := hb.trans (div_le_div_of_nonneg_right hm' (by positivity))
  change _ ≤ U n sigma*((2*Real.pi*u*x^2)/(2*T))^(-a)*T/T^n/|delta/(u*x)|^n at hh
  rw [core,norm_mul,power_norm sigma x hx]
  apply (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq
  rw [abs_div,abs_of_pos (mul_pos hu hx),div_pow]
  field_simp

def envelope (x : ℝ) : ℝ := if x ≤ 1 then 1 else x^(-2:ℝ)

theorem envelope_nonneg (x : ℝ) : 0 ≤ envelope x := by
  unfold envelope
  split_ifs with hx
  · norm_num
  · exact Real.rpow_nonneg (by linarith) _

theorem envelope_integrable : IntegrableOn envelope (Ioi (0:ℝ)) := by
  have hs : IntegrableOn envelope (Ioc (0:ℝ) 1) := by
    have hh : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Icc (0:ℝ) 1) := continuous_const.integrableOn_Icc
    exact (hh.mono_set Ioc_subset_Icc_self).congr_fun
      (fun x hx => by simp only [envelope,if_pos (mem_Ioc.mp hx).2]) measurableSet_Ioc
  have hl : IntegrableOn envelope (Ioi (1:ℝ)) := by
    apply (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) (by norm_num : (0:ℝ) < 1)).congr_fun
      _ measurableSet_Ioi
    intro x hx
    simp only [envelope,if_neg (not_le.mpr (mem_Ioi.mp hx))]
  have he : Ioc (0:ℝ) 1 ∪ Ioi 1 = Ioi 0 := by
    ext x
    simp only [mem_union,mem_Ioc,mem_Ioi]
    constructor
    · rintro (h | h)
      · exact h.1
      · linarith
    · intro h
      by_cases h1 : x ≤ 1
      · exact Or.inl ⟨h,h1⟩
      · exact Or.inr (lt_of_not_ge h1)
  rw [← he]
  exact hs.union hl

/-- The two different decay rates are used before taking the common cap.
In particular the small-x side is bounded; no spurious x^-4 divergence
is introduced when the spatial partition is later removed. -/
theorem core_envelope (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hcPhi : HasCompactSupport Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2) :
    ∀ (sigma : ℂ) (T u : ℝ), sigma ≠ 0 → ‖sigma‖ ≤ 1/8 → 0 < T → 0 < u →
      ∃ B : ℝ, 0 < B ∧ ∀ delta x : ℝ, delta ≠ 0 → 0 < x →
        ‖core Phi T u sigma delta x‖ ≤ B*envelope x/|delta|^2 := by
  obtain ⟨U,hU,hu⟩ := core_decay Phi hPhi hcPhi hsPhi (1/4) (by norm_num)
  obtain ⟨V,hV,hv⟩ := core_decay Phi hPhi hcPhi hsPhi 2 (by norm_num)
  intro sigma T u hs hn hT hup
  let C := fun (a A : ℝ) => A*(Real.pi*u/T)^(-a)*T/T^2*u^2
  have hC (a A : ℝ) (hA : 0 ≤ A) : 0 ≤ C a A := by dsimp [C]; positivity
  let B := C (1/4) (U 2 sigma)+C 2 (V 2 sigma)+1
  refine ⟨B,by dsimp [B]; linarith [hC (1/4) (U 2 sigma) (hU _ _),hC 2 (V 2 sigma) (hV _ _)],?_⟩
  intro delta x hd hx
  have normalize (a A : ℝ) :
      x^(-(sigma.re+1))*A*((2*Real.pi*u*x^2)/(2*T))^(-a)*T/T^2*(u*x)^2/|delta|^2 =
        C a A*x^(1-sigma.re-2*a)/|delta|^2 := by
    have he : (2*Real.pi*u*x^2)/(2*T) = (Real.pi*u/T)*x^2 := by ring
    rw [he,Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_natCast x 2,← Real.rpow_mul hx.le]
    rw [show 1-sigma.re-2*a = -(sigma.re+1)+2*(-a)+2 by ring]
    simp only [Real.rpow_add hx,Real.rpow_two]
    dsimp [C]
    ring
  have hsr := abs_le.mp ((Complex.abs_re_le_norm sigma).trans hn)
  by_cases hxl : x ≤ 1
  · have hh := hu 2 sigma T u delta x hs hT hup hd hx
    rw [normalize] at hh
    have hp : x^(1-sigma.re-2*(1/4:ℝ)) ≤ 1 :=
      Real.rpow_le_one hx.le hxl (by linarith [hsr.2])
    apply hh.trans
    unfold envelope
    rw [if_pos hxl]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have h0 := hC (1/4) (U 2 sigma) (hU _ _)
    have h1 := hC 2 (V 2 sigma) (hV _ _)
    dsimp only [B]
    nlinarith [mul_le_mul_of_nonneg_left hp h0]
  · have hh := hv 2 sigma T u delta x hs hT hup hd hx
    rw [normalize] at hh
    have hp : x^(1-sigma.re-2*(2:ℝ)) ≤ x^(-2:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [hsr.1])
    apply hh.trans
    unfold envelope
    rw [if_neg hxl]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have h0 := hC (1/4) (U 2 sigma) (hU _ _)
    have h1 := hC 2 (V 2 sigma) (hV _ _)
    exact (mul_le_mul_of_nonneg_left hp h1).trans
      (mul_le_mul_of_nonneg_right (show C 2 (V 2 sigma) ≤ B by dsimp [B]; linarith)
        (Real.rpow_nonneg hx.le (-2:ℝ)))

#print axioms kernel_time
#print axioms power_norm
#print axioms core_decay
#print axioms envelope_nonneg
#print axioms envelope_integrable
#print axioms core_envelope
end XiPrime8845.PRZZZeroGap
