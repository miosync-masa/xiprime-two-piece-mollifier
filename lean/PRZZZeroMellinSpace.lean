import PRZZSourceWLine
import PRZZCentralFubini

/-! Exact Mellin representation of the original supported zero Fourier
spatial integral. Joint integrability is supplied from positive compact
support and the actual sourceW contour norm. No space/Mellin Fubini
premise or replacement of the reciprocal phase is supplied. -/
noncomputable section
open scoped FourierTransform
open MeasureTheory Complex Set Filter Topology
namespace XiPrime8845.PRZZZeroMellinSpace
open PRZZDyadicEnvelope PRZZSourceWLine
set_option maxHeartbeats 5000000

def amplitude (F : ℝ → ℂ) (M omega : ℝ) (z : ℂ) (x : ℝ) : ℂ :=
  F (M⁻¹*x)*exp (-z*(Real.log x:ℂ))*exp (I*((omega/x:ℝ):ℂ))
def lifted (F : ℝ → ℂ) (M k omega : ℝ) (z sigma : ℂ) (c x tau : ℝ) : ℂ :=
  amplitude F M omega z x*exp (-line c tau*(Real.log (k*x^2):ℂ))*weight sigma 1 c tau

theorem lifted_eq (F : ℝ → ℂ) (M k omega : ℝ) (z sigma : ℂ) (c x tau : ℝ)
    (hk : 0 < k) (hx : 0 < x) :
    lifted F M k omega z sigma c x tau = amplitude F M omega z x*weight sigma (k*x^2) c tau := by
  have hy : 0 < k*x^2 := by positivity
  have hp : ((k*x^2:ℝ):ℂ)^(-line c tau) = exp (-line c tau*(Real.log (k*x^2):ℂ)) := by
    rw [cpow_def_of_ne_zero (by exact_mod_cast hy.ne'),← ofReal_log hy.le]
    congr 1; ring
  unfold lifted weight
  rw [hp]
  try simp only [ofReal_one,one_cpow]
  ring

theorem lifted_norm (F : ℝ → ℂ) (M k omega : ℝ) (z sigma : ℂ) (c x tau : ℝ)
    (hk : 0 < k) (hx : 0 < x) :
    ‖lifted F M k omega z sigma c x tau‖ =
      (‖amplitude F M omega z x‖*(k*x^2)^(-c))*‖weight sigma 1 c tau‖ := by
  have hy : 0 < k*x^2 := by positivity
  have he : ‖exp (-line c tau*(Real.log (k*x^2):ℂ))‖ = (k*x^2)^(-c) := by
    rw [norm_exp,Real.rpow_def_of_pos hy]
    congr 1
    simp [line,mul_re]
    ring
  simp only [lifted,norm_mul,he]

theorem joint_integrable (F : ℝ → ℂ) (hF : Continuous F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (M k omega : ℝ) (z sigma : ℂ) (c : ℝ)
    (hM : 0 < M) (hk : 0 < k) (hs : sigma ≠ 0) (hc : 0 < c) :
    Integrable (fun p : ℝ × ℝ => lifted F M k omega z sigma c p.1 p.2)
      ((volume.restrict (Ioi (0:ℝ))).prod volume) := by
  let K : Set ℝ := Icc (M/2) (3*M)
  let g : ℝ → ℝ := fun x => ‖amplitude F M omega z x‖*(k*x^2)^(-c)
  have hg : ContinuousOn g K := by
    intro x hx
    have hxpos : 0 < x := (by positivity : 0 < M/2).trans_le hx.1
    have hx0 : x ≠ 0 := hxpos.ne'
    have hy : k*x^2 ≠ 0 := by positivity
    have hf : ContinuousAt (fun y : ℝ => F (M⁻¹*y)) x :=
      hF.continuousAt.comp (continuousAt_const.mul continuousAt_id)
    have hl : ContinuousAt (fun y : ℝ => (Real.log y:ℂ)) x :=
      Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log hx0)
    have hp : ContinuousAt (fun y : ℝ => ((omega/y:ℝ):ℂ)) x :=
      Complex.continuous_ofReal.continuousAt.comp
        ((continuousAt_const : ContinuousAt (fun _ : ℝ => omega) x).div continuousAt_id hx0)
    have hrp : ContinuousAt (fun y : ℝ => (k*y^2)^(-c)) x :=
      (continuousAt_const.mul (continuousAt_id.pow 2)).rpow_const (Or.inl hy)
    have he1 : ContinuousAt (fun y : ℝ => exp (-z*(Real.log y:ℂ))) x :=
      Complex.continuous_exp.continuousAt.comp
        ((continuousAt_const : ContinuousAt (fun _ : ℝ => -z) x).mul hl)
    have he2 : ContinuousAt (fun y : ℝ => exp (I*((omega/y:ℝ):ℂ))) x :=
      Complex.continuous_exp.continuousAt.comp
        ((continuousAt_const : ContinuousAt (fun _ : ℝ => I) x).mul hp)
    exact (((hf.mul he1).mul he2).norm.mul hrp).continuousWithinAt
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  let D : ℝ := |B|+1
  have hD : 0 < D := by dsimp [D]; positivity
  have hb0 : IntegrableOn (fun _ : ℝ => D) K :=
    continuous_const.continuousOn.integrableOn_compact isCompact_Icc
  have hspace : Integrable (K.indicator (fun _ : ℝ => D)) :=
    hb0.integrable_indicator measurableSet_Icc
  have ht := (weight_integrable sigma hs 1 c zero_lt_one hc).norm
  apply ((hspace.integrableOn (s := Ioi (0:ℝ))).mul_prod ht).mono'
  · exact (by
      unfold lifted amplitude
      simp only [weight,ofReal_one,one_cpow]
      unfold line annihilator
      fun_prop :
      Measurable (fun p : ℝ × ℝ => lifted F M k omega z sigma c p.1 p.2)).aestronglyMeasurable
  · have hpos : ∀ᵐ p : ℝ × ℝ ∂(volume.restrict (Ioi (0:ℝ))).prod volume, 0 < p.1 :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)
    filter_upwards [hpos] with p hx
    rcases p with ⟨x,tau⟩
    by_cases hxK : x ∈ K
    · rw [Set.indicator_of_mem hxK,lifted_norm F M k omega z sigma c x tau hk hx]
      have hb : g x ≤ D := by
        have hh := hB x hxK
        have ha := le_abs_self (g x)
        rw [Real.norm_eq_abs] at hh
        dsimp [D]; linarith [le_abs_self B]
      exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    · have hz : F (M⁻¹*x) = 0 := by
        by_contra hn
        have hh := hsF hn
        have hl : M/2 ≤ x := by
          have he := (le_div_iff₀ hM).mp (show (1/2:ℝ) ≤ x/M by simpa [div_eq_mul_inv,mul_comm] using hh.1)
          linarith
        have hu : x ≤ 3*M := (div_le_iff₀ hM).mp (by simpa [div_eq_mul_inv,mul_comm] using hh.2)
        exact hxK ⟨hl,hu⟩
      simp [Set.indicator_of_notMem hxK,lifted,amplitude,hz]

theorem spatial_mellin (F : ℝ → ℂ) (hF : Continuous F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (M k omega : ℝ) (z sigma : ℂ) (c : ℝ)
    (hM : 0 < M) (hk : 0 < k) (hs : sigma ≠ 0) (hc : 0 < c) :
    (∫ x in Ioi (0:ℝ), amplitude F M omega z x*sourceW sigma (k*x^2)) =
      (1/(2*Real.pi):ℂ)*∫ tau : ℝ, ∫ x in Ioi (0:ℝ), lifted F M k omega z sigma c x tau := by
  calc
    _ = (1/(2*Real.pi):ℂ)*∫ x in Ioi (0:ℝ), ∫ tau : ℝ, lifted F M k omega z sigma c x tau := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [sourceW_shift sigma hs (k*x^2) c (mul_pos hk (sq_pos_of_pos hx)) hc]
      simp_rw [lifted_eq F M k omega z sigma c x _ hk hx]
      rw [integral_const_mul]
      ring
    _ = _ := by rw [integral_integral_swap (joint_integrable F hF hsF M k omega z sigma c hM hk hs hc)]

/-- The original literal zero-frequency spatial kernel, with the
unchanged reciprocal phase, test cutoff, and Mellin normalization. -/
theorem original_zero_spatial (F Phi : ℝ → ℂ) (hF : Continuous F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (M u delta T t : ℝ) (z sigma : ℂ)
    (hM : 0 < M) (hu : 0 < u) (ht : 0 < t) (hs : sigma ≠ 0) :
    (∫ x in Ioi (0:ℝ), PRZZCentralFubini.kernel F Phi M u delta T 0 z sigma x t) =
      Phi (t/T)*(1/(2*Real.pi):ℂ)*∫ tau : ℝ, ∫ x in Ioi (0:ℝ),
        lifted F M (2*Real.pi*u/t) (delta*t/u) z sigma (5/4) x tau := by
  have he (x : ℝ) : PRZZCentralFubini.kernel F Phi M u delta T 0 z sigma x t =
      Phi (t/T)*(amplitude F M (delta*t/u) z x*sourceW sigma ((2*Real.pi*u/t)*x^2)) := by
    unfold PRZZCentralFubini.kernel PRZZFullWeightSmooth.weight amplitude
    simp only [mul_zero,zero_mul,Complex.ofReal_zero,Complex.exp_zero,one_mul]
    ring
  simp_rw [he]
  rw [integral_const_mul,spatial_mellin F hF hsF M (2*Real.pi*u/t) (delta*t/u) z sigma (5/4)
    hM (by positivity) hs (by norm_num)]
  ring

/-- Return the supported original space-time zero mode to a Mellin
spatial integral. Time remains outside Mellin; no time/Mellin exchange
or removal of the spatial partition is asserted here. -/
theorem original_zero_time (F Phi : ℝ → ℂ) (hF : Continuous F) (hP : Continuous Phi)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (M u delta T : ℝ) (z sigma : ℂ)
    (hM : 0 < M) (hu : 0 < u) (hT : 0 < T) (hs : sigma ≠ 0) :
    (∫ x in Ioi (0:ℝ), ∫ t : ℝ, PRZZCentralFubini.kernel F Phi M u delta T 0 z sigma x t) =
      (1/(2*Real.pi):ℂ)*∫ t in Ioi (0:ℝ), Phi (t/T)*∫ tau : ℝ, ∫ x in Ioi (0:ℝ),
        lifted F M (2*Real.pi*u/t) (delta*t/u) z sigma (5/4) x tau := by
  rw [PRZZCentralFubini.kernel_swap F Phi hF hP M u delta T 0 z sigma hM hu hT hs hsF hsP,
    ← integral_const_mul,← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  by_cases ht : 0 < t
  · rw [Set.indicator_of_mem (show t ∈ Ioi (0:ℝ) from ht)]
    have he : (∫ x in Ioi (0:ℝ), PRZZCentralFubini.kernel F Phi M u delta T 0 z sigma x t) =
        Phi (t/T)*𝓕 (PRZZFullWeightSmooth.weight F M (2*Real.pi*u/t) (delta*t/u) z sigma) 0 := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
      · exact PRZZCentralFubini.kernel_fourier F Phi M u delta T 0 z sigma t
      · intro x hx
        by_contra hn
        have hh := (PRZZCentralFubini.kernel_support F Phi M u delta T 0 z sigma hM hT hsF hsP
          (show (x,t) ∈ Function.support (Function.uncurry (PRZZCentralFubini.kernel F Phi M u delta T 0 z sigma)) from hn)).1.1
        have hx0 : x ≤ 0 := by simpa only [mem_Ioi,not_lt] using hx
        linarith
    dsimp only
    rw [← he,original_zero_spatial F Phi hF hsF M u delta T t z sigma hM hu ht hs]
    ring
  · rw [Set.indicator_of_notMem (show t ∉ Ioi (0:ℝ) from ht)]
    have hz : Phi (t/T) = 0 := by
      by_contra hn
      have hh := (le_div_iff₀ hT).mp (hsP hn).1
      linarith
    simp [hz]

#print axioms original_zero_time
#print axioms lifted_eq
#print axioms lifted_norm
#print axioms joint_integrable
#print axioms spatial_mellin
#print axioms original_zero_spatial
end XiPrime8845.PRZZZeroMellinSpace
