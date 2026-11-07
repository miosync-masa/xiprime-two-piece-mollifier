import PRZZZeroNormalization

/-! Absolute time/gap exchange for the normalized actual zero mode.
The product envelope is supplied from the unit-scale evaluated kernel;
the signed-gap count costs a summable (n+1)^-2, not a row count premise. -/
noncomputable section
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZZeroGapTime
open PRZZCosineMellinCore PRZZCosineMellin PRZZCosineGapMellin
set_option maxHeartbeats 6000000

def weight (Phi : ℝ → ℂ) (T : ℝ) (sigma : ℂ) (t : ℝ) : ℂ :=
  Phi (t/T)*exp (-sigma*(Real.log t:ℂ))
def base (Phi : ℝ → ℂ) (T P : ℝ) (sigma : ℂ) (p : ℝ × ℝ) : ℂ :=
  weight Phi T sigma p.1*evaluated sigma (2*Real.pi*p.1/P) p.2
def summand (Phi : ℝ → ℂ) (T P : ℝ) (sigma : ℂ) (n : ℕ) (p : ℝ × ℝ) : ℂ :=
  weight Phi T sigma p.1*term sigma (2*Real.pi*p.1/P) n p.2

theorem base_integrable (Phi : ℝ → ℂ) (hPhi : Continuous Phi) (T P : ℝ) (sigma : ℂ)
    (hT : 0 < T) (hP : 0 < P) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8) :
    Integrable (base Phi T P sigma) ((volume.restrict (Icc T (2*T))).prod volume) := by
  have hi := evaluated_integrable sigma hs hn 1 (by norm_num)
  let D := (2*Real.pi*T/P)^(-5/4:ℝ)
  have ht : IntegrableOn (fun t : ℝ => ‖weight Phi T sigma t‖*D) (Icc T (2*T)) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    intro t ht
    have ht0 := (hT.trans_le ht.1).ne'
    have hT0 := hT.ne'
    have hl := (Real.continuousAt_log ht0).ofReal
    apply ContinuousAt.continuousWithinAt
    unfold weight
    fun_prop
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => weight Phi T sigma p.1*
      exp (-(line p.2)*(Real.log (2*Real.pi*p.1/P):ℂ))*evaluated sigma 1 p.2)
      ((volume.restrict (Icc T (2*T))).prod volume) := by
    have he : AEStronglyMeasurable (fun p : ℝ × ℝ => evaluated sigma 1 p.2)
        ((volume.restrict (Icc T (2*T))).prod volume) :=
      hi.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    have hc : Measurable (fun p : ℝ × ℝ => weight Phi T sigma p.1*
        exp (-(line p.2)*(Real.log (2*Real.pi*p.1/P):ℂ))) := by
      have hp := hPhi.measurable
      unfold weight line
      fun_prop
    exact hc.aestronglyMeasurable.mul he
  have hpos : ∀ᵐ p : ℝ × ℝ ∂(volume.restrict (Icc T (2*T))).prod volume, p.1 ∈ Icc T (2*T) :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
  apply (ht.mul_prod hi.norm).mono'
  · apply hm.congr
    filter_upwards [hpos] with p hp
    rw [base,PRZZCosineTimeMellin.evaluated_scale sigma (2*Real.pi*p.1/P) p.2
      (by have ht0 := hT.trans_le hp.1; positivity)]
    ring
  · filter_upwards [hpos] with p hp
    have ht0 : 0 < p.1 := hT.trans_le hp.1
    have hx : 0 < 2*Real.pi*p.1/P := by positivity
    have he : ‖exp (-(line p.2)*(Real.log (2*Real.pi*p.1/P):ℂ))‖ = (2*Real.pi*p.1/P)^(-5/4:ℝ) := by
      rw [norm_exp,Real.rpow_def_of_pos hx]
      congr 1
      simp [line]
      ring
    have hlo : 2*Real.pi*T/P ≤ 2*Real.pi*p.1/P := by gcongr; exact hp.1
    have hb : (2*Real.pi*p.1/P)^(-5/4:ℝ) ≤ D :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hlo (by norm_num)
    rw [base,PRZZCosineTimeMellin.evaluated_scale sigma (2*Real.pi*p.1/P) p.2 hx,norm_mul,norm_mul,he]
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
      (norm_nonneg _)).trans_eq (by ring)

theorem summand_bound (Phi : ℝ → ℂ) (T P : ℝ) (sigma : ℂ) (hn : ‖sigma‖ ≤ 1/8)
    (n : ℕ) (p : ℝ × ℝ) :
    ‖summand Phi T P sigma n p‖ ≤ ‖base Phi T P sigma p‖*(1/(((n+1:ℕ):ℝ)^2)) := by
  rw [summand,base,norm_mul,norm_mul]
  exact (mul_le_mul_of_nonneg_left (term_bound sigma hn _ _ n) (norm_nonneg _)).trans_eq (by ring)

theorem summand_integrable (Phi : ℝ → ℂ) (hPhi : Continuous Phi) (T P : ℝ) (sigma : ℂ)
    (hT : 0 < T) (hP : 0 < P) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8) (n : ℕ) :
    Integrable (summand Phi T P sigma n) ((volume.restrict (Icc T (2*T))).prod volume) := by
  have hi := base_integrable Phi hPhi T P sigma hT hP hs hn
  have hd : Continuous (fun tau : ℝ => ((n+1:ℕ):ℂ)^(exponent sigma tau)) := by
    have hnC : ((n+1:ℕ):ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
    simp_rw [Complex.cpow_def_of_ne_zero hnC]
    unfold exponent line
    fun_prop
  apply (hi.norm.mul_const (1/(((n+1:ℕ):ℝ)^2))).mono'
  · have hm := hi.aestronglyMeasurable.div₀ ((hd.measurable.comp measurable_snd).aestronglyMeasurable)
    convert hm using 1
    funext p
    simp only [Pi.div_apply,Function.comp_apply,summand,base,term]
    ring
  · exact Eventually.of_forall (summand_bound Phi T P sigma hn n)

theorem time_absolute_exchange (Phi : ℝ → ℂ) (hPhi : Continuous Phi) (T P : ℝ) (sigma : ℂ)
    (hT : 0 < T) (hP : 0 < P) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8) :
    (∀ n : ℕ, IntegrableOn (fun t : ℝ => weight Phi T sigma t*(∫ tau : ℝ, term sigma (2*Real.pi*t/P) n tau))
      (Icc T (2*T))) ∧
    Summable (fun n : ℕ => ∫ t in Icc T (2*T),
      ‖weight Phi T sigma t*(∫ tau : ℝ, term sigma (2*Real.pi*t/P) n tau)‖) := by
  let mu : Measure (ℝ × ℝ) := (volume.restrict (Icc T (2*T))).prod volume
  have hi := base_integrable Phi hPhi T P sigma hT hP hs hn
  have hj := summand_integrable Phi hPhi T P sigma hT hP hs hn
  have he (n : ℕ) (t : ℝ) : (∫ tau : ℝ, summand Phi T P sigma n (t,tau)) =
      weight Phi T sigma t*(∫ tau : ℝ, term sigma (2*Real.pi*t/P) n tau) := by
    change (∫ tau : ℝ, weight Phi T sigma t*term sigma (2*Real.pi*t/P) n tau) = _
    rw [integral_const_mul]
  refine ⟨?_,?_⟩
  · intro n
    change Integrable (fun t : ℝ => weight Phi T sigma t*(∫ tau : ℝ, term sigma (2*Real.pi*t/P) n tau))
      (volume.restrict (Icc T (2*T)))
    convert (hj n).integral_prod_left using 1
    funext t
    exact (he n t).symm
  have hp : Summable (fun n : ℕ => 1/(((n+1:ℕ):ℝ)^2)) :=
    (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  apply (hp.mul_left (∫ p : ℝ × ℝ, ‖base Phi T P sigma p‖ ∂mu)).of_nonneg_of_le
    (fun n => integral_nonneg (fun t => norm_nonneg _))
  intro n
  have htime := integral_mono_ae (hj n).integral_prod_left.norm (hj n).integral_norm_prod_left
    (Eventually.of_forall (fun t => norm_integral_le_integral_norm (fun tau => summand Phi T P sigma n (t,tau))))
  simp only [he] at htime
  have hprod := integral_prod (fun p : ℝ × ℝ => ‖summand Phi T P sigma n p‖) (hj n).norm
  have hcap := integral_mono_ae (hj n).norm (hi.norm.mul_const (1/(((n+1:ℕ):ℝ)^2)))
    (Eventually.of_forall (summand_bound Phi T P sigma hn n))
  rw [integral_mul_const] at hcap
  exact (htime.trans_eq hprod.symm).trans (hcap.trans_eq (by dsimp [mu]))

theorem time_gap_exchange (Phi : ℝ → ℂ) (hPhi : Continuous Phi) (T P : ℝ) (sigma : ℂ)
    (hT : 0 < T) (hP : 0 < P) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8) :
    (∑' n : ℕ, ∫ t in Icc T (2*T), weight Phi T sigma t*(∫ tau : ℝ, term sigma (2*Real.pi*t/P) n tau)) =
      ∫ t in Icc T (2*T), weight Phi T sigma t*(∑' n : ℕ, ∫ tau : ℝ, term sigma (2*Real.pi*t/P) n tau) := by
  obtain ⟨hi,ha⟩ := time_absolute_exchange Phi hPhi T P sigma hT hP hs hn
  rw [integral_tsum_of_summable_integral_norm hi ha]
  congr 1
  funext t
  exact (tsum_mul_left (a := weight Phi T sigma t)
    (f := fun n : ℕ => ∫ tau : ℝ, term sigma (2*Real.pi*t/P) n tau))

#print axioms base_integrable
#print axioms summand_bound
#print axioms summand_integrable
#print axioms time_absolute_exchange
#print axioms time_gap_exchange
end XiPrime8845.PRZZZeroGapTime
