import WuUnsmoothing

/-! Interior-window logarithmic input, using only the original PRZZ input.
Positive regularization avoids assigning a finite logarithm to a zero.
This is a left-line integral bound, not a Littlewood or zero-counting theorem. -/
noncomputable section
open Filter Topology MeasureTheory
namespace XiPrime8845.WuTrimmedLog
open WuUnsmoothing WuAuxiliary WuStirling WitnessMomentBound
set_option maxHeartbeats 2000000

def interval (δ T : ℝ) : Set ℝ := Set.Icc ((1+δ)*T) ((2-δ)*T)
def length (δ T : ℝ) : ℝ := (1-2*δ)*T
def logMean (δ ρ T : ℝ) : ℝ :=
  (∫ t in interval δ T, Real.log (density T t+ρ))/(2*length δ T)

theorem density_continuous :
    ∀ᶠ T : ℝ in atTop, ContinuousOn (density T) (Set.Icc T (2*T)) := by
  filter_upwards [WuStirlingTransfer.leftPoint_strip] with T hs
  have hp : Continuous (fun t => leftPoint T t) := by unfold leftPoint; fun_prop
  have hc : ContinuousOn (fun t => V T (leftPoint T t)*psi T (leftPoint T t))
      (Set.Icc T (2*T)) := by
    apply ContinuousOn.mul _ ((psi_entire T).continuous.comp hp).continuousOn
    intro t ht
    have hr : 0 < (leftPoint T t).re := by
      simp only [leftPoint, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero]
      linarith [hs.2.2.1]
    have h1 : leftPoint T t ≠ 1 := by
      intro he
      have hh := congrArg Complex.im he
      simp [leftPoint] at hh
      linarith [ht.1, hs.1]
    exact (((eta_entire (Real.log T) _).continuousAt.div
      (H_analytic _ hr).continuousAt (H_ne_zero _ hr h1)).comp hp.continuousAt).continuousWithinAt
  exact hc.norm.pow 2

theorem length_pos (δ T : ℝ) (hd : δ < 1/2) (hT : 0 < T) : 0 < length δ T :=
  mul_pos (by linarith) hT

theorem integral_density (δ T : ℝ) (hd : δ < 1/2) (hT : 0 < T) :
    (∫ t in interval δ T, density T t) = length δ T*trimmedMean δ T := by
  rw [trimmedMean, trimmedMoment_eq]
  unfold interval length
  have hn : 1-2*δ ≠ 0 := by linarith
  rw [div_div, mul_comm T (1-2*δ)]
  exact (mul_div_cancel₀ _ (mul_ne_zero hn hT.ne')).symm

theorem log_tangent (x c : ℝ) (hx : 0 < x) (hc : 0 < c) :
    Real.log x ≤ Real.log c+x/c-1 := by
  have h := Real.log_le_sub_one_of_pos (div_pos hx hc)
  rw [Real.log_div hx.ne' hc.ne'] at h
  linarith

/-- A finite-T Jensen bound proved by the tangent inequality. -/
theorem logMean_le (δ ρ T c : ℝ) (hd : δ < 1/2) (hT : 0 < T)
    (hρ : 0 < ρ) (hc : 0 < c) (hf : ContinuousOn (density T) (interval δ T))
    (hm : trimmedMean δ T+ρ ≤ c) : logMean δ ρ T ≤ Real.log c/2 := by
  have hlen := length_pos δ T hd hT
  have hab : (1+δ)*T ≤ (2-δ)*T := by have := hlen; unfold length at this; nlinarith
  have hi : IntegrableOn (density T) (interval δ T) := hf.integrableOn_compact isCompact_Icc
  have hlog : IntegrableOn (fun t => Real.log (density T t+ρ)) (interval δ T) :=
    ((hf.add continuousOn_const).log (fun t _ => ne_of_gt (by
      change 0 < density T t+ρ
      have : 0 ≤ density T t := sq_nonneg _
      linarith))).integrableOn_compact isCompact_Icc
  have hci (a : ℝ) : IntegrableOn (fun _ : ℝ => a) (interval δ T) :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  have hid : IntegrableOn (fun t => (density T t+ρ)/c) (interval δ T) :=
    (hi.add (hci ρ)).div_const c
  have his : IntegrableOn (fun t => Real.log c+(density T t+ρ)/c) (interval δ T) :=
    (hci (Real.log c)).add hid
  have hconst (a : ℝ) : (∫ _ in interval δ T, a) = length δ T*a := by
    simp only [interval, setIntegral_const, Real.volume_real_Icc_of_le hab, smul_eq_mul]
    unfold length
    ring
  have hb : (∫ t in interval δ T, Real.log (density T t+ρ)) ≤
      length δ T*(Real.log c+(trimmedMean δ T+ρ)/c-1) := by
    calc
      _ ≤ ∫ t in interval δ T, Real.log c+(density T t+ρ)/c-1 := by
        apply setIntegral_mono_on hlog
          (((hci (Real.log c)).add ((hi.add (hci ρ)).div_const c)).sub (hci 1))
          measurableSet_Icc
        intro t ht
        exact log_tangent _ c (by have := sq_nonneg ‖V T (leftPoint T t)*psi T (leftPoint T t)‖; change 0 < density T t+ρ; unfold density; linarith) hc
      _ = _ := by
        rw [integral_sub his (hci 1),
          integral_add (hci (Real.log c)) hid, integral_div,
          integral_add hi (hci ρ), hconst, hconst, hconst, integral_density δ T hd hT]
        ring
  have hh : (trimmedMean δ T+ρ)/c ≤ 1 := (div_le_one hc).mpr hm
  unfold logMean
  apply (div_le_iff₀ (mul_pos (by norm_num) hlen)).mpr
  nlinarith

/-- One positive regularization cap works for every fixed interior width.
The height threshold may depend on the width, but not on rho below the cap. -/
theorem logMean_eventually_le :
    ∃ ρ0 : ℝ, 0 < ρ0 ∧ ∀ δ : ℝ, 0 < δ → δ < 1/2 →
      ∀ᶠ T : ℝ in atTop, ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ0 →
        logMean δ ρ T ≤ Real.log countingCap/2 := by
  have hgap : NumericalGate.actual.re < countingCap :=
    LogarithmicBudget.actual_le_cap.trans_lt (by
      norm_num [LogarithmicBudget.certifiedCap, countingCap])
  let ρ0 := (countingCap-NumericalGate.actual.re)/2
  have hρ0 : 0 < ρ0 := by dsimp [ρ0]; linarith
  refine ⟨ρ0,hρ0,?_⟩
  intro δ hδ hd
  have hmid : NumericalGate.actual.re < countingCap-ρ0 := by dsimp [ρ0]; linarith
  filter_upwards [density_continuous, eventually_gt_atTop (0:ℝ),
    (trimmedMean_tendsto δ hδ hd).eventually (gt_mem_nhds hmid)] with T hf hT hm
  intro ρ hρ hr
  apply logMean_le δ ρ T countingCap hd hT hρ (by norm_num [countingCap]) _ (by linarith)
  apply hf.mono
  intro t ht
  dsimp [interval] at ht
  constructor <;> nlinarith [ht.1,ht.2]

#print axioms density_continuous
#print axioms integral_density
#print axioms log_tangent
#print axioms logMean_le
#print axioms logMean_eventually_le
end XiPrime8845.WuTrimmedLog
