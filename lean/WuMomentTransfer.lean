import WuStirlingMoment

/-! Actual V*Psi smoothed square moment: quantitative replacement, the same
fixed-witness limit, and a mass-normalized numerical cap. The smooth weight
is fixed; neither removal of smoothing nor zero counting is asserted. -/
noncomputable section
open scoped BigOperators
open Filter Topology MeasureTheory Finset
namespace XiPrime8845.WuMomentTransfer
open WuAuxiliary WuStirling WuStirlingTransfer WuStirlingMoment WitnessMomentBound
set_option maxHeartbeats 2000000

def vMoment (Phi : ℝ → ℝ) (T : ℝ) : ℝ :=
  (∫ t : ℝ, ‖V T (leftPoint T t)*psi T (leftPoint T t)‖^2*Phi (t/T))/T

def normalizedVMoment (Phi : ℝ → ℝ) (T : ℝ) : ℝ := vMoment Phi T/mass Phi

theorem square_difference (v u : ℂ) (δ : ℝ) (hδ : 0 < δ) :
    |‖v‖^2-‖u‖^2| ≤ δ*‖u‖^2+(1+1/δ)*‖v-u‖^2 := by
  have ht : ‖v‖ ≤ ‖u‖+‖v-u‖ := by
    have h := norm_add_le u (v-u)
    rw [add_sub_cancel] at h
    exact h
  have hab := abs_norm_sub_norm_le v u
  have he : |‖v‖^2-‖u‖^2| = |‖v‖-‖u‖| * (‖v‖+‖u‖) := by
    rw [show ‖v‖^2-‖u‖^2=(‖v‖-‖u‖)*(‖v‖+‖u‖) by ring,abs_mul,
      abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  have hy : 2*‖u‖*‖v-u‖ ≤ δ*‖u‖^2+‖v-u‖^2/δ := by
    apply le_of_mul_le_mul_left (a:=δ) ?_ hδ
    rw [mul_add,mul_div_cancel₀ _ hδ.ne']
    nlinarith [sq_nonneg (δ*‖u‖-‖v-u‖)]
  rw [he]
  have hh := mul_le_mul hab (show ‖v‖+‖u‖ ≤ 2*‖u‖+‖v-u‖ by linarith)
    (by positivity) (norm_nonneg _)
  calc
    _ ≤ _ := hh
    _ = 2*‖u‖*‖v-u‖+‖v-u‖^2 := by ring
    _ ≤ (δ*‖u‖^2+‖v-u‖^2/δ)+‖v-u‖^2 := add_le_add hy le_rfl
    _ = δ*‖u‖^2+(1+1/δ)*‖v-u‖^2 := by ring

/-- An integral inequality with actual integrability assumptions. -/
theorem weighted_square_difference (v u : ℝ → ℂ) (w : ℝ → ℝ)
    (hw : ∀ t, 0 ≤ w t) (δ T : ℝ) (hδ : 0 < δ) (hT : 0 < T)
    (hv : Integrable (fun t => ‖v t‖^2*w t))
    (hu : Integrable (fun t => ‖u t‖^2*w t))
    (he : Integrable (fun t => ‖v t-u t‖^2*w t)) :
    |(∫ t, ‖v t‖^2*w t)/T-(∫ t, ‖u t‖^2*w t)/T| ≤
      δ*((∫ t, ‖u t‖^2*w t)/T)+(1+1/δ)*((∫ t, ‖v t-u t‖^2*w t)/T) := by
  rw [← sub_div,← integral_sub hv hu,abs_div,abs_of_pos hT]
  have hi : (∫ t, |‖v t‖^2*w t-‖u t‖^2*w t|) ≤
      ∫ t, δ*(‖u t‖^2*w t)+(1+1/δ)*(‖v t-u t‖^2*w t) := by
    apply integral_mono (hv.sub hu).abs ((hu.const_mul δ).add (he.const_mul (1+1/δ)))
    intro t
    change |‖v t‖^2*w t-‖u t‖^2*w t| ≤
      δ*(‖u t‖^2*w t)+(1+1/δ)*(‖v t-u t‖^2*w t)
    have h := mul_le_mul_of_nonneg_right (square_difference (v t) (u t) δ hδ) (hw t)
    simpa only [← sub_mul,abs_mul,abs_of_nonneg (hw t),add_mul,mul_assoc] using h
  have hn : |∫ t, ‖v t‖^2*w t-‖u t‖^2*w t| ≤ ∫ t, |‖v t‖^2*w t-‖u t‖^2*w t| := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
      (fun t => ‖v t‖^2*w t-‖u t‖^2*w t)
  apply (div_le_div_of_nonneg_right (hn.trans hi) hT.le).trans_eq
  rw [integral_add (hu.const_mul δ) (he.const_mul (1+1/δ)),integral_const_mul,integral_const_mul]
  ring

theorem u_integrable (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi) (T : ℝ) (hT : 0 < T) :
    Integrable (fun t => ‖U T (leftPoint T t)*psi T (leftPoint T t)‖^2*Phi (t/T)) := by
  apply weighted_integrable Phi hPhi T hT
  have hp : Continuous (fun t => leftPoint T t) := by unfold leftPoint; fun_prop
  apply ContinuousOn.mul _ ((psi_entire T).continuous.comp hp).continuousOn
  unfold U ZetaMomentPolynomial.differentialPolynomial
  apply continuousOn_finsetSum
  intro k hk
  have hreg : ContinuousOn (iteratedDeriv k riemannZeta) {(1:ℂ)}ᶜ := by
    rw [iteratedDeriv_eq_iterate]
    exact (analyticOn_riemannZeta.iterated_deriv k).continuousOn
  apply continuousOn_const.mul
  apply (hreg.comp hp.continuousOn ?_).div_const
  intro t ht
  change leftPoint T t ≠ 1
  intro hh
  have hh' := congrArg Complex.im hh
  simp [leftPoint] at hh'
  linarith [ht.1]

theorem v_integrable (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi)
    (T : ℝ) (hT : 4 ≤ T)
    (hs : (1/2-PRZZAsymptotic.R/Real.log T) ∈ Set.Icc (7/16) 3) :
    Integrable (fun t => ‖V T (leftPoint T t)*psi T (leftPoint T t)‖^2*Phi (t/T)) := by
  apply weighted_integrable Phi hPhi T (by linarith)
  have hp : Continuous (fun t => leftPoint T t) := by unfold leftPoint; fun_prop
  apply ContinuousOn.mul _ ((psi_entire T).continuous.comp hp).continuousOn
  intro t ht
  have hr : 0 < (leftPoint T t).re := by
    simp only [leftPoint,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_self,add_zero]
    linarith [hs.1]
  have h1 : leftPoint T t ≠ 1 := by
    intro he
    have hh := congrArg Complex.im he
    simp [leftPoint] at hh
    linarith [ht.1]
  exact (((eta_entire (Real.log T) _).continuousAt.div
    (H_analytic _ hr).continuousAt (H_ne_zero _ hr h1)).comp hp.continuousAt).continuousWithinAt

theorem vMoment_nonneg (Phi : ℝ → ℝ) (hPhi : ∀ t, 0 ≤ Phi t) (T : ℝ) (hT : 0 ≤ T) :
    0 ≤ vMoment Phi T :=
  div_nonneg (integral_nonneg (fun t => mul_nonneg (sq_nonneg _) (hPhi (t/T)))) hT

theorem moment_difference_bound (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi)
    (hPhi0 : ∀ t, 0 ≤ Phi t) :
    ∀ᶠ T : ℝ in atTop, ∀ δ > 0,
      |vMoment Phi T-smoothedMoment Phi T| ≤
        δ*smoothedMoment Phi T+(1+1/δ)*errorMoment Phi T := by
  filter_upwards [leftPoint_strip] with T hstrip
  intro δ hδ
  have hT : 0 < T := by linarith [hstrip.1]
  have he := error_integrable Phi hPhi T hstrip.1 hstrip.2.2
  simp only [sub_mul] at he
  simpa only [vMoment,smoothedMoment,errorMoment,sub_mul] using
    weighted_square_difference _ _ _ (fun t => hPhi0 (t/T)) δ T hδ hT
    (v_integrable Phi hPhi T hstrip.1 hstrip.2.2) (u_integrable Phi hPhi T hT) he

/-- Quantitative transfer: O(log^-2 T) squared error gives O(log^-1 T)
difference of the actual square moments. Phi remains fixed. -/
theorem moment_difference_rate (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi)
    (hPhi0 : ∀ t, 0 ≤ Phi t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      |vMoment Phi T-smoothedMoment Phi T| ≤ C/Real.log T := by
  obtain ⟨D,hD,he⟩ := errorMoment_rate Phi hPhi hPhi0
  let M := |NumericalGate.actual.re*mass Phi|+1
  have hM : 0 < M := by dsimp [M]; positivity
  have hu := (smoothedMoment_tendsto Phi hPhi).abs.eventually (gt_mem_nhds
    (show |NumericalGate.actual.re*mass Phi| < M by dsimp [M]; linarith))
  refine ⟨M+2*D,by positivity,?_⟩
  filter_upwards [moment_difference_bound Phi hPhi hPhi0,he,hu,leftPoint_strip] with T hb heT huT hs
  have hl : 0 < Real.log T := by linarith [hs.2.1]
  have hu' : smoothedMoment Phi T ≤ M := (le_abs_self _).trans huT.le
  have h := hb (1/Real.log T) (by positivity)
  have ht : (1+Real.log T)*(D/(Real.log T)^2) ≤ 2*D/Real.log T := by
    calc
      _ ≤ (2*Real.log T)*(D/(Real.log T)^2) :=
        mul_le_mul_of_nonneg_right (by linarith [hs.2.1]) (by positivity)
      _ = _ := by field_simp
  have hh := add_le_add
    (mul_le_mul_of_nonneg_left hu' (by positivity : 0 ≤ 1/Real.log T))
    (mul_le_mul_of_nonneg_left heT.2 (by positivity : 0 ≤ 1+1/(1/Real.log T)))
  simp only [one_div_one_div] at h hh
  apply h.trans
  apply hh.trans
  calc
    _ ≤ (1/Real.log T)*M+2*D/Real.log T := add_le_add le_rfl ht
    _ = _ := by ring

theorem moment_difference_tendsto (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi)
    (hPhi0 : ∀ t, 0 ≤ Phi t) :
    Tendsto (fun T => vMoment Phi T-smoothedMoment Phi T) atTop (nhds 0) := by
  obtain ⟨C,hC,h⟩ := moment_difference_rate Phi hPhi hPhi0
  have ht : Tendsto (fun T : ℝ => C/Real.log T) atTop (nhds 0) := by
    simpa only [Function.comp_def,div_eq_mul_inv,mul_zero] using
      (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul C
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero' (Eventually.of_forall (fun T => norm_nonneg _))
      (by simpa only [Real.norm_eq_abs] using h) ht)

theorem vMoment_tendsto (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi)
    (hPhi0 : ∀ t, 0 ≤ Phi t) :
    Tendsto (vMoment Phi) atTop (nhds (NumericalGate.actual.re*mass Phi)) := by
  simpa only [sub_add_cancel,zero_add] using
    (moment_difference_tendsto Phi hPhi hPhi0).add (smoothedMoment_tendsto Phi hPhi)

theorem normalizedVMoment_tendsto (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi)
    (hPhi0 : ∀ t, 0 ≤ Phi t) (hm : 0 < mass Phi) :
    Tendsto (normalizedVMoment Phi) atTop (nhds NumericalGate.actual.re) := by
  change Tendsto (fun T => vMoment Phi T/mass Phi) atTop _
  simpa only [normalizedVMoment,mul_div_cancel_right₀ _ hm.ne'] using
    (vMoment_tendsto Phi hPhi hPhi0).div_const (mass Phi)

theorem normalizedVMoment_eventually_lt (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi)
    (hPhi0 : ∀ t, 0 ≤ Phi t) (hm : 0 < mass Phi) (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ T : ℝ in atTop, normalizedVMoment Phi T < LogarithmicBudget.certifiedCap+eps :=
  (normalizedVMoment_tendsto Phi hPhi hPhi0 hm).eventually
    (gt_mem_nhds (lt_of_le_of_lt LogarithmicBudget.actual_le_cap (by linarith)))

/-- The literal V=eta/H moment, normalized by the smoothing mass, is ready
for a counting supplier. This theorem does not itself count zeros. -/
theorem v_moment_bound (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi)
    (hPhi0 : ∀ t, 0 ≤ Phi t) (hm : 0 < mass Phi) :
    (0.8845:ℝ) < 1-Real.log countingCap/NumericalGate.R ∧
      ∀ᶠ T : ℝ in atTop, 1 < T ∧ 0 ≤ normalizedVMoment Phi T ∧
        normalizedVMoment Phi T < countingCap := by
  refine ⟨countingCap_budget,?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ),
    normalizedVMoment_eventually_lt Phi hPhi hPhi0 hm (1/1000000) (by norm_num)] with T hT hb
  refine ⟨hT,div_nonneg (vMoment_nonneg Phi hPhi0 T (by linarith)) hm.le,?_⟩
  convert hb using 1
  norm_num [LogarithmicBudget.certifiedCap,countingCap]

theorem unit_mass_vMoment_bound (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi)
    (hPhi0 : ∀ t, 0 ≤ Phi t) (hm : mass Phi = 1) :
    ∀ᶠ T : ℝ in atTop, 0 ≤ vMoment Phi T ∧ vMoment Phi T < countingCap := by
  have h := (v_moment_bound Phi hPhi hPhi0 (by rw [hm]; norm_num)).2
  filter_upwards [h] with T hT
  simpa only [normalizedVMoment,hm,div_one] using hT.2

#print axioms square_difference
#print axioms weighted_square_difference
#print axioms u_integrable
#print axioms v_integrable
#print axioms vMoment_nonneg
#print axioms moment_difference_bound
#print axioms moment_difference_rate
#print axioms moment_difference_tendsto
#print axioms vMoment_tendsto
#print axioms normalizedVMoment_tendsto
#print axioms normalizedVMoment_eventually_lt
#print axioms v_moment_bound
#print axioms unit_mass_vMoment_bound
end XiPrime8845.WuMomentTransfer
