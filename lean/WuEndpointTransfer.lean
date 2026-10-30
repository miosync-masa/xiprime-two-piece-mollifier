import SmoothEndpoint
import WuUnsmoothing

/-! Conditional endpoint transfer with the ORIGINAL height and mollifier.
The missing localized moment suppliers are explicit hypotheses, not axioms.
Stirling is used only on [T,2T], never on the widened support of the U weights.
No implication from LocalizedEstimate to these suppliers is asserted here. -/
noncomputable section
open scoped BigOperators
open Filter Topology MeasureTheory Finset
namespace XiPrime8845.WuEndpointTransfer
open PRZZLocalization SmoothEndpoint SmoothWindow WuUnsmoothing
open WuAuxiliary WuStirling WuStirlingTransfer WuStirlingMoment ZetaMomentIntegral
set_option maxHeartbeats 2000000

def errorDensity (T t : ℝ) : ℝ :=
  ‖(V T (leftPoint T t)-U T (leftPoint T t))*psi T (leftPoint T t)‖^2

def fullError (T : ℝ) : ℝ := (∫ t in Set.Icc T (2*T), errorDensity T t)/T

/-- Needed from localized PRZZ plus gcd/jet identification; not supplied by
the existing [1,2]-supported moment theorem. Full mass is essential. -/
def LocalizedUMoments : Prop :=
  ∀ Phi : ℝ → ℝ, SmoothWeightOn (1/2) (5/2) Phi → (∀ u, 0 ≤ Phi u) →
    Tendsto (smoothedMoment Phi) atTop (nhds (NumericalGate.actual.re*fullMass Phi))

/-- Only one fixed majorant is required for the seven derivative orders. -/
def MajorantDerivativeBounds : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ k ≤ 6, derivativeMoment k fullCap T ≤ C

theorem zeta_continuous (k : ℕ) (T a b : ℝ) (hT : 0 < T) (ha : 0 < a) :
    ContinuousOn (fun t => scaledZeta k T (leftPoint T t)) (Set.Icc (a*T) (b*T)) := by
  have hp : Continuous (fun t => leftPoint T t) := by unfold leftPoint; fun_prop
  have hreg : ContinuousOn (iteratedDeriv k riemannZeta) {(1:ℂ)}ᶜ := by
    rw [iteratedDeriv_eq_iterate]
    exact (analyticOn_riemannZeta.iterated_deriv k).continuousOn
  exact (hreg.comp hp.continuousOn (by
    intro t ht
    change leftPoint T t ≠ 1
    intro hh
    have hh' := congrArg Complex.im hh
    simp [leftPoint] at hh'
    nlinarith [ht.1])).div_const _

theorem u_continuous (T a b : ℝ) (hT : 0 < T) (ha : 0 < a) :
    ContinuousOn (fun t => U T (leftPoint T t)*psi T (leftPoint T t))
      (Set.Icc (a*T) (b*T)) := by
  have hp : Continuous (fun t => leftPoint T t) := by unfold leftPoint; fun_prop
  apply ContinuousOn.mul _ ((psi_entire T).continuous.comp hp).continuousOn
  unfold U ZetaMomentPolynomial.differentialPolynomial
  apply continuousOn_finsetSum
  intro k hk
  exact continuousOn_const.mul (zeta_continuous k T a b hT ha)

theorem broad_u_integrable (Phi : ℝ → ℝ) (hPhi : SmoothWeightOn (1/2) (5/2) Phi)
    (T : ℝ) (hT : 0 < T) :
    Integrable (fun t => ‖U T (leftPoint T t)*psi T (leftPoint T t)‖^2*Phi (t/T)) :=
  PRZZLocalization.weighted_integrable hPhi hT _ (u_continuous T _ _ hT (by norm_num))

theorem broad_derivative_integrable (k : ℕ) (T : ℝ) (hT : 0 < T) :
    Integrable (fun t => ‖scaledZeta k T (leftPoint T t)*psi T (leftPoint T t)‖^2*fullCap (t/T)) := by
  apply PRZZLocalization.weighted_integrable fullCap_smooth hT
  have hp : Continuous (fun t => leftPoint T t) := by unfold leftPoint; fun_prop
  exact (zeta_continuous k T _ _ hT (by norm_num)).mul
    ((psi_entire T).continuous.comp hp).continuousOn

theorem full_error_integrable :
    ∀ᶠ T : ℝ in atTop, IntegrableOn (errorDensity T) (Set.Icc T (2*T)) := by
  filter_upwards [leftPoint_strip] with T hs
  have hT : 0 < T := by linarith [hs.1]
  have hp : Continuous (fun t => leftPoint T t) := by unfold leftPoint; fun_prop
  have hv : ContinuousOn (fun t => V T (leftPoint T t)*psi T (leftPoint T t))
      (Set.Icc T (2*T)) := by
    apply ContinuousOn.mul _ ((psi_entire T).continuous.comp hp).continuousOn
    intro t ht
    have hr : 0 < (leftPoint T t).re := by
      simp only [leftPoint,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
        Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_self,add_zero]
      linarith [hs.2.2.1]
    have h1 : leftPoint T t ≠ 1 := by
      intro he
      have hh := congrArg Complex.im he
      simp [leftPoint] at hh
      linarith [ht.1]
    exact (((eta_entire (Real.log T) _).continuousAt.div
      (H_analytic _ hr).continuousAt (H_ne_zero _ hr h1)).comp hp.continuousAt).continuousWithinAt
  have hu := u_continuous T 1 2 hT (by norm_num)
  simp only [one_mul] at hu
  have hi : IntegrableOn (fun t => ‖V T (leftPoint T t)*psi T (leftPoint T t)-
      U T (leftPoint T t)*psi T (leftPoint T t)‖^2) (Set.Icc T (2*T)) :=
    ((hv.sub hu).norm.pow 2).integrableOn_compact isCompact_Icc
  change IntegrableOn (fun t => ‖(V T (leftPoint T t)-U T (leftPoint T t))*
    psi T (leftPoint T t)‖^2) (Set.Icc T (2*T))
  simpa only [sub_mul] using hi

theorem fullError_bound :
    ∀ᶠ T : ℝ in atTop, 0 ≤ fullError T ∧
      fullError T ≤ 7*(transferConstant/Real.log T)^2*
        ∑ k ∈ range 7, derivativeMoment k fullCap T := by
  filter_upwards [difference_left_bound,full_error_integrable,eventually_gt_atTop (0:ℝ)] with T hb hi hT
  refine ⟨div_nonneg (integral_nonneg (fun _ => sq_nonneg _)) hT.le, ?_⟩
  let f := fun t => ∑ k ∈ range 7,
    ‖scaledZeta k T (leftPoint T t)*psi T (leftPoint T t)‖^2*fullCap (t/T)
  have hf : Integrable f := integrable_finsetSum _ (fun k _ => broad_derivative_integrable k T hT)
  have hfn : ∀ t, 0 ≤ f t := fun _ => sum_nonneg (fun _ _ => mul_nonneg (sq_nonneg _) fullCap.nonneg)
  have hh : (∫ t in Set.Icc T (2*T), errorDensity T t) ≤
      7*(transferConstant/Real.log T)^2*∫ t, f t := by
    calc
      _ ≤ ∫ t in Set.Icc T (2*T), 7*(transferConstant/Real.log T)^2*f t := by
        apply setIntegral_mono_on hi (hf.const_mul _).integrableOn measurableSet_Icc
        intro t ht
        have hw := fullCap_one (t/T) (show t/T ∈ Set.Icc (1:ℝ) 2 from
          ⟨(le_div_iff₀ hT).mpr (by linarith [ht.1]), (div_le_iff₀ hT).mpr ht.2⟩)
        simpa only [f,hw,mul_one,errorDensity] using square_error_bound T t (hb t ht)
      _ = 7*(transferConstant/Real.log T)^2*∫ t in Set.Icc T (2*T), f t := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (setIntegral_le_integral hf (Eventually.of_forall hfn)) (by positivity)
  apply (div_le_div_of_nonneg_right hh hT.le).trans_eq
  rw [show (∫ t, f t) = ∑ k ∈ range 7,
    ∫ t, ‖scaledZeta k T (leftPoint T t)*psi T (leftPoint T t)‖^2*fullCap (t/T) from
      integral_finsetSum _ (fun k _ => broad_derivative_integrable k T hT)]
  simp only [derivativeMoment,sum_div,mul_div_assoc]

theorem fullError_tendsto (hb : MajorantDerivativeBounds) :
    Tendsto fullError atTop (nhds 0) := by
  obtain ⟨C,hC,hb⟩ := hb
  have ht : Tendsto (fun T : ℝ => 49*transferConstant^2*C/(Real.log T)^2) atTop (nhds 0) := by
    simpa only [Function.comp_def,div_eq_mul_inv,inv_pow,zero_pow,ne_eq,OfNat.ofNat_ne_zero,
      not_false_eq_true,mul_zero] using
      ((tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).pow 2).const_mul (49*transferConstant^2*C)
  apply squeeze_zero' (fullError_bound.mono (fun _ h => h.1)) ?_ ht
  filter_upwards [fullError_bound,hb] with T hT hbT
  have hh : (∑ k ∈ range 7, derivativeMoment k fullCap T) ≤ 7*C := by
    calc
      _ ≤ ∑ k ∈ range 7, C := sum_le_sum (fun k hk => hbT k (by have := mem_range.mp hk; omega))
      _ = _ := by simp
  exact hT.2.trans ((mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by ring))

theorem endpoint_bound (δ : ℝ) (hδ : 0 < δ) (hd : δ < 1/4) :
    ∀ᶠ T : ℝ in atTop, endpointMoment δ T ≤
      2*smoothedMoment (weight δ hδ) T+2*fullError T := by
  filter_upwards [full_integrable,full_error_integrable,eventually_gt_atTop (0:ℝ)] with T hv he hT
  let s := window (1/2) T \ window (1/2-δ) T
  let f := fun t => ‖U T (leftPoint T t)*psi T (leftPoint T t)‖^2*weight δ hδ (t/T)
  have hf : Integrable f := broad_u_integrable _ (weight_smooth δ hδ hd) T hT
  have he' : IntegrableOn (errorDensity T) (window (1/2) T) := by norm_num [window]; exact he
  have hi : (∫ t in s, density T t) ≤ 2*(∫ t, f t)+2*(∫ t in Set.Icc T (2*T), errorDensity T t) := by
    calc
      _ ≤ ∫ t in s, 2*f t+2*errorDensity T t := by
        apply setIntegral_mono_on (hv.mono_set Set.sdiff_subset)
          ((hf.const_mul 2).integrableOn.add ((he'.mono_set Set.sdiff_subset).const_mul 2))
          (measurableSet_Icc.diff measurableSet_Icc)
        intro t ht
        have hh := WuMomentTransfer.square_difference
          (V T (leftPoint T t)*psi T (leftPoint T t))
          (U T (leftPoint T t)*psi T (leftPoint T t)) 1 (by norm_num)
        have hw := mul_le_mul_of_nonneg_left (endpoint_majorant δ T t hδ hT ht)
          (sq_nonneg ‖U T (leftPoint T t)*psi T (leftPoint T t)‖)
        simp only [one_div_one] at hh
        have ha := le_abs_self (‖V T (leftPoint T t)*psi T (leftPoint T t)‖^2-
          ‖U T (leftPoint T t)*psi T (leftPoint T t)‖^2)
        dsimp [density,f,errorDensity]
        rw [sub_mul]
        nlinarith
      _ = 2*(∫ t in s, f t)+2*(∫ t in s, errorDensity T t) := by
        rw [integral_add (hf.const_mul 2).integrableOn ((he'.mono_set Set.sdiff_subset).const_mul 2),
          integral_const_mul,integral_const_mul]
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_left (setIntegral_le_integral hf
          (Eventually.of_forall (fun _ => mul_nonneg (sq_nonneg _) (weight_nonneg _ _ _)))) (by norm_num))
        (mul_le_mul_of_nonneg_left (setIntegral_mono_set he
          (Eventually.of_forall (fun _ => sq_nonneg _))
          (Eventually.of_forall (fun t ht => by have hh := ht.1; norm_num [window] at hh; exact hh))) (by norm_num))
  exact (div_le_div_of_nonneg_right hi hT.le).trans_eq (by
    dsimp [endpointMoment,smoothedMoment,fullError,s,f]; ring)

/-- The width is selected before T. This theorem does not supply hu or hb. -/
theorem endpointTight_of_localizedMoments (hu : LocalizedUMoments) (hb : MajorantDerivativeBounds) :
    EndpointTight := by
  intro eps heps
  let c := NumericalGate.actual.re
  let δ0 := min (1/4 : ℝ) (eps/(32*(|c|+1)))
  refine ⟨δ0, lt_min (by norm_num) (by positivity), ?_⟩
  intro δ hδ hd _
  have hdq : δ < 1/4 := hd.trans_le (min_le_left _ _)
  have hm := weight_mass δ hδ
  have hc : 2*c*fullMass (weight δ hδ) < eps := by
    have h1 := mul_le_mul_of_nonneg_right (le_abs_self c) hm.1
    have h2 := mul_le_mul_of_nonneg_left hm.2 (abs_nonneg c)
    have h3 := (lt_div_iff₀ (show 0 < 32*(|c|+1) by positivity)).mp
      (hd.trans_le (min_le_right _ _))
    nlinarith [abs_nonneg c]
  have hl := ((hu _ (weight_smooth δ hδ hdq) (weight_nonneg δ hδ)).const_mul 2).add
    ((fullError_tendsto hb).const_mul 2)
  have hl' : Tendsto (fun T => 2*smoothedMoment (weight δ hδ) T+2*fullError T)
      atTop (nhds (2*c*fullMass (weight δ hδ))) := by simpa [c,mul_assoc] using hl
  filter_upwards [endpoint_bound δ hδ hdq,hl'.eventually (gt_mem_nhds hc)] with T hT hh
  exact hT.trans_lt hh

theorem fullMoment_tendsto_of_localizedMoments (hu : LocalizedUMoments) (hb : MajorantDerivativeBounds) :
    Tendsto fullMoment atTop (nhds NumericalGate.actual.re) :=
  fullMoment_tendsto_of_endpointTight (endpointTight_of_localizedMoments hu hb)

#print axioms broad_u_integrable
#print axioms broad_derivative_integrable
#print axioms full_error_integrable
#print axioms fullError_bound
#print axioms fullError_tendsto
#print axioms endpoint_bound
#print axioms endpointTight_of_localizedMoments
#print axioms fullMoment_tendsto_of_localizedMoments
end XiPrime8845.WuEndpointTransfer
