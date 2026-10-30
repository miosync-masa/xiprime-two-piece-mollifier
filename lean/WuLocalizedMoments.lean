import ExpandedZetaPolynomial
import ExpandedMoment
import WuEndpointTransfer

/-! Suppliers of the expanded-support U moment and seven derivative bounds.
All limits below are conditional on LocalizedEstimate, a proposition rather
than a new axiom. The endpoint conclusion uses Stirling only on [T,2T]. -/
noncomputable section
open scoped BigOperators
open Filter Topology
namespace XiPrime8845.WuLocalizedMoments
open ZetaMomentPolynomial FiniteJet PRZZAsymptotic ConreyMainTerm ConreyCoefficientBridge

theorem normalizedMoment_contract_eq (D : ℕ) (q : ℕ → ℂ)
    (Phi : ℝ → ℝ) (hPhi : PRZZLocalization.SmoothWeightOn (1/2) (5/2) Phi) (T : ℝ) (hT : 1 < T) :
    contract₂ D (opMinus q) (fun x y => normalizedMoment Phi T (x,y)) (-R) (-R) =
      moment D q PRZZ.witness PRZZ.witness PRZZAsymptotic.theta T Phi (-R) (-R) := by
  have hc : (-(R:ℂ)).re < 0 := by simpa using neg_neg_of_pos radius_pos
  exact ExpandedZetaPolynomial.contract₂_eq_moment D q _ _ _ T Phi hPhi hT _ _ hc hc

/-- The two explicit finite zeta-derivative sums, with all original mollifier
coefficients, converge to the untruncated exact kernel evaluator. -/
theorem moment_exactEvaluator_tendsto (hlocal : PRZZLocalization.LocalizedEstimate) (D : ℕ) (q : ℕ → ℂ)
    (Phi : ℝ → ℝ) (hPhi : PRZZLocalization.SmoothWeightOn (1/2) (5/2) Phi) :
    Tendsto (fun T => moment D q PRZZ.witness PRZZ.witness PRZZAsymptotic.theta T Phi (-R) (-R))
      atTop (nhds (IntegralJet.exactEvaluator D q (-R) (-R) PRZZAsymptotic.theta
        (complexify PRZZ.witness.conrey) (complexify PRZZ.witness.feng)*(PRZZLocalization.fullMass Phi:ℂ))) := by
  apply (ExpandedMoment.normalizedMoment_exactEvaluator_tendsto hlocal Phi hPhi D q).congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
  exact normalizedMoment_contract_eq D q Phi hPhi T hT

/-- For real operator coefficients this is the actual nonnegative integrand
|q(-d/ds/log T) zeta(s) M(1/2+it)|^2, on s=1/2-R/log T+it.
Phi itself is not assumed nonnegative. -/
theorem squareMoment_exactEvaluator_tendsto (hlocal : PRZZLocalization.LocalizedEstimate) (D : ℕ) (q : ℕ → ℝ)
    (Phi : ℝ → ℝ) (hPhi : PRZZLocalization.SmoothWeightOn (1/2) (5/2) Phi) :
    Tendsto (fun T => squareMoment D q PRZZ.witness PRZZAsymptotic.theta T Phi (1/2-R/Real.log T))
      atTop (nhds ((IntegralJet.exactEvaluator D (fun n => (q n:ℂ)) (-R) (-R) PRZZAsymptotic.theta
        (complexify PRZZ.witness.conrey) (complexify PRZZ.witness.feng)*(PRZZLocalization.fullMass Phi:ℂ)).re)) := by
  have h := (Complex.continuous_re.tendsto _).comp
    (moment_exactEvaluator_tendsto hlocal D (fun n => (q n:ℂ)) Phi hPhi)
  simpa only [Function.comp_def,show ∀ T : ℝ, moment D (fun n => (q n:ℂ))
    PRZZ.witness PRZZ.witness PRZZAsymptotic.theta T Phi (-(R:ℂ)) (-(R:ℂ)) =
      (squareMoment D q PRZZ.witness PRZZAsymptotic.theta T Phi (1/2-R/Real.log T):ℂ) from
        fun T => by simpa only [Complex.ofReal_neg,neg_div,sub_eq_add_neg] using
          moment_eq_square D q PRZZ.witness PRZZAsymptotic.theta T (-R) Phi,
    Complex.ofReal_re] using h


open PRZZLocalization WuAuxiliary WitnessMomentBound

theorem smoothedMoment_tendsto (hlocal : LocalizedEstimate) (Phi : ℝ → ℝ)
    (hPhi : SmoothWeightOn (1/2) (5/2) Phi) :
    Tendsto (smoothedMoment Phi) atTop (nhds (NumericalGate.actual.re*fullMass Phi)) := by
  change Tendsto (fun T => smoothedMoment Phi T) atTop _
  have h := squareMoment_exactEvaluator_tendsto hlocal 6 qReal Phi hPhi
  simpa only [smoothedMoment_eq,witnessMoment,evaluator_eq_actual,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero] using h

theorem derivativeMoments_bounded (hlocal : LocalizedEstimate) (Phi : ℝ → ℝ)
    (hPhi : SmoothWeightOn (1/2) (5/2) Phi) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ k ≤ 6, |derivativeMoment k Phi T| ≤ C := by
  have hb (k : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, |derivativeMoment k Phi T| ≤ C := by
    have h := squareMoment_exactEvaluator_tendsto hlocal k
      (fun n => if n=k then 1 else 0) Phi hPhi
    simp only [← derivativeMoment_eq] at h
    obtain ⟨c, hc⟩ : ∃ c : ℝ, Tendsto (fun T => derivativeMoment k Phi T) atTop (nhds c) := ⟨_, h⟩
    refine ⟨|c|+1, by positivity, ?_⟩
    exact (hc.abs.eventually (gt_mem_nhds (lt_add_one _))).mono (fun T hT => hT.le)
  choose c hc hbound using hb
  refine ⟨∑ k ∈ Finset.range 7, c k, ?_, ?_⟩
  · exact Finset.sum_pos (fun k _ => hc k) (by simp)
  have hall : ∀ᶠ T : ℝ in atTop, ∀ k ∈ Finset.range 7, |derivativeMoment k Phi T| ≤ c k :=
    (eventually_all_finset _).mpr (fun k _ => hbound k)
  filter_upwards [hall] with T hT
  intro k hk
  have hk' : k ∈ Finset.range 7 := Finset.mem_range.mpr (by omega)
  exact (hT k hk').trans (Finset.single_le_sum (fun j _ => (hc j).le) hk')


theorem localizedUMoments (hlocal : LocalizedEstimate) :
    WuEndpointTransfer.LocalizedUMoments :=
  fun Phi hPhi _ => smoothedMoment_tendsto hlocal Phi hPhi

theorem majorantDerivativeBounds (hlocal : LocalizedEstimate) :
    WuEndpointTransfer.MajorantDerivativeBounds := by
  obtain ⟨C,hC,h⟩ := derivativeMoments_bounded hlocal SmoothEndpoint.fullCap SmoothEndpoint.fullCap_smooth
  refine ⟨C,hC.le,?_⟩
  filter_upwards [h] with T hT
  intro k hk
  exact (le_abs_self _).trans (hT k hk)

theorem endpointTight (hlocal : LocalizedEstimate) : WuUnsmoothing.EndpointTight :=
  WuEndpointTransfer.endpointTight_of_localizedMoments
    (localizedUMoments hlocal) (majorantDerivativeBounds hlocal)

theorem fullMoment_tendsto (hlocal : LocalizedEstimate) :
    Tendsto WuUnsmoothing.fullMoment atTop (nhds NumericalGate.actual.re) :=
  WuEndpointTransfer.fullMoment_tendsto_of_localizedMoments
    (localizedUMoments hlocal) (majorantDerivativeBounds hlocal)

/-- An eventual cap for the literal unsmoothed [T,2T] V*psi moment.
This is still conditional on localization and is not a zero-counting result. -/
theorem fullMoment_eventually_lt (hlocal : LocalizedEstimate) :
    ∀ᶠ T : ℝ in atTop, WuUnsmoothing.fullMoment T < countingCap := by
  exact (fullMoment_tendsto hlocal).eventually (gt_mem_nhds
    (LogarithmicBudget.actual_le_cap.trans_lt (by
      norm_num [LogarithmicBudget.certifiedCap,countingCap])))

#print axioms normalizedMoment_contract_eq
#print axioms moment_exactEvaluator_tendsto
#print axioms squareMoment_exactEvaluator_tendsto
#print axioms smoothedMoment_tendsto
#print axioms derivativeMoments_bounded
#print axioms localizedUMoments
#print axioms majorantDerivativeBounds
#print axioms endpointTight
#print axioms fullMoment_tendsto
#print axioms fullMoment_eventually_lt
end XiPrime8845.WuLocalizedMoments

