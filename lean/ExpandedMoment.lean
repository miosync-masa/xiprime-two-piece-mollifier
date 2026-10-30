import ExpandedMainTerm
import ExpandedRegularity
import TwoPieceMoment

/-! Expanded-support uniform moment and Cauchy jets. LocalizedEstimate is the
sole explicit analytic estimate input; no localized axiom is introduced. -/
noncomputable section
open scoped BigOperators
open Filter Topology
namespace XiPrime8845.ExpandedMoment
open PRZZAsymptotic ConreyMainTerm ConreyCoefficientBridge FiniteJet IntegralJet
open CauchyJetTransfer
set_option maxHeartbeats 1000000

def kernel (A B : ℂ) : ℂ :=
  BetaKernel.shiftedFunctional A B PRZZAsymptotic.theta
    (complexify PRZZ.witness.conrey) (complexify PRZZ.witness.feng)

/-- All four arithmetic components enter before the PRZZ error is transferred. -/
theorem normalizedMoment_uniform (hlocal : PRZZLocalization.LocalizedEstimate) (Phi : ℝ → ℝ) (hPhi : PRZZLocalization.SmoothWeightOn (1/2) (5/2) Phi) :
    TendstoUniformlyOn (normalizedMoment Phi)
      (fun p => kernel p.1 p.2*(PRZZLocalization.fullMass Phi:ℂ)) atTop witnessBidisc :=
  ExpandedMainTerm.normalizedMoment_uniform hlocal Phi hPhi

theorem normalizedMoment_tendsto (hlocal : PRZZLocalization.LocalizedEstimate) (Phi : ℝ → ℝ) (hPhi : PRZZLocalization.SmoothWeightOn (1/2) (5/2) Phi)
    (p : ℂ × ℂ) (hp : p ∈ witnessBidisc) :
    Tendsto (fun T => normalizedMoment Phi T p) atTop
      (nhds (kernel p.1 p.2*(PRZZLocalization.fullMass Phi:ℂ))) :=
  (normalizedMoment_uniform hlocal Phi hPhi).tendsto_at hp

theorem normalizedMoment_regular (Phi : ℝ → ℝ) (hPhi : PRZZLocalization.SmoothWeightOn (1/2) (5/2) Phi)
    (T : ℝ) (hT : 1 < T) :
    RegularNegative (fun x y => normalizedMoment Phi T (x,y)) :=
  regularNegative_of_smooth _ ((ExpandedRegularity.twistedMoment_smooth PRZZ.witness PRZZ.witness
    PRZZAsymptotic.theta T Phi hPhi hT).div_const (T:ℂ))

theorem kernel_regular : RegularNegative kernel :=
  shiftedFunctional_regular _ _ _

theorem limit_regular (Phi : ℝ → ℝ) :
    RegularNegative (fun x y => kernel x y*(PRZZLocalization.fullMass Phi:ℂ)) := by
  constructor
  · intro x y hx hy n
    exact (kernel_regular.1 x y hx hy n).mul contDiffAt_const
  · intro y hy j x hx n
    simp only [jet,iteratedDeriv_mul_const_field, mul_div_right_comm]
    exact (kernel_regular.2 y hy j x hx n).mul contDiffAt_const

/-- Arbitrary independent orders, hence the full 0..6 by 0..6 witness jet. -/
theorem normalizedMoment_jet₂_tendsto (hlocal : PRZZLocalization.LocalizedEstimate) (Phi : ℝ → ℝ) (hPhi : PRZZLocalization.SmoothWeightOn (1/2) (5/2) Phi) (a b : ℕ) :
    Tendsto (fun T => jet₂ a b (fun x y => normalizedMoment Phi T (x,y)) (-R) (-R))
      atTop (nhds (jet₂ a b kernel (-R) (-R)*(PRZZLocalization.fullMass Phi:ℂ))) := by
  have h := jet₂_tendsto (fun T x y => normalizedMoment Phi T (x,y))
    (fun x y => kernel x y*(PRZZLocalization.fullMass Phi:ℂ)) (by
      filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
      exact normalizedMoment_regular Phi hPhi T hT)
    (limit_regular Phi) (normalizedMoment_uniform hlocal Phi hPhi) a b
  simpa only [jet₂,jet,iteratedDeriv_mul_const_field,mul_div_right_comm] using h

/-- Finite differential contraction of the actual normalized moment. -/
theorem normalizedMoment_contract_tendsto (hlocal : PRZZLocalization.LocalizedEstimate) (Phi : ℝ → ℝ) (hPhi : PRZZLocalization.SmoothWeightOn (1/2) (5/2) Phi)
    (D : ℕ) (op : ℕ → ℂ) :
    Tendsto (fun T => contract₂ D op (fun x y => normalizedMoment Phi T (x,y)) (-R) (-R))
      atTop (nhds (contract₂ D op kernel (-R) (-R)*(PRZZLocalization.fullMass Phi:ℂ))) := by
  have hc : (-(R:ℂ)).re < 0 := by simpa using neg_neg_of_pos radius_pos
  have h := tendsto_finsetSum (Finset.range (D+1)) (fun a _ =>
    tendsto_finsetSum (Finset.range (D+1)) (fun b _ =>
      (normalizedMoment_jet₂_tendsto hlocal Phi hPhi a b).const_mul (op a*op b)))
  have he : (fun T => contract₂ D op (fun x y => normalizedMoment Phi T (x,y)) (-R) (-R)) =ᶠ[atTop]
      (fun T => ∑ a ∈ Finset.range (D+1), ∑ b ∈ Finset.range (D+1),
        op a*op b*jet₂ a b (fun x y => normalizedMoment Phi T (x,y)) (-R) (-R)) := by
    filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
    exact contract₂_rect D op _ (-R) (-R) (fun b _ =>
      (normalizedMoment_regular Phi hPhi T hT).2 (-R) hc b (-R) hc D)
  rw [contract₂_rect D op kernel (-R) (-R) (fun b _ => kernel_regular.2 (-R) hc b (-R) hc D)]
  apply Tendsto.congr' he.symm
  simpa only [Finset.sum_mul,mul_assoc] using h

/-- The limiting contraction is the existing exact (untruncated) K2 evaluator.
In particular D=6 is permitted; numerical truncation is a separate theorem. -/
theorem normalizedMoment_exactEvaluator_tendsto (hlocal : PRZZLocalization.LocalizedEstimate) (Phi : ℝ → ℝ) (hPhi : PRZZLocalization.SmoothWeightOn (1/2) (5/2) Phi)
    (D : ℕ) (q : ℕ → ℂ) :
    Tendsto (fun T => contract₂ D (opMinus q)
      (fun x y => normalizedMoment Phi T (x,y)) (-R) (-R))
      atTop (nhds (exactEvaluator D q (-R) (-R) PRZZAsymptotic.theta
        (complexify PRZZ.witness.conrey) (complexify PRZZ.witness.feng)*(PRZZLocalization.fullMass Phi:ℂ))) := by
  have hn : (-(R:ℂ))+(-(R:ℂ)) ≠ 0 := by
    have hr : (R:ℂ) ≠ 0 := by exact_mod_cast radius_pos.ne'
    intro h
    apply hr
    linear_combination -h/2
  rw [← K2_exact_evaluator D q (-R) (-R) hn]
  exact normalizedMoment_contract_tendsto hlocal Phi hPhi D (opMinus q)

#print axioms normalizedMoment_uniform
#print axioms normalizedMoment_tendsto
#print axioms normalizedMoment_regular
#print axioms kernel_regular
#print axioms limit_regular
#print axioms normalizedMoment_jet₂_tendsto
#print axioms normalizedMoment_contract_tendsto
#print axioms normalizedMoment_exactEvaluator_tendsto
end XiPrime8845.ExpandedMoment


