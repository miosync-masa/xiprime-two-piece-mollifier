import ZetaMomentPolynomial
import TwoPieceMoment

/-! Concrete zeta-derivative moment limits for the fixed two-piece witness.
The finite-T integral identity is unconditional. Only the convergence uses
the previously named PRZZ input through TwoPieceMoment. No zero-counting
adapter or final zero-proportion conclusion is asserted here. -/
noncomputable section
open scoped BigOperators
open Filter Topology
namespace XiPrime8845.ZetaMomentMainTerm
open ZetaMomentPolynomial FiniteJet PRZZAsymptotic ConreyMainTerm ConreyCoefficientBridge

theorem normalizedMoment_contract_eq (D : ℕ) (q : ℕ → ℂ)
    (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi) (T : ℝ) (hT : 1 < T) :
    contract₂ D (opMinus q) (fun x y => normalizedMoment Phi T (x,y)) (-R) (-R) =
      moment D q PRZZ.witness PRZZ.witness PRZZAsymptotic.theta T Phi (-R) (-R) := by
  have hc : (-(R:ℂ)).re < 0 := by simpa using neg_neg_of_pos radius_pos
  exact contract₂_eq_moment D q _ _ _ T Phi hPhi hT _ _ hc hc

/-- The two explicit finite zeta-derivative sums, with all original mollifier
coefficients, converge to the untruncated exact kernel evaluator. -/
theorem moment_exactEvaluator_tendsto (D : ℕ) (q : ℕ → ℂ)
    (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi) :
    Tendsto (fun T => moment D q PRZZ.witness PRZZ.witness PRZZAsymptotic.theta T Phi (-R) (-R))
      atTop (nhds (IntegralJet.exactEvaluator D q (-R) (-R) PRZZAsymptotic.theta
        (complexify PRZZ.witness.conrey) (complexify PRZZ.witness.feng)*weightMass Phi)) := by
  apply (TwoPieceMoment.normalizedMoment_exactEvaluator_tendsto Phi hPhi D q).congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
  exact normalizedMoment_contract_eq D q Phi hPhi T hT

/-- For real operator coefficients this is the actual nonnegative integrand
|q(-d/ds/log T) zeta(s) M(1/2+it)|^2, on s=1/2-R/log T+it.
Phi itself is not assumed nonnegative. -/
theorem squareMoment_exactEvaluator_tendsto (D : ℕ) (q : ℕ → ℝ)
    (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi) :
    Tendsto (fun T => squareMoment D q PRZZ.witness PRZZAsymptotic.theta T Phi (1/2-R/Real.log T))
      atTop (nhds ((IntegralJet.exactEvaluator D (fun n => (q n:ℂ)) (-R) (-R) PRZZAsymptotic.theta
        (complexify PRZZ.witness.conrey) (complexify PRZZ.witness.feng)*weightMass Phi).re)) := by
  have h := (Complex.continuous_re.tendsto _).comp
    (moment_exactEvaluator_tendsto D (fun n => (q n:ℂ)) Phi hPhi)
  simpa only [Function.comp_def,show ∀ T : ℝ, moment D (fun n => (q n:ℂ))
    PRZZ.witness PRZZ.witness PRZZAsymptotic.theta T Phi (-(R:ℂ)) (-(R:ℂ)) =
      (squareMoment D q PRZZ.witness PRZZAsymptotic.theta T Phi (1/2-R/Real.log T):ℂ) from
        fun T => by simpa only [Complex.ofReal_neg,neg_div,sub_eq_add_neg] using
          moment_eq_square D q PRZZ.witness PRZZAsymptotic.theta T (-R) Phi,
    Complex.ofReal_re] using h

#print axioms normalizedMoment_contract_eq
#print axioms moment_exactEvaluator_tendsto
#print axioms squareMoment_exactEvaluator_tendsto
end XiPrime8845.ZetaMomentMainTerm

