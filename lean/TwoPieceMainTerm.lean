import FengSquareMainTerm

/-! Assembly of the four original two-piece coefficient components.
Both ordered cross terms are retained. Arithmetic convergence is on both
bidiscs; the normalized gcd limit is on witnessBidisc. The same-profile limit
is the existing shiftedFunctional, before q-jets or any counting transfer. -/
noncomputable section
open Filter Topology
namespace XiPrime8845.TwoPieceMainTerm
open PRZZAsymptotic GcdDecomposition ConreyCoefficientBridge FengCoefficientBridge
open ConreyMainTerm
set_option maxHeartbeats 1000000

/-- Independent left and right two-piece profiles, in order 00,02,20,22. -/
def kernel (P Q : PRZZ.Profiles) (A B : ℂ) : ℂ :=
  BetaKernel.H 0 0 A B PRZZAsymptotic.theta (complexify P.conrey) (complexify Q.conrey) +
  BetaKernel.H 0 2 A B PRZZAsymptotic.theta (complexify P.conrey) (complexify Q.feng) +
  BetaKernel.H 2 0 A B PRZZAsymptotic.theta (complexify P.feng) (complexify Q.conrey) +
  BetaKernel.H 2 2 A B PRZZAsymptotic.theta (complexify P.feng) (complexify Q.feng)

def functional (P Q : PRZZ.Profiles) (A B : ℂ) : ℂ :=
  FengMixedMainTerm.dualFunctional (kernel P Q) A B

theorem kernel_self (P : PRZZ.Profiles) (A B : ℂ) :
    kernel P P A B = BetaKernel.fourTerms A B PRZZAsymptotic.theta
      (complexify P.conrey) (complexify P.feng) := rfl

/-- Exact identification with the functional used by the finite jet evaluator. -/
theorem functional_self (P : PRZZ.Profiles) (A B : ℂ) :
    functional P P A B = BetaKernel.shiftedFunctional A B PRZZAsymptotic.theta
      (complexify P.conrey) (complexify P.feng) := rfl

theorem functional_four (P Q : PRZZ.Profiles) (A B : ℂ) :
    functional P Q A B =
      FengMixedMainTerm.functional 0 0 P.conrey Q.conrey A B +
      FengMixedMainTerm.functional 0 2 P.conrey Q.feng A B +
      FengMixedMainTerm.functional 2 0 P.feng Q.conrey A B +
      FengMixedMainTerm.functional 2 2 P.feng Q.feng A B := by
  unfold functional kernel FengMixedMainTerm.functional FengMixedMainTerm.dualFunctional
  ring

/-- Finite identity for every T; no asymptotic or endpoint assumption. -/
theorem normalized_gcd_four (P Q : PRZZ.Profiles) (θ T : ℝ)
    (Phi : ℝ → ℝ) (A B : ℂ) :
    PRZZ.gcdMainTerm P Q θ T Phi A B/(T:ℂ) =
      PRZZ.gcdMainTerm (profile P.conrey) (profile Q.conrey) θ T Phi A B/(T:ℂ) +
      PRZZ.gcdMainTerm (profile P.conrey) (fengProfile Q.feng) θ T Phi A B/(T:ℂ) +
      PRZZ.gcdMainTerm (fengProfile P.feng) (profile Q.conrey) θ T Phi A B/(T:ℂ) +
      PRZZ.gcdMainTerm (fengProfile P.feng) (fengProfile Q.feng) θ T Phi A B/(T:ℂ) := by
  rw [gcdMainTerm_four]
  ring

theorem scaledArithmetic_twoBidiscs (P Q : PRZZ.Profiles)
    (hPc : P.conrey.eval 0 = 0) (hPf : P.feng.eval 0 = 0)
    (hQc : Q.conrey.eval 0 = 0) (hQf : Q.feng.eval 0 = 0) :
    TendstoUniformlyOn
      (fun T (p : ℂ × ℂ) => scaledArithmetic P Q PRZZAsymptotic.theta T p.1 p.2)
      (fun p => kernel P Q p.1 p.2) atTop ElementaryGcd.twoBidiscs := by
  have h := (((ConreyCoefficientBridge.scaledArithmetic_twoBidiscs P.conrey Q.conrey hPc hQc).add
    (FengCrossCoefficient.scaledArithmetic20_twoBidiscs P.feng Q.conrey hPf hQc)).add
    (FengCrossCoefficient.scaledArithmetic02_twoBidiscs P.conrey Q.feng hPc hQf)).add
    (FengSquareCoefficient.scaledArithmetic22_twoBidiscs P.feng Q.feng hPf hQf)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h eps heps] with T hT
  intro p hp
  rw [scaledArithmetic_four]
  simpa only [Pi.add_def,kernel,add_comm,add_left_comm,add_assoc] using hT p hp

theorem scaledArithmetic_reflected (P Q : PRZZ.Profiles)
    (hPc : P.conrey.eval 0 = 0) (hPf : P.feng.eval 0 = 0)
    (hQc : Q.conrey.eval 0 = 0) (hQf : Q.feng.eval 0 = 0) :
    TendstoUniformlyOn
      (fun T (p : ℂ × ℂ) => scaledArithmetic P Q PRZZAsymptotic.theta T (-p.2) (-p.1))
      (fun p => kernel P Q (-p.2) (-p.1)) atTop witnessBidisc :=
  ElementaryGcd.uniform_reflected (scaledArithmetic_twoBidiscs P Q hPc hPf hQc hQf)

/-- Literal original two-piece gcd main term, not a separately chosen model.
The ordered cross terms are added, never doubled at unequal shifts. -/
theorem normalized_gcd_uniform (P Q : PRZZ.Profiles)
    (hPc : P.conrey.eval 0 = 0) (hPf : P.feng.eval 0 = 0)
    (hQc : Q.conrey.eval 0 = 0) (hQf : Q.feng.eval 0 = 0)
    (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi) :
    TendstoUniformlyOn
      (fun T (p : ℂ × ℂ) => PRZZ.gcdMainTerm P Q PRZZAsymptotic.theta T Phi p.1 p.2/(T:ℂ))
      (fun p => functional P Q p.1 p.2 * weightMass Phi) atTop witnessBidisc := by
  have h00 : TendstoUniformlyOn
      (fun T (p : ℂ × ℂ) => PRZZ.gcdMainTerm (profile P.conrey) (profile Q.conrey)
        PRZZAsymptotic.theta T Phi p.1 p.2/(T:ℂ))
      (fun p => FengMixedMainTerm.functional 0 0 P.conrey Q.conrey p.1 p.2 * weightMass Phi)
      atTop witnessBidisc :=
    ConreyMainTerm.normalized_gcdMainTerm_uniform P.conrey Q.conrey hPc hQc Phi hPhi
  have h := ((h00.add (FengMixedMainTerm.normalized_gcd02_uniform P.conrey Q.feng hPc hQf Phi hPhi)).add
    (FengMixedMainTerm.normalized_gcd20_uniform P.feng Q.conrey hPf hQc Phi hPhi)).add
    (FengSquareMainTerm.normalized_gcd22_uniform P.feng Q.feng hPf hQf Phi hPhi)
  simpa only [Pi.add_def,← normalized_gcd_four,← add_mul,← functional_four] using h

theorem normalized_self_uniform (P : PRZZ.Profiles)
    (hPc : P.conrey.eval 0 = 0) (hPf : P.feng.eval 0 = 0)
    (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi) :
    TendstoUniformlyOn
      (fun T (p : ℂ × ℂ) => PRZZ.gcdMainTerm P P PRZZAsymptotic.theta T Phi p.1 p.2/(T:ℂ))
      (fun p => BetaKernel.shiftedFunctional p.1 p.2 PRZZAsymptotic.theta
        (complexify P.conrey) (complexify P.feng) * weightMass Phi)
      atTop witnessBidisc := by
  simpa only [functional_self] using normalized_gcd_uniform P P hPc hPf hPc hPf Phi hPhi

/-- The fixed witness reaches the actual full shifted functional. This theorem
uses no PRZZ moment axiom; moment and counting transfers remain separate. -/
theorem normalized_witness_uniform (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi) :
    TendstoUniformlyOn (normalizedGcd Phi)
      (fun p => BetaKernel.shiftedFunctional p.1 p.2 PRZZAsymptotic.theta
        (complexify PRZZ.witness.conrey) (complexify PRZZ.witness.feng) * weightMass Phi)
      atTop witnessBidisc :=
  normalized_self_uniform PRZZ.witness PRZZ.witness_endpoints.1 PRZZ.witness_endpoints.2.1 Phi hPhi

theorem normalized_witness_tendsto (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi)
    (p : ℂ × ℂ) (hp : p ∈ witnessBidisc) :
    Tendsto (fun T => normalizedGcd Phi T p) atTop
      (nhds (BetaKernel.shiftedFunctional p.1 p.2 PRZZAsymptotic.theta
        (complexify PRZZ.witness.conrey) (complexify PRZZ.witness.feng) * weightMass Phi)) :=
  (normalized_witness_uniform Phi hPhi).tendsto_at hp

#print axioms kernel_self
#print axioms functional_self
#print axioms functional_four
#print axioms normalized_gcd_four
#print axioms scaledArithmetic_twoBidiscs
#print axioms scaledArithmetic_reflected
#print axioms normalized_gcd_uniform
#print axioms normalized_self_uniform
#print axioms normalized_witness_uniform
#print axioms normalized_witness_tendsto
end XiPrime8845.TwoPieceMainTerm
