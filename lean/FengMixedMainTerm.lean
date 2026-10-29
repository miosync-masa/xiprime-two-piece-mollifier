import FengCrossCoefficient
import ConreyMainTerm
import IntegralJet

/-! Uniform limits of the original ordered Conrey/Feng normalized gcd terms.
The arithmetic suppliers hold on both reflected bidiscs; the pole/height
composition is on witnessBidisc, away from A+B=0. No PRZZ moment axiom,
K22 asymptotic, or counting result is used. -/
noncomputable section
open Filter Topology MeasureTheory
namespace XiPrime8845.FengMixedMainTerm
open PRZZAsymptotic GcdDecomposition ConreyCoefficientBridge
open FengCoefficientBridge FengCrossCoefficient ConreyMainTerm
set_option maxHeartbeats 1000000

/-- Joint continuity of the integrand supplies a common bound on a compact
shift ball and the whole integration interval, including its endpoints. -/
theorem monomial_bounded (e f : ℤ) (n : ℕ) (θ C : ℝ) (hθ : 0 < θ)
    (P G : Polynomial ℂ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ A B : ℂ, ‖A‖ ≤ C → ‖B‖ ≤ C →
      ‖BetaKernel.monomialIntegral A B θ P G e f n‖ ≤ M := by
  let integrand := fun p : (ℂ × ℂ) × ℝ =>
    (p.2:ℂ)^(n-1)/((n-1).factorial:ℂ) *
      BetaKernel.D e p.1.1 θ (θ-p.2) P * BetaKernel.D f p.1.2 θ (θ-p.2) G
  have hD (k : ℤ) (F : Polynomial ℂ) :
      Continuous (fun p : ℂ × ℝ => BetaKernel.D k p.1 θ p.2 F) := by
    simpa only [IntegralJet.jet_zero] using IntegralJet.operator_jet_continuous k 0 θ F
  have hc : Continuous integrand := by
    have he : Continuous (fun p : (ℂ × ℂ) × ℝ =>
        BetaKernel.D e p.1.1 θ (θ-p.2) P) := (hD e P).comp
      ((continuous_fst.fst).prodMk (continuous_const.sub continuous_snd))
    have hf : Continuous (fun p : (ℂ × ℂ) × ℝ =>
        BetaKernel.D f p.1.2 θ (θ-p.2) G) := (hD f G).comp
      ((continuous_fst.snd).prodMk (continuous_const.sub continuous_snd))
    exact ((by fun_prop : Continuous (fun p : (ℂ × ℂ) × ℝ =>
      (p.2:ℂ)^(n-1)/((n-1).factorial:ℂ))).mul he).mul hf
  obtain ⟨M,hM⟩ := (((isCompact_closedBall (0:ℂ) C).prod
    (isCompact_closedBall (0:ℂ) C)).prod (isCompact_Icc (a:=(0:ℝ)) (b:=θ))).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max 0 M*θ,mul_nonneg (le_max_left _ _) hθ.le,?_⟩
  intro A B hA hB
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=(0:ℝ)) (b:=θ) (C:=max 0 M) (fun v hv => show ‖integrand ((A,B),v)‖ ≤ max 0 M from by
      apply (hM ((A,B),v) ?_).trans (le_max_right _ _)
      rw [Set.uIoc_of_le hθ.le] at hv
      exact ⟨⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using hA,
        by simpa only [Metric.mem_closedBall,dist_zero_right] using hB⟩,hv.1.le,hv.2⟩)
  simpa only [BetaKernel.monomialIntegral,integrand,sub_zero,abs_of_pos hθ] using hi

theorem H02_bounded (P G : Polynomial ℂ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ ElementaryGcd.twoBidiscs,
      ‖BetaKernel.H 0 2 p.1 p.2 PRZZAsymptotic.theta P G‖ ≤ M := by
  have hθ : 0 < PRZZAsymptotic.theta := by norm_num [PRZZAsymptotic.theta]
  obtain ⟨M,hM,hm⟩ := monomial_bounded 1 1 3 PRZZAsymptotic.theta (5*R/4) hθ P G
  obtain ⟨N,hN,hn⟩ := monomial_bounded 1 0 2 PRZZAsymptotic.theta (5*R/4) hθ P G
  obtain ⟨Q,hQ,hq⟩ := monomial_bounded 1 (-1) 1 PRZZAsymptotic.theta (5*R/4) hθ P G
  refine ⟨(M+2*N+Q)/PRZZAsymptotic.theta^2,by positivity,?_⟩
  intro p hp
  have hs := ShiftedMobius.twoBidiscs_norm p hp
  rw [BetaKernel.H,BetaKernel.assemble02,norm_div]
  simp only [Nat.zero_add,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hθ]
  apply div_le_div_of_nonneg_right _ (sq_nonneg PRZZAsymptotic.theta)
  apply (norm_add_le _ _).trans
  apply add_le_add _ (hq _ _ hs.1 hs.2)
  apply (norm_sub_le _ _).trans
  apply add_le_add (hm _ _ hs.1 hs.2)
  have htwo : ‖(2:ℂ)‖ = (2:ℝ) := by norm_num
  rw [norm_mul,htwo]
  exact mul_le_mul_of_nonneg_left (hn _ _ hs.1 hs.2) (by norm_num : (0:ℝ) ≤ 2)

theorem H20_bounded (G P : Polynomial ℂ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ ElementaryGcd.twoBidiscs,
      ‖BetaKernel.H 2 0 p.1 p.2 PRZZAsymptotic.theta G P‖ ≤ M := by
  obtain ⟨M,hM,hm⟩ := H02_bounded P G
  refine ⟨M,hM,?_⟩
  intro p hp
  rw [← BetaKernel.H02_swap]
  exact hm (p.2,p.1) (swap_mem_twoBidiscs p hp)

/-- Direct and dual evaluation of an ordered arithmetic kernel. -/
def dualFunctional (H : ℂ → ℂ → ℂ) (A B : ℂ) : ℂ :=
  (H A B-Complex.exp (-A-B)*H (-B) (-A))/(A+B)

/-- Generic transfer from the actual scaled coefficient sum. Both arithmetic
domains and a bounded limiting kernel are explicit inputs, not new axioms.
No positivity or unit-mass assumption is imposed on the fixed smooth weight. -/
theorem normalized_gcd_uniform_of_arithmetic (P Q : PRZZ.Profiles) (H : ℂ → ℂ → ℂ)
    (ha : TendstoUniformlyOn
      (fun T (p : ℂ × ℂ) => scaledArithmetic P Q PRZZAsymptotic.theta T p.1 p.2)
      (fun p => H p.1 p.2) atTop ElementaryGcd.twoBidiscs)
    (hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ ElementaryGcd.twoBidiscs, ‖H p.1 p.2‖ ≤ M)
    (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi) :
    TendstoUniformlyOn
      (fun T (p : ℂ × ℂ) => PRZZ.gcdMainTerm P Q PRZZAsymptotic.theta T Phi p.1 p.2/(T:ℂ))
      (fun p => dualFunctional H p.1 p.2 * weightMass Phi) atTop witnessBidisc := by
  obtain ⟨M,hM,hMb⟩ := hb
  obtain ⟨Z,hZ,hZb⟩ := reciprocal_bounded
  have hdirect := uniform_mul_bounded ZetaPoleScaling.direct_pole_on_bidisc
    (ha.mono (fun _ hp => Or.inl hp))
    ⟨Z,hZ,hZb⟩ ⟨M,hM,fun p hp => hMb p (Or.inl hp)⟩
  have hdual := uniform_mul_bounded ZetaPoleScaling.dual_pole_on_bidisc
    (ElementaryGcd.uniform_reflected ha)
    ⟨Z,hZ,fun p hp => by simpa only [norm_neg] using hZb p hp⟩
    ⟨M,hM,fun p hp => hMb (ElementaryGcd.reflect p) (Or.inr ⟨p,hp,rfl⟩)⟩
  have hdirect' := uniform_mul_bounded hdirect (mass_uniform Phi)
    ⟨Z*M,mul_nonneg hZ hM,fun p hp => by
      rw [norm_mul]; exact mul_le_mul (hZb p hp) (hMb p (Or.inl hp)) (norm_nonneg _) hZ⟩
    ⟨‖weightMass Phi‖,norm_nonneg _,fun _ _ => le_rfl⟩
  have hdual' := uniform_mul_bounded hdual (height_uniform Phi hPhi)
    ⟨Z*M,mul_nonneg hZ hM,fun p hp => by
      rw [norm_mul,norm_neg]
      exact mul_le_mul (hZb p hp)
        (hMb (ElementaryGcd.reflect p) (Or.inr ⟨p,hp,rfl⟩)) (norm_nonneg _) hZ⟩
    (height_limit_bounded Phi)
  have hsum := hdirect'.add hdual'
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hsum eps heps,
    eventually_gt_atTop (1:ℝ)] with T hh hT
  intro p hp
  have h := hh p hp
  simp only [Pi.add_apply] at h
  rw [normalized_gcd_split P Q PRZZAsymptotic.theta T Phi hPhi hT]
  convert h using 1
  congr 1
  unfold dualFunctional ElementaryGcd.reflect
  ring

def functional (l m : ℕ) (P G : Polynomial ℝ) (A B : ℂ) : ℂ :=
  dualFunctional (fun A B => BetaKernel.H l m A B PRZZAsymptotic.theta (complexify P) (complexify G)) A B

theorem normalized_gcd02_uniform (P G : Polynomial ℝ)
    (hP : P.eval 0 = 0) (hG : G.eval 0 = 0)
    (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi) :
    TendstoUniformlyOn
      (fun T (p : ℂ × ℂ) => PRZZ.gcdMainTerm (profile P) (fengProfile G) PRZZAsymptotic.theta T Phi p.1 p.2/(T:ℂ))
      (fun p => functional 0 2 P G p.1 p.2 * weightMass Phi) atTop witnessBidisc :=
  normalized_gcd_uniform_of_arithmetic _ _ _
    (scaledArithmetic02_twoBidiscs P G hP hG)
    (H02_bounded (complexify P) (complexify G)) Phi hPhi

theorem normalized_gcd20_uniform (G P : Polynomial ℝ)
    (hG : G.eval 0 = 0) (hP : P.eval 0 = 0)
    (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi) :
    TendstoUniformlyOn
      (fun T (p : ℂ × ℂ) => PRZZ.gcdMainTerm (fengProfile G) (profile P) PRZZAsymptotic.theta T Phi p.1 p.2/(T:ℂ))
      (fun p => functional 2 0 G P p.1 p.2 * weightMass Phi) atTop witnessBidisc :=
  normalized_gcd_uniform_of_arithmetic _ _ _
    (scaledArithmetic20_twoBidiscs G P hG hP)
    (H20_bounded (complexify G) (complexify P)) Phi hPhi

/-- Ordered mixed terms are added, not doubled at unequal shifts. -/
theorem normalized_cross_uniform (P G : Polynomial ℝ)
    (hP : P.eval 0 = 0) (hG : G.eval 0 = 0)
    (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi) :
    TendstoUniformlyOn
      (fun T (p : ℂ × ℂ) =>
        (PRZZ.gcdMainTerm (profile P) (fengProfile G) PRZZAsymptotic.theta T Phi p.1 p.2+
          PRZZ.gcdMainTerm (fengProfile G) (profile P) PRZZAsymptotic.theta T Phi p.1 p.2)/(T:ℂ))
      (fun p => (functional 0 2 P G p.1 p.2+functional 2 0 G P p.1 p.2)*weightMass Phi)
      atTop witnessBidisc := by
  simpa only [Pi.add_def,add_div,add_mul] using
    (normalized_gcd02_uniform P G hP hG Phi hPhi).add
      (normalized_gcd20_uniform G P hG hP Phi hPhi)

theorem normalized_gcd02_tendsto (P G : Polynomial ℝ)
    (hP : P.eval 0 = 0) (hG : G.eval 0 = 0)
    (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi)
    (p : ℂ × ℂ) (hp : p ∈ witnessBidisc) :
    Tendsto (fun T => PRZZ.gcdMainTerm (profile P) (fengProfile G) PRZZAsymptotic.theta T Phi p.1 p.2/(T:ℂ))
      atTop (nhds (functional 0 2 P G p.1 p.2*weightMass Phi)) :=
  (normalized_gcd02_uniform P G hP hG Phi hPhi).tendsto_at hp

theorem normalized_gcd20_tendsto (G P : Polynomial ℝ)
    (hG : G.eval 0 = 0) (hP : P.eval 0 = 0)
    (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi)
    (p : ℂ × ℂ) (hp : p ∈ witnessBidisc) :
    Tendsto (fun T => PRZZ.gcdMainTerm (fengProfile G) (profile P) PRZZAsymptotic.theta T Phi p.1 p.2/(T:ℂ))
      atTop (nhds (functional 2 0 G P p.1 p.2*weightMass Phi)) :=
  (normalized_gcd20_uniform G P hG hP Phi hPhi).tendsto_at hp

#print axioms monomial_bounded
#print axioms H02_bounded
#print axioms H20_bounded
#print axioms normalized_gcd_uniform_of_arithmetic
#print axioms normalized_gcd02_uniform
#print axioms normalized_gcd20_uniform
#print axioms normalized_cross_uniform
#print axioms normalized_gcd02_tendsto
#print axioms normalized_gcd20_tendsto
end XiPrime8845.FengMixedMainTerm
