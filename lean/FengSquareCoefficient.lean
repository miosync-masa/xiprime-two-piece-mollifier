import FengCrossCoefficient
import FengSharedShift

/-! Exact theta^-4 normalization of the original Feng/Feng coefficient sum.
The two actual Feng blocks retain every g and their finite inner cutoffs.
This supplies H22 arithmetic asymptotics, not the normalized gcd limit or
the zero-counting adapter. -/
noncomputable section
open scoped BigOperators
open Finset Filter Topology
namespace XiPrime8845.FengSquareCoefficient
open GcdDecomposition ConreyCoefficientBridge FengCoefficientBridge FengCrossCoefficient
set_option maxHeartbeats 1000000

/-- Each original Feng inner coefficient contributes theta^-2, hence theta^-4
for the product. This finite identity needs no vanishing profile endpoint. -/
theorem scaledArithmetic22_eq (P G : Polynomial ℝ) (θ T : ℝ)
    (hθ : 0 < θ) (hT : 1 < T) (A B : ℂ) :
    scaledArithmetic (fengProfile P) (fengProfile G) θ T A B =
      FengSquareAssembly.fullSum (Real.log T) θ (complexify P) (complexify G) A B / (θ:ℂ)^4 := by
  have hL : (Real.log T : ℂ) ≠ 0 := by exact_mod_cast (Real.log_pos hT).ne'
  have hs : Icc 1 (PRZZ.cutoff θ T) = Ioc 0 (CoprimeEndpoint.cutoff (Real.log T) θ) := by
    rw [cutoff_eq θ T hT]
    ext n
    simp only [mem_Icc,mem_Ioc,CoprimeEndpoint.cutoff]
    omega
  rw [scaledArithmetic_diagonal,FengSquareAssembly.fullSum,FengLogProducts.productSum,← hs]
  simp only [Finset.mul_sum,Finset.sum_div]
  apply sum_congr rfl
  intro g hg
  have hp := feng_inner_scaled P θ T hθ hT g (mem_Icc.mp hg).1 A
  have hg' := feng_inner_scaled G θ T hθ hT g (mem_Icc.mp hg).1 B
  unfold FengMixedShift.rawWeight LogProfileSum.coordinate
  calc
    _ = ElementaryGcd.generalizedTotient (1+A/(Real.log T:ℂ)+B/(Real.log T:ℂ)) g /
          (g:ℂ)^(2+A/(Real.log T:ℂ)+B/(Real.log T:ℂ)) *
          ((Real.log T:ℂ)*inner (fengProfile P) θ T g A) *
          ((Real.log T:ℂ)*inner (fengProfile G) θ T g B) / (Real.log T:ℂ) := by
      field_simp
    _ = _ := by rw [hp,hg']; ring

/-- The original unscaled finite double sum retains its additional 1/log T.
No coefficient is replaced by an asymptotic in this identity. -/
theorem arithmeticSum22_eq (P G : Polynomial ℝ) (θ T : ℝ)
    (hθ : 0 < θ) (hT : 1 < T) (A B : ℂ) :
    arithmeticSum (PRZZ.coefficient (fengProfile P) θ T)
      (PRZZ.coefficient (fengProfile G) θ T) (PRZZ.cutoff θ T)
      (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) =
      FengSquareAssembly.fullSum (Real.log T) θ (complexify P) (complexify G) A B /
        ((θ:ℂ)^4*(Real.log T:ℂ)) := by
  have hL : (Real.log T:ℂ) ≠ 0 := by exact_mod_cast (Real.log_pos hT).ne'
  have h := scaledArithmetic22_eq P G θ T hθ hT A B
  unfold scaledArithmetic at h
  rw [← div_div]
  apply (eq_div_iff hL).mpr
  exact (mul_comm _ _).trans h

/-- Normalization of the actual nine-product sum, still parametrized by L. -/
theorem normalized_fullSum_twoBidiscs (P G : Polynomial ℂ)
    (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => FengSquareAssembly.fullSum L PRZZAsymptotic.theta P G p.1 p.2 /
        (PRZZAsymptotic.theta:ℂ)^4)
      (fun p => BetaKernel.H 2 2 p.1 p.2 PRZZAsymptotic.theta P G)
      atTop ElementaryGcd.twoBidiscs := by
  have h := FengSharedShift.fullSum_twoBidiscs P G hP hG
  have hθ : 0 < PRZZAsymptotic.theta := by norm_num [PRZZAsymptotic.theta]
  have hden : 0 < ‖(PRZZAsymptotic.theta:ℂ)^4‖ :=
    norm_pos_iff.mpr (pow_ne_zero _ (by exact_mod_cast hθ.ne'))
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h (eps*‖(PRZZAsymptotic.theta:ℂ)^4‖)
    (mul_pos heps hden)] with L hh
  intro p hp
  have ht := hh p hp
  rw [dist_comm,dist_eq_norm] at ht ⊢
  simp only [BetaKernel.H,show (2+2:ℕ)=4 by norm_num,← sub_div,norm_div]
  exact (div_lt_iff₀ hden).mpr ht

/-- Literal PRZZ coefficient double sum, with L=log T and no arithmetic premise. -/
theorem scaledArithmetic22_twoBidiscs (P G : Polynomial ℝ)
    (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) :
    TendstoUniformlyOn
      (fun T (p : ℂ × ℂ) => scaledArithmetic (fengProfile P) (fengProfile G)
        PRZZAsymptotic.theta T p.1 p.2)
      (fun p => BetaKernel.H 2 2 p.1 p.2 PRZZAsymptotic.theta (complexify P) (complexify G))
      atTop ElementaryGcd.twoBidiscs := by
  have hPc : (complexify P).eval 0 = 0 := by
    simpa only [Complex.ofReal_zero,hP] using complexify_eval P 0
  have hGc : (complexify G).eval 0 = 0 := by
    simpa only [Complex.ofReal_zero,hG] using complexify_eval G 0
  have h := normalized_fullSum_twoBidiscs (complexify P) (complexify G) hPc hGc
  have hθ : 0 < PRZZAsymptotic.theta := by norm_num [PRZZAsymptotic.theta]
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (Metric.tendstoUniformlyOn_iff.mp h eps heps)] with T hT hh
  intro p hp
  rw [scaledArithmetic22_eq P G _ T hθ hT]
  exact hh p hp

theorem scaledArithmetic22_reflected (P G : Polynomial ℝ)
    (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) :
    TendstoUniformlyOn
      (fun T (p : ℂ × ℂ) => scaledArithmetic (fengProfile P) (fengProfile G)
        PRZZAsymptotic.theta T (-p.2) (-p.1))
      (fun p => BetaKernel.H 2 2 (-p.2) (-p.1) PRZZAsymptotic.theta (complexify P) (complexify G))
      atTop PRZZAsymptotic.witnessBidisc :=
  ElementaryGcd.uniform_reflected (scaledArithmetic22_twoBidiscs P G hP hG)

/-- Exact direct/dual gcd interface only. The zeta and height limits are not
composed here. The dual keeps both profiles and uses the shifts (-B,-A). -/
theorem normalized_gcd22_eq (P G : Polynomial ℝ) (θ T : ℝ)
    (hθ : 0 < θ) (hT : 1 < T) (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi) (A B : ℂ) :
    PRZZ.gcdMainTerm (fengProfile P) (fengProfile G) θ T Phi A B/(T:ℂ) =
      (riemannZeta (1+(A+B)/(Real.log T:ℂ))/(Real.log T:ℂ)) *
        (FengSquareAssembly.fullSum (Real.log T) θ (complexify P) (complexify G) A B/(θ:ℂ)^4) *
        (mass Phi T/(T:ℂ)) +
      (riemannZeta (1-(A+B)/(Real.log T:ℂ))/(Real.log T:ℂ)) *
        (FengSquareAssembly.fullSum (Real.log T) θ (complexify P) (complexify G) (-B) (-A)/(θ:ℂ)^4) *
        (heightFactor Phi T ((A+B)/(Real.log T:ℂ))/(T:ℂ)) := by
  rw [normalized_gcd_split _ _ _ _ _ hPhi hT,
    scaledArithmetic22_eq P G θ T hθ hT,scaledArithmetic22_eq P G θ T hθ hT]

#print axioms scaledArithmetic22_eq
#print axioms arithmeticSum22_eq
#print axioms normalized_fullSum_twoBidiscs
#print axioms scaledArithmetic22_twoBidiscs
#print axioms scaledArithmetic22_reflected
#print axioms normalized_gcd22_eq
end XiPrime8845.FengSquareCoefficient
