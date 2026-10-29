import FengMixedShift
import ConreyOuter

/-! Exact polynomial absorption closes the actual Conrey/logBlock limit.
The outside prime-power block is not included in this theorem. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Finset Filter Topology Polynomial
namespace XiPrime8845.FengLogMainTerm
open FengAtG FengMixedInterior LogProfileSum CoprimeEndpoint BetaKernel
set_option maxHeartbeats 1000000

def logProfile (U θ : ℝ) (G : Polynomial ℂ) : Polynomial ℂ :=
  (C (U:ℂ)-C (θ:ℂ)*X)^2*G

theorem logProfile_eval (U θ w : ℝ) (G : Polynomial ℂ) (hθ : θ ≠ 0) :
    (logProfile U θ G).eval ((w/θ:ℝ):ℂ) = (U-w:ℝ)^2*G.eval ((w/θ:ℝ):ℂ) := by
  have ht : (θ:ℂ) ≠ 0 := by exact_mod_cast hθ
  simp only [logProfile,eval_mul,eval_pow,eval_sub,eval_C,eval_X,Complex.ofReal_div,
    Complex.ofReal_sub]
  field_simp

theorem logProfile_zero (U θ : ℝ) (G : Polynomial ℂ) (hG : G.eval 0 = 0) :
    (logProfile U θ G).eval 0 = 0 := by simp [logProfile,hG]

theorem logBlock_eq_conrey (L U θ : ℝ) (g : ℕ) (G : Polynomial ℂ) (B : ℂ)
    (hg : g ≠ 0) (hθ : θ ≠ 0) :
    logBlock ⌊Real.exp (L*coordinate L U g)⌋₊ g L (coordinate L U g) θ G B =
      conrey L g (coordinate L U g) θ (logProfile U θ G) B := by
  rw [logBlock,conrey_eq]
  congr 1
  apply sum_congr rfl
  intro n hn
  have hg' : (g:ℝ) ≠ 0 := by exact_mod_cast hg
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by have := (mem_Icc.mp hn).1; omega)
  simp only [ShiftWeights.weight,logProfile_eval U θ _ G hθ]
  rw [Real.log_mul hg' hn']
  simp only [coordinate]
  push_cast
  ring

theorem D_logProfile (U θ w : ℝ) (G : Polynomial ℂ) (B : ℂ) (hθ : θ ≠ 0) :
    D 1 B θ w (logProfile U θ G) =
      (U-w:ℝ)^2*D 1 B θ w G-2*(U-w:ℝ)*D 0 B θ w G := by
  have ht : (θ:ℂ) ≠ 0 := by exact_mod_cast hθ
  simp [D,logProfile,Polynomial.derivative_mul,Polynomial.derivative_pow]
  field_simp
  ring

def actualSum (L θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) : ℂ :=
  (∑ g ∈ Ioc 0 (cutoff L θ), FengMixedShift.rawWeight (A/L) (B/L) g *
    conrey L g (coordinate L θ g) θ P A *
    logBlock ⌊Real.exp (L*coordinate L θ g)⌋₊ g L (coordinate L θ g) θ G B)/(L:ℂ)

theorem actualSum_eq (L θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) (hθ : θ ≠ 0) :
    actualSum L θ P G A B = ConreyOuter.actualSum L θ P (logProfile θ θ G) A B := by
  unfold actualSum ConreyOuter.actualSum
  congr 1
  apply sum_congr rfl
  intro g hg
  rw [logBlock_eq_conrey L θ θ g G B (mem_Ioc.mp hg).1.ne' hθ]
  unfold conrey FengMixedShift.rawWeight BareEuler.weight
  ring

theorem log_kernel (θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) (hθ : θ ≠ 0) :
    H 0 0 A B θ P (logProfile θ θ G) =
      2*monomialIntegral A B θ P G 1 1 3-2*monomialIntegral A B θ P G 1 0 2 := by
  simp only [H,assemble00,Nat.add_zero,pow_zero,div_one]
  unfold monomialIntegral
  norm_num
  rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub]
  · apply intervalIntegral.integral_congr
    intro v hv
    dsimp only
    rw [D_logProfile θ θ (θ-v) G B hθ]
    push_cast
    ring
  all_goals apply Continuous.intervalIntegrable; unfold D; norm_num; fun_prop

theorem actualSum_twoBidiscs (P G : Polynomial ℂ) (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => actualSum L PRZZAsymptotic.theta P G p.1 p.2)
      (fun p => 2*monomialIntegral p.1 p.2 PRZZAsymptotic.theta P G 1 1 3-
        2*monomialIntegral p.1 p.2 PRZZAsymptotic.theta P G 1 0 2)
      atTop ElementaryGcd.twoBidiscs := by
  have ht : PRZZAsymptotic.theta ≠ 0 := by norm_num [PRZZAsymptotic.theta]
  simpa only [actualSum_eq _ _ _ _ _ _ ht,log_kernel _ _ _ _ _ ht] using
    ConreyOuter.actualSum_twoBidiscs P (logProfile PRZZAsymptotic.theta PRZZAsymptotic.theta G)
      hP (logProfile_zero _ _ G hG)

theorem actualSum_reflected (P G : Polynomial ℂ) (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => actualSum L PRZZAsymptotic.theta P G (-p.2) (-p.1))
      (fun p => 2*monomialIntegral (-p.2) (-p.1) PRZZAsymptotic.theta P G 1 1 3-
        2*monomialIntegral (-p.2) (-p.1) PRZZAsymptotic.theta P G 1 0 2)
      atTop PRZZAsymptotic.witnessBidisc :=
  ElementaryGcd.uniform_reflected (actualSum_twoBidiscs P G hP hG)

#print axioms logProfile_eval
#print axioms logBlock_eq_conrey
#print axioms D_logProfile
#print axioms actualSum_eq
#print axioms log_kernel
#print axioms actualSum_twoBidiscs
#print axioms actualSum_reflected
end XiPrime8845.FengLogMainTerm
