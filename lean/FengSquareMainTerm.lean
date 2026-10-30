import FengSquareCoefficient
import FengMixedMainTerm

/-! Uniform limit of the original normalized Feng/Feng gcd main term.
The arithmetic supplier includes all nine blocks and theta^-4. Pole and height
composition is on witnessBidisc, away from A+B=0; no counting claim is made. -/
noncomputable section
open Filter Topology
namespace XiPrime8845.FengSquareMainTerm
open PRZZAsymptotic ConreyCoefficientBridge FengCoefficientBridge
open FengMixedMainTerm ConreyMainTerm
set_option maxHeartbeats 1000000

/-- A common bound for all nine monomial contributions, on both bidiscs. -/
theorem H22_bounded (P G : Polynomial ℂ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ ElementaryGcd.twoBidiscs,
      ‖BetaKernel.H 2 2 p.1 p.2 PRZZAsymptotic.theta P G‖ ≤ M := by
  have hθ : 0 < PRZZAsymptotic.theta := by norm_num [PRZZAsymptotic.theta]
  obtain ⟨a,ha,h1⟩ := monomial_bounded 1 1 5 PRZZAsymptotic.theta (5*R/4) hθ P G
  obtain ⟨b,hb,h2⟩ := monomial_bounded 1 0 4 PRZZAsymptotic.theta (5*R/4) hθ P G
  obtain ⟨c,hc,h3⟩ := monomial_bounded 0 1 4 PRZZAsymptotic.theta (5*R/4) hθ P G
  obtain ⟨d,hd,h4⟩ := monomial_bounded 1 (-1) 3 PRZZAsymptotic.theta (5*R/4) hθ P G
  obtain ⟨e,he,h5⟩ := monomial_bounded (-1) 1 3 PRZZAsymptotic.theta (5*R/4) hθ P G
  obtain ⟨f,hf,h6⟩ := monomial_bounded 0 0 3 PRZZAsymptotic.theta (5*R/4) hθ P G
  obtain ⟨g,hg,h7⟩ := monomial_bounded (-1) 0 2 PRZZAsymptotic.theta (5*R/4) hθ P G
  obtain ⟨h,hh,h8⟩ := monomial_bounded 0 (-1) 2 PRZZAsymptotic.theta (5*R/4) hθ P G
  obtain ⟨i,hi,h9⟩ := monomial_bounded (-1) (-1) 1 PRZZAsymptotic.theta (5*R/4) hθ P G
  refine ⟨(7*a+6*(b+c)+d+e+8*f+2*(g+h)+i)/PRZZAsymptotic.theta^4,by positivity,?_⟩
  intro p hp
  have hs := ShiftedMobius.twoBidiscs_norm p hp
  rw [BetaKernel.H,BetaKernel.assemble22,norm_div]
  simp only [show 2+2=4 from rfl,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hθ]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply (norm_add_le _ _).trans
  apply add_le_add _ (h9 _ _ hs.1 hs.2)
  apply (norm_sub_le _ _).trans
  apply add_le_add
  · apply (norm_add_le _ _).trans
    apply add_le_add
    · apply (norm_add_le _ _).trans
      apply add_le_add _ (h5 _ _ hs.1 hs.2)
      apply (norm_add_le _ _).trans
      apply add_le_add _ (h4 _ _ hs.1 hs.2)
      apply (norm_sub_le _ _).trans
      apply add_le_add
      · rw [norm_mul]
        norm_num only [Complex.norm_ofNat]
        exact mul_le_mul_of_nonneg_left (h1 _ _ hs.1 hs.2) (by norm_num)
      · rw [norm_mul]
        norm_num only [Complex.norm_ofNat]
        exact mul_le_mul_of_nonneg_left
          ((norm_add_le _ _).trans (add_le_add (h2 _ _ hs.1 hs.2) (h3 _ _ hs.1 hs.2))) (by norm_num)
    · rw [norm_mul]
      norm_num only [Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_left (h6 _ _ hs.1 hs.2) (by norm_num)
  · rw [norm_mul]
    norm_num only [Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left
      ((norm_add_le _ _).trans (add_le_add (h7 _ _ hs.1 hs.2) (h8 _ _ hs.1 hs.2))) (by norm_num)

/-- The actual original Feng/Feng gcd term, including the direct and dual
zeta poles and the height factor, uniformly on the witness bidisc. -/
theorem normalized_gcd22_uniform (P G : Polynomial ℝ)
    (hP : P.eval 0 = 0) (hG : G.eval 0 = 0)
    (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi) :
    TendstoUniformlyOn
      (fun T (p : ℂ × ℂ) => PRZZ.gcdMainTerm (fengProfile P) (fengProfile G)
        PRZZAsymptotic.theta T Phi p.1 p.2/(T:ℂ))
      (fun p => functional 2 2 P G p.1 p.2 * weightMass Phi) atTop witnessBidisc :=
  normalized_gcd_uniform_of_arithmetic _ _ _
    (FengSquareCoefficient.scaledArithmetic22_twoBidiscs P G hP hG)
    (H22_bounded (complexify P) (complexify G)) Phi hPhi

theorem normalized_gcd22_tendsto (P G : Polynomial ℝ)
    (hP : P.eval 0 = 0) (hG : G.eval 0 = 0)
    (Phi : ℝ → ℝ) (hPhi : PRZZ.SmoothWeight Phi)
    (p : ℂ × ℂ) (hp : p ∈ witnessBidisc) :
    Tendsto (fun T => PRZZ.gcdMainTerm (fengProfile P) (fengProfile G)
      PRZZAsymptotic.theta T Phi p.1 p.2/(T:ℂ))
      atTop (nhds (functional 2 2 P G p.1 p.2 * weightMass Phi)) :=
  (normalized_gcd22_uniform P G hP hG Phi hPhi).tendsto_at hp

#print axioms H22_bounded
#print axioms normalized_gcd22_uniform
#print axioms normalized_gcd22_tendsto
end XiPrime8845.FengSquareMainTerm
