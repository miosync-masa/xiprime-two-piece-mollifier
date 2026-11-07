import PRZZAllPoissonRows

/-! Remove the original AFE truncation after the exhaustive Poisson row
substitution. The Fourier cutoff may vary arbitrarily with L. The retained
large-gap complement and all tails/boundaries remain in the model: this is
a closed AFE reduction, not a claimed optimized PRZZ moment asymptotic. -/
noncomputable section
open scoped ContDiff
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZAllPoissonAFE
open PRZZAllPoissonRows PRZZCoupledAFE
set_option maxHeartbeats 7000000

def model (L J N : ℕ) (F : ℝ → ℂ) (a : ℕ → ℂ) (alpha beta : ℂ)
    (T : ℝ) (phi : ℝ → ℂ) : ℂ :=
  diagonalMain N a alpha beta T phi+
    (((∫ t in Icc T (2*T), phi t*family L J N F (fun _ => 1) (fun _ => 1) a alpha beta t)+
      ∫ t in Icc T (2*T), (phi t*PRZZAFEDual.dualMultiplier alpha beta t)*
        family L J N F (fun _ => 1) (fun _ => 1) a (-beta) (-alpha) t)-
      PRZZZeroCoupled.zeroPair N a alpha beta T phi)+
    ∫ t in Icc T (2*T), phi t*PRZZZeroCross.gammaDefect N a alpha beta t

theorem model_eq (L J N : ℕ) (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hlo : ∀ y ≤ (1/2:ℝ), F y = 1) (hhi : ∀ y, 1 ≤ y → F y = 0)
    (R : ℕ → PRZZAFEIndices.Label → Prop)
    [DecidablePred (fun p : ℕ × PRZZAFEIndices.Label => R p.1 p.2)]
    (a : ℕ → ℂ) (alpha beta : ℂ) (ha : ‖alpha‖ ≤ 1/4) (hb : ‖beta‖ ≤ 1/4)
    (hs : alpha+beta ≠ 0) (hn : ‖alpha+beta‖ ≤ 1/8)
    (T : ℝ) (hT : 0 < T) (phi : ℝ → ℂ) (hp : Continuous phi) :
    model L J N F a alpha beta T phi = coupledModel L N F R a alpha beta T phi :=
  (coupled_poisson L J N F hF hlo hhi R a alpha beta ha hb hs hn T hT phi hp).symm

/-- The sharp original AFE error budget survives the full row
substitution and L-limit. No decomposition identity is a premise. -/
theorem scaled_afe_limit (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hlo : ∀ y ≤ (1/2:ℝ), F y = 1) (hhi : ∀ y, 1 ≤ y → F y = 0)
    (js : List ℕ) (S r delta : ℝ) (hS : 0 ≤ S) (hr : 0 < r) (hd : 0 < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ → ∀ N : ℕ, 1 ≤ N → (N:ℝ) ≤ T →
      ∀ (phi : ℝ → ℂ) (P : ℝ), Continuous phi → 0 ≤ P →
      (∀ t ∈ Icc T (2*T), ‖phi t‖ ≤ P) → ∀ J : ℕ → ℕ, ∃ E : ℂ,
      Tendsto (fun L : ℕ =>
        (∫ t in Icc T (2*T), PRZZMollifiedTime.mollifierWeight phi
          (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
          (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) N t *
            (riemannZeta (PRZZAFEDual.leftArg (A/(Real.log T:ℂ)) t)*
             riemannZeta (PRZZAFEDual.rightArg (B/(Real.log T:ℂ)) t)))-
        model L (J L) N F (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T phi) atTop (𝓝 E) ∧
      ‖E‖ ≤ C*P*T^delta*PRZZOptimalPowers.target N T := by
  let R : ℕ → PRZZAFEIndices.Label → Prop := fun _ _ => True
  obtain ⟨C,hC,h⟩ := scaled_coupled_limit F R hlo hhi js S r delta hS hr hd
  refine ⟨C,hC,?_⟩
  filter_upwards [h,PRZZScaledReplacement.shifts_eventually S (1/16) (by norm_num),
    eventually_ge_atTop (2:ℝ)] with T h hsmall hT
  intro A B hA hB hsep N hN hNT phi P hp hP hphi J
  obtain ⟨E,hlim,hbound⟩ := h A B hA hB hsep N hN hNT phi P hp hP hphi
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]
    exact div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep))
      (by exact_mod_cast (Real.log_pos (by linarith : 1 < T)).ne')
  have hn : ‖A/(Real.log T:ℂ)+B/(Real.log T:ℂ)‖ ≤ 1/8 :=
    (norm_add_le _ _).trans (by linarith [hsmall.2 A hA,hsmall.2 B hB])
  refine ⟨E,?_,hbound⟩
  convert hlim using 1
  funext L
  rw [model_eq L (J L) N F hF hlo hhi R _ _ _
    (by linarith [hsmall.2 A hA]) (by linarith [hsmall.2 B hB]) hs hn T (by linarith) phi hp]

#print axioms model_eq
#print axioms scaled_afe_limit
end XiPrime8845.PRZZAllPoissonAFE
