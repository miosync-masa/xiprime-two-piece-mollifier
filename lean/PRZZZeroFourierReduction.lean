import PRZZZeroGammaBound
import PRZZSignedCentral

/-! Actual finite central Fourier integrals minus their zero mode are the
positive literal A* plus the negative signed integral. The final estimate
also removes gammaDefect from the coupled AFE error budget. The full
offDiagonalPair-to-centralRows reindexing is still a separate obligation. -/
noncomputable section
open scoped BigOperators
open Complex MeasureTheory Set Filter
namespace XiPrime8845.PRZZZeroFourierReduction
open PRZZSignedCentral PRZZCoupledAFE PRZZZeroCoupled
set_option maxHeartbeats 6000000

theorem nonzero_time (N d J : ℕ) (D T M : ℝ) (a : ℕ → ℂ)
    (F1 F2 F Phi : ℝ → ℂ) (alpha beta sigma : ℂ)
    (hF : Continuous F) (hP : Continuous Phi) (hT : 0 < T) (hM : 0 < M)
    (hs : sigma ≠ 0) (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2) :
    (∫ t : ℝ, centralRows N d J D T M a F1 F2 F Phi alpha beta sigma t-
      band 0 N d D 2 T M a F1 F2 F Phi alpha beta sigma t) =
      PRZZAStar.literal N d D ((J:ℝ)+1) T a F1 F2 (fun y => F (M⁻¹*y))
        (PRZZDyadicEnvelope.sourceW sigma) Phi alpha beta+
      signedLiteral (-1) N d D ((J:ℝ)+1) T M a F1 F2 F Phi alpha beta sigma := by
  have h0 := band_integrable 0 N d D 2 T M a F1 F2 F Phi alpha beta sigma hF hP hT hM hs hsF hsP
  have hp := band_integrable 1 N d D ((J:ℝ)+1) T M a F1 F2 F Phi alpha beta sigma hF hP hT hM hs hsF hsP
  have hm := band_integrable (-1) N d D ((J:ℝ)+1) T M a F1 F2 F Phi alpha beta sigma hF hP hT hM hs hsF hsP
  have hc : Integrable (centralRows N d J D T M a F1 F2 F Phi alpha beta sigma) := by
    have he : centralRows N d J D T M a F1 F2 F Phi alpha beta sigma =
        fun t => band 0 N d D 2 T M a F1 F2 F Phi alpha beta sigma t+
          band 1 N d D ((J:ℝ)+1) T M a F1 F2 F Phi alpha beta sigma t+
          band (-1) N d D ((J:ℝ)+1) T M a F1 F2 F Phi alpha beta sigma t := by
      funext t
      exact central_split N d J D T M a F1 F2 F Phi alpha beta sigma t
    rw [he]
    exact (h0.add hp).add hm
  rw [integral_sub hc h0,
    central_time N d J D T M a F1 F2 F Phi alpha beta sigma hF hP hT hM hs hsF hsP,
    band_literal 0 N d D 2 T M a F1 F2 F Phi alpha beta sigma hF hP hT hM hs hsF hsP]
  ring

/-- All finite gcd and spatial dyadic configurations, with their actual
complex weights and cell-dependent frequency cutoffs. -/
theorem nonzero_configurations (N K : ℕ) (D : ℕ → ℕ → ℝ) (J : ℕ → ℕ → ℕ)
    (w : ℕ → ℕ → ℂ) (T M : ℝ) (a : ℕ → ℂ)
    (F1 F2 F Phi : ℝ → ℂ) (alpha beta sigma : ℂ)
    (hF : Continuous F) (hP : Continuous Phi) (hT : 0 < T) (hM : 0 < M)
    (hs : sigma ≠ 0) (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hsP : Function.support Phi ⊆ Icc (1:ℝ) 2) :
    (∑ d ∈ Finset.Icc 1 N, ∑ k ∈ Finset.range K, w d k*
      ∫ t : ℝ, centralRows N d (J d k) (D d k) T ((2:ℝ)^k*M) a F1 F2 F Phi alpha beta sigma t-
        band 0 N d (D d k) 2 T ((2:ℝ)^k*M) a F1 F2 F Phi alpha beta sigma t) =
      (∑ d ∈ Finset.Icc 1 N, ∑ k ∈ Finset.range K, w d k*
        PRZZAStar.literal N d (D d k) ((J d k:ℝ)+1) T a F1 F2
          (fun y => F (((2:ℝ)^k*M)⁻¹*y)) (PRZZDyadicEnvelope.sourceW sigma) Phi alpha beta)+
      (∑ d ∈ Finset.Icc 1 N, ∑ k ∈ Finset.range K, w d k*
        signedLiteral (-1) N d (D d k) ((J d k:ℝ)+1) T ((2:ℝ)^k*M) a F1 F2 F Phi alpha beta sigma) := by
  simp only [← Finset.sum_add_distrib,← mul_add]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  exact nonzero_time N d (J d k) (D d k) T ((2:ℝ)^k*M) a F1 F2 F Phi alpha beta sigma
    hF hP hT (by positivity) hs hsF hsP

/-- The actual Gamma defect is now bounded, not an additional estimate
premise. Only the genuine signed off-diagonal residual remains unevaluated. -/
theorem coupled_error (js : List ℕ) (S r : ℝ) (hS : 0 ≤ S) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ → ∀ L N : ℕ,
      1 ≤ N → (N:ℝ) ≤ T → ∀ (F : ℝ → ℂ) (R : ℕ → PRZZAFEIndices.Label → Prop)
      [DecidablePred (fun p : ℕ × PRZZAFEIndices.Label => R p.1 p.2)],
      ∀ phi : ℝ → ℂ, Continuous phi →
      let a := fun n => (PRZZGCoefficient.coefficient js n:ℂ)
      let alpha := A/(Real.log T:ℂ)
      let beta := B/(Real.log T:ℂ)
      ‖coupledModel L N F R a alpha beta T phi-diagonalMain N a alpha beta T phi‖ ≤
        ‖offDiagonalPair L N F R a alpha beta T phi-zeroPair N a alpha beta T phi‖+
        C*(1+16*(Real.log T)^2/r^2)*(N:ℝ)^(1/4:ℝ)*T^(-(9/8:ℝ))*
          (1+Real.log N)^(2*PRZZGCoefficient.degree js+2)*(∫ t in Icc T (2*T), ‖phi t‖) := by
  obtain ⟨C,hC,h⟩ := PRZZZeroGammaBound.defect_time_bound js S r hS hr
  refine ⟨C,hC,?_⟩
  filter_upwards [h,PRZZScaledReplacement.shifts_eventually S (1/16) (by norm_num),
    eventually_ge_atTop (2:ℝ)] with T h hsmall hT
  intro A B hA hB hsep L N hN hNT F R inst phi hp
  dsimp only
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]
    exact div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep))
      (by exact_mod_cast (Real.log_pos (by linarith : 1 < T)).ne')
  have hn : ‖A/(Real.log T:ℂ)+B/(Real.log T:ℂ)‖ ≤ 1/8 :=
    (norm_add_le _ _).trans (by linarith [hsmall.2 A hA,hsmall.2 B hB])
  rw [coupled_reassembly L N F R _ _ _ (by linarith [hsmall.2 A hA])
    (by linarith [hsmall.2 B hB]) hs hn T (by linarith) phi hp]
  have hh := h A B hA hB hsep N hN hNT phi hp
  have he := norm_add_le
    (offDiagonalPair L N F R (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
      (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T phi-
      zeroPair N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) T phi)
    (∫ t in Icc T (2*T), phi t*PRZZZeroCross.gammaDefect N
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
      (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t)
  have hbnd := he.trans (add_le_add le_rfl hh)
  convert hbnd using 1
  congr 1
  ring

#print axioms nonzero_time
#print axioms nonzero_configurations
#print axioms coupled_error
end XiPrime8845.PRZZZeroFourierReduction
