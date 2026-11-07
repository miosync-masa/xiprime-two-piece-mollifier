import PRZZActualAStar
import PRZZLiteralFourierLimit

/-! Weil/DI on the positive part of the actual native central cell.
The native shift-slot swap is retained. The spatial scale M and second
arithmetic profile are fixed BEFORE the constants: this is not a uniform
estimate for the height-dependent family of all rescaled profiles.
The negative mode and the actual Fourier tail remain explicit. -/
noncomputable section
open scoped BigOperators ContDiff Topology
open Complex MeasureTheory Set Filter
namespace XiPrime8845.PRZZCentralArithmeticJoin
open PRZZMellinSeparation PRZZActualAggregate PRZZLiteralFourierLimit
set_option maxHeartbeats 6000000

def zeroCell (N d : ℕ) (D T M : ℝ) (a : ℕ → ℂ)
    (F G H Phi : ℝ → ℂ) (alpha beta : ℂ) : ℂ :=
  PRZZSignedCentral.signedLiteral 0 N d D 2 T M a G H F Phi beta alpha (alpha+beta)

def positiveCell (N d J : ℕ) (D T M : ℝ) (a : ℕ → ℂ)
    (F G H Phi : ℝ → ℂ) (alpha beta : ℂ) : ℂ :=
  PRZZAStar.literal N d D ((J:ℝ)+1) T a G H (fun y => F (M⁻¹*y))
    (PRZZDyadicEnvelope.sourceW (alpha+beta)) Phi beta alpha

def negativeCell (N d J : ℕ) (D T M : ℝ) (a : ℕ → ℂ)
    (F G H Phi : ℝ → ℂ) (alpha beta : ℂ) : ℂ :=
  PRZZSignedCentral.signedLiteral (-1) N d D ((J:ℝ)+1) T M a G H F Phi beta alpha (alpha+beta)

theorem prefix_split (N d J : ℕ) (D T M : ℝ) (a : ℕ → ℂ)
    (F G H Phi : ℝ → ℂ) (alpha beta : ℂ) :
    cellPrefix N d J D T M a F G H Phi alpha beta =
      zeroCell N d D T M a F G H Phi alpha beta+
        positiveCell N d J D T M a F G H Phi alpha beta+
        negativeCell N d J D T M a F G H Phi alpha beta := rfl

def cellTail (N d J : ℕ) (D T M : ℝ) (a : ℕ → ℂ)
    (F G H Phi : ℝ → ℂ) (alpha beta : ℂ) : ℂ :=
  cellFull N d D T M a F G H Phi alpha beta-cellPrefix N d J D T M a F G H Phi alpha beta

theorem tail_tendsto (N d : ℕ) (D T M : ℝ) (a : ℕ → ℂ)
    (F G H Phi : ℝ → ℂ) (alpha beta : ℂ)
    (hF : ContDiff ℝ ∞ F) (hPhi : Continuous Phi)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hT : 0 < T) (hM : 0 < M) (hs : alpha+beta ≠ 0) :
    Tendsto (fun J : ℕ => cellTail N d J D T M a F G H Phi alpha beta) atTop (𝓝 0) := by
  have hc : Tendsto (fun _ : ℕ => cellFull N d D T M a F G H Phi alpha beta) atTop
      (𝓝 (cellFull N d D T M a F G H Phi alpha beta)) := tendsto_const_nhds
  simpa only [cellTail,sub_self] using
    hc.sub (cell_tendsto N d D T M a F G H Phi alpha beta
      hF hPhi hsF hsPhi hT hM hs)

def positiveBudget (C : ℝ) (w : (List ℕ × List ℕ) → ℝ)
    (caps : (List ℕ × List ℕ) → Caps) (js : List ℕ) (K N d J : ℕ)
    (eps eta b D T M : ℝ) (Phi : ℝ → ℂ) (alpha beta : ℂ) : ℝ :=
  (1/(2*Real.pi)) *
    (∫ p, ‖PRZZAStarIntegralBound.common N d T (M/2) (3*M)
      (PRZZDyadicEnvelope.sourceW (alpha+beta)) beta alpha p‖) *
    totalBudget C w caps js eps eta b T
      (PRZZActualSignedBranches.frequencyBound d D ((J:ℝ)+1)) N d K *
    (∫ t : ℝ, (1+|t|)*‖mellin Phi (t*I)‖)

/-- Only Weil and DI are analytic estimate premises. Support endpoints
M/2,3M are supplied from the actual scaled spatial profile. -/
theorem positive_weil_di
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js : List ℕ) (eps eta b S Z M : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hb : 0 < b) (hS : 0 ≤ S) (hZ : 0 ≤ Z) (hM : 0 < M)
    (F0 F2 F : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (hF2 : Continuous F2) (hcF2 : HasCompactSupport F2)
    (hF : Continuous F) (hcF : HasCompactSupport F)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3) :
    ∃ caps : (List ℕ × List ℕ) → Caps, ∃ w : (List ℕ × List ℕ) → ℝ,
      ∃ C : ℝ, 0 < C ∧ (∀ q, 0 < w q) ∧
      ∀ N d J : ℕ, ∀ T Q D : ℝ, ∀ alpha beta : ℂ,
      0 < N → 0 < d → 1 < T → (N:ℝ)+1 ≤ T → (d:ℝ) ≤ T → 1 ≤ Real.log T →
      1 ≤ (PRZZActualSignedBranches.frequencyBound d D ((J:ℝ)+1):ℝ) →
      |beta.re| ≤ S/Real.log T → 1+‖beta‖ ≤ Z → |alpha.re| ≤ S/Real.log T →
      alpha+beta ≠ 0 → ∀ Phi : ℝ → ℂ,
      ContDiff ℝ ∞ Phi → Function.support Phi ⊆ Icc (1:ℝ) 2 →
      ‖positiveCell N d J D T M (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        F (scaledCutoff F0 Q) F2 Phi alpha beta‖ ≤
        positiveBudget C w caps js K N d J eps eta b D T M Phi alpha beta := by
  have hi : M⁻¹ ≠ 0 := inv_ne_zero hM.ne'
  have hcM : HasCompactSupport (fun y => F (M⁻¹*y)) :=
    hcF.comp_homeomorph (Homeomorph.mulLeft₀ M⁻¹ hi)
  have hsM : Function.support (fun y => F (M⁻¹*y)) ⊆ Icc (M/2) (3*M) := by
    intro y hy
    have hh := hsF hy
    rw [Set.mem_Icc] at hh ⊢
    have he : M*(M⁻¹*y) = y := by field_simp
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hh.1 hM.le,
      mul_le_mul_of_nonneg_left hh.2 hM.le]
  obtain ⟨caps,w,C,hC,hw,h⟩ := PRZZActualAStar.literal_sourceW_bound
    hWeil hDI K hK js eps eta b S Z heps heta hb hS hZ F0 F2 (fun y => F (M⁻¹*y))
    hf hc hF2 hcF2 (hF.comp (continuous_const.mul continuous_id)) hcM
  refine ⟨caps,w,C,hC,hw,?_⟩
  intro N d J T Q D alpha beta hN hd hT hNT hdT hlog hfreq hbeta hz halpha hs Phi hPhi hsPhi
  exact h N d T Q D ((J:ℝ)+1) (M/2) (3*M) beta alpha (alpha+beta)
    hN hd hT hNT hdT hlog hfreq hbeta hz halpha hs (by positivity) (by positivity)
    hsM Phi hPhi hsPhi

/-- The evaluated positive piece can be substituted into the full cell
without throwing away either the negative piece or the true tail. -/
theorem full_cell_bound (N d J : ℕ) (D T M B : ℝ) (a : ℕ → ℂ)
    (F G H Phi : ℝ → ℂ) (alpha beta : ℂ)
    (hB : ‖positiveCell N d J D T M a F G H Phi alpha beta‖ ≤ B) :
    ‖cellFull N d D T M a F G H Phi alpha beta-
        zeroCell N d D T M a F G H Phi alpha beta‖ ≤
      B+‖negativeCell N d J D T M a F G H Phi alpha beta‖+
        ‖cellTail N d J D T M a F G H Phi alpha beta‖ := by
  have he : cellFull N d D T M a F G H Phi alpha beta-
      zeroCell N d D T M a F G H Phi alpha beta =
      (positiveCell N d J D T M a F G H Phi alpha beta+
        negativeCell N d J D T M a F G H Phi alpha beta)+
        cellTail N d J D T M a F G H Phi alpha beta := by
    rw [cellTail,prefix_split]; ring
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add hB le_rfl)) le_rfl)

#print axioms prefix_split
#print axioms tail_tendsto
#print axioms positive_weil_di
#print axioms full_cell_bound
end XiPrime8845.PRZZCentralArithmeticJoin
