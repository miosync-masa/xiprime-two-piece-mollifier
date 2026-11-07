import PRZZCentralMainAssembly

/-! Substitute Weil/DI into every positive cell of the ACTUAL finite grid.
The constants are chosen before N,T,L,J, but remain indexed by the second
arithmetic scale and spatial scale. No uniform bound for that indexed
family, nor its optimal height-power absorption, is asserted here. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Finset MeasureTheory Set
namespace XiPrime8845.PRZZCentralGridWeilDI
open PRZZCentralArithmeticJoin PRZZCentralMainAssembly PRZZMellinSeparation PRZZActualAggregate
set_option maxHeartbeats 9000000

/-- The actual logarithmic shifts supply the fixed norm cap Z=1+S;
no height-dependent Z is hidden in the arithmetic constants. -/
theorem scaled_shift_conditions (S T : ℝ) (A B : ℂ) (hS : 0 ≤ S)
    (hlog : 1 ≤ Real.log T) (hA : ‖A‖ ≤ S) (hB : ‖B‖ ≤ S) :
    |(B/(Real.log T:ℂ)).re| ≤ S/Real.log T ∧
      1+‖B/(Real.log T:ℂ)‖ ≤ 1+S ∧
      |(A/(Real.log T:ℂ)).re| ≤ S/Real.log T := by
  have hn (z : ℂ) : ‖z/(Real.log T:ℂ)‖ = ‖z‖/Real.log T := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith)]
  have ha : ‖A/(Real.log T:ℂ)‖ ≤ S/Real.log T := by rw [hn]; gcongr
  have hb : ‖B/(Real.log T:ℂ)‖ ≤ S/Real.log T := by rw [hn]; gcongr
  exact ⟨(abs_re_le_norm _).trans hb,
    add_le_add le_rfl (hb.trans (div_le_self hS hlog)),(abs_re_le_norm _).trans ha⟩

theorem frequency_positive (d J : ℕ) (D : ℝ) (hd : 0 < d) (hD : 0 < D) :
    1 ≤ (PRZZActualSignedBranches.frequencyBound d D ((J:ℝ)+1):ℝ) := by
  have hc : 0 < ⌈D/(d:ℝ)⌉ := Int.ceil_pos.mpr (by positivity)
  have ha : 1 ≤ (⌈D/(d:ℝ)⌉).natAbs := Int.natAbs_pos.mpr (ne_of_gt hc)
  have hf : ⌊((J:ℝ)+1)⌋₊ = J+1 := by
    rw [show (J:ℝ)+1 = ((J+1:ℕ):ℝ) by push_cast; rfl,Nat.floor_natCast]
  unfold PRZZActualSignedBranches.frequencyBound
  rw [hf]
  exact_mod_cast (show 1 ≤ (⌈D/(d:ℝ)⌉).natAbs*(J+1) by nlinarith)

def gridBudget (caps : (ℕ × ℕ) → (List ℕ × List ℕ) → Caps)
    (w : (ℕ × ℕ) → (List ℕ × List ℕ) → ℝ) (C : (ℕ × ℕ) → ℝ)
    (js : List ℕ) (K Kgrid L J N : ℕ) (eps eta b T eCut : ℝ)
    (Phi : ℝ → ℂ) (alpha beta : ℂ) : ℝ :=
  ∑ p ∈ range Kgrid ×ˢ range Kgrid,
    ∑ s ∈ (range (L+2)).filter (fun s => (2:ℝ)^s < T^(4:ℝ)), ∑ d ∈ Icc 1 N,
      positiveBudget (C (p.2,s)) (w (p.2,s)) (caps (p.2,s)) js K N d J eps eta b
        (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) ((2:ℝ)^p.1) eCut) T ((2:ℝ)^s)
        Phi alpha beta

/-- Original arithmetic profile values, spatial profile, modulus cutoff,
all d and all strict spatial rows. There is no supplied cell-bound premise.
Only Weil and DI are the arithmetic estimate premises. -/
theorem positive_grid_bound
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js : List ℕ) (eps eta b S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hb : 0 < b) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (P F : ℝ → ℂ) (hP : ContDiff ℝ ∞ P) (hF : ContDiff ℝ ∞ F)
    (hPl : ∀ x ≤ (1/2:ℝ), P x = 1) (hPr : ∀ x, 1 ≤ x → P x = 0)
    (hFl : ∀ x ≤ (1/2:ℝ), F x = 1) (hFr : ∀ x, 1 ≤ x → F x = 0) :
    ∃ caps : (ℕ × ℕ) → (List ℕ × List ℕ) → Caps,
      ∃ w : (ℕ × ℕ) → (List ℕ × List ℕ) → ℝ, ∃ C : (ℕ × ℕ) → ℝ,
      (∀ i, 0 < C i) ∧ (∀ i q, 0 < w i q) ∧
      ∀ Kgrid L J N : ℕ, ∀ T eCut : ℝ, ∀ alpha beta : ℂ,
      1 ≤ N → (N:ℝ)+1 ≤ T → 1 ≤ Real.log T →
      |beta.re| ≤ S/Real.log T → 1+‖beta‖ ≤ Z → |alpha.re| ≤ S/Real.log T →
      alpha+beta ≠ 0 → ∀ Phi : ℝ → ℂ,
      ContDiff ℝ ∞ Phi → Function.support Phi ⊆ Icc (1:ℝ) 2 →
      ‖positivePart P F Phi Kgrid L J N (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
          T eCut alpha beta‖ ≤
        gridBudget caps w C js K Kgrid L J N eps eta b T eCut Phi alpha beta := by
  have hp := PRZZWRowLimit.profile_regular P hP hPl hPr
  have hf := PRZZWRowLimit.profile_regular F hF hFl hFr
  have hex (i : ℕ × ℕ) := positive_weil_di hWeil hDI K hK js eps eta b S Z ((2:ℝ)^i.2)
    heps heta hb hS hZ (by positivity) (PRZZWRowLimit.profile P)
    (scaledCutoff (PRZZWRowLimit.profile P) ((2:ℝ)^i.1)) (PRZZWRowLimit.profile F)
    hp.1 hp.2.1
    (hp.1.continuous.comp (continuous_const.mul continuous_id))
    (hp.2.1.comp_homeomorph (Homeomorph.mulLeft₀ (((2:ℝ)^i.1)⁻¹) (by positivity)))
    hf.1.continuous hf.2.1 hf.2.2
  choose caps w C hC hw hbound using hex
  refine ⟨caps,w,C,hC,hw,?_⟩
  intro Kgrid L J N T eCut alpha beta hN hNT hlog hbeta hz halpha hs Phi hPhi hsPhi
  have hT : 1 < T := by
    have : (1:ℝ) ≤ N := by exact_mod_cast hN
    linarith
  unfold positivePart collect gridBudget
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro p hp'
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro s hs'
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro d hd
  have hd0 : 0 < d := (mem_Icc.mp hd).1
  have hdT : (d:ℝ) ≤ T := (by exact_mod_cast (mem_Icc.mp hd).2 : (d:ℝ) ≤ N).trans (by linarith)
  exact hbound (p.2,s) N d J T ((2:ℝ)^p.1)
    (PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) ((2:ℝ)^p.1) eCut) alpha beta
    (by omega) hd0 hT hNT hdT hlog
    (frequency_positive d J _ hd0 (by unfold PRZZSourceCutoffs.deltaCutoff; positivity))
    hbeta hz halpha hs Phi hPhi hsPhi

/-- Propagate any actual positive-grid evaluation through the two genuine
branches, with the negative, zero-discrepancy and tail pieces untouched. -/
theorem arithmetic_residual_bound (P F Phi : ℝ → ℂ) (K J N : ℕ) (a : ℕ → ℂ)
    (T eps Bp Bm : ℝ) (alpha beta : ℂ)
    (hp : ‖positivePart P F Phi K (PRZZLiteralExhaustion.spatialLength T) J N a T eps alpha beta‖ ≤ Bp)
    (hm : ‖positivePart P F (PRZZKeptLiteral.dualProfile Phi T alpha beta)
      K (PRZZLiteralExhaustion.spatialLength T) J N a T eps (-beta) (-alpha)‖ ≤ Bm) :
    ‖arithmeticResidual P F Phi K J N a T eps alpha beta‖ ≤
      ‖zeroMismatch P F Phi K N a T eps alpha beta‖+(Bp+Bm)+
        ‖branchPair (fun Phi alpha beta => negativePart P F Phi K
          (PRZZLiteralExhaustion.spatialLength T) J N a T eps alpha beta) Phi T alpha beta‖+
        ‖branchPair (fun Phi alpha beta => tailPart P F Phi K
          (PRZZLiteralExhaustion.spatialLength T) J N a T eps alpha beta) Phi T alpha beta‖ := by
  have hb : ‖branchPair (fun Phi alpha beta => positivePart P F Phi K
      (PRZZLiteralExhaustion.spatialLength T) J N a T eps alpha beta) Phi T alpha beta‖ ≤ Bp+Bm :=
    (norm_add_le _ _).trans (add_le_add hp hm)
  unfold arithmeticResidual
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add le_rfl hb)) le_rfl)) le_rfl)

/-- Direct substitution into the actual two-branch arithmetic residual.
The dual Mellin mass contains the GENUINE smooth Gamma profile, not the
unweighted Phi mass. No estimate for that mass is smuggled into a constant. -/
theorem paired_residual_weil_di
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js : List ℕ) (eps eta b S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hb : 0 < b) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (P F : ℝ → ℂ) (hP : ContDiff ℝ ∞ P) (hF : ContDiff ℝ ∞ F)
    (hPl : ∀ x ≤ (1/2:ℝ), P x = 1) (hPr : ∀ x, 1 ≤ x → P x = 0)
    (hFl : ∀ x ≤ (1/2:ℝ), F x = 1) (hFr : ∀ x, 1 ≤ x → F x = 0) :
    ∃ caps : (ℕ × ℕ) → (List ℕ × List ℕ) → Caps,
      ∃ w : (ℕ × ℕ) → (List ℕ × List ℕ) → ℝ, ∃ C : (ℕ × ℕ) → ℝ,
      (∀ i, 0 < C i) ∧ (∀ i q, 0 < w i q) ∧
      ∀ Kgrid J N : ℕ, ∀ T eCut : ℝ, ∀ alpha beta : ℂ,
      1 ≤ N → (N:ℝ)+1 ≤ T → 1 ≤ Real.log T →
      |beta.re| ≤ S/Real.log T → 1+‖beta‖ ≤ Z →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z →
      ‖alpha‖ ≤ 1/4 → ‖beta‖ ≤ 1/4 → alpha+beta ≠ 0 →
      ∀ Phi : ℝ → ℂ, ContDiff ℝ ∞ Phi → Function.support Phi ⊆ Icc (1:ℝ) 2 →
      let a := fun n => (PRZZGCoefficient.coefficient js n:ℂ)
      let L := PRZZLiteralExhaustion.spatialLength T
      ‖arithmeticResidual P F Phi Kgrid J N a T eCut alpha beta‖ ≤
        ‖zeroMismatch P F Phi Kgrid N a T eCut alpha beta‖+
          (gridBudget caps w C js K Kgrid L J N eps eta b T eCut Phi alpha beta+
            gridBudget caps w C js K Kgrid L J N eps eta b T eCut
              (PRZZKeptLiteral.dualProfile Phi T alpha beta) (-beta) (-alpha))+
          ‖branchPair (fun Phi alpha beta => negativePart P F Phi Kgrid L J N a T eCut alpha beta)
            Phi T alpha beta‖+
          ‖branchPair (fun Phi alpha beta => tailPart P F Phi Kgrid L J N a T eCut alpha beta)
            Phi T alpha beta‖ := by
  obtain ⟨caps,w,C,hC,hw,h⟩ := positive_grid_bound hWeil hDI K hK js eps eta b S Z
    heps heta hb hS hZ P F hP hF hPl hPr hFl hFr
  refine ⟨caps,w,C,hC,hw,?_⟩
  intro Kgrid J N T eCut alpha beta hN hNT hlog hbeta hzb halpha hza ha hb' hs Phi hPhi hsPhi
  dsimp only
  have hd : ContDiff ℝ ∞ (PRZZKeptLiteral.dualProfile Phi T alpha beta) :=
    hPhi.mul ((PRZZDualSmooth.multiplier_contDiff alpha beta ha hb').comp
      (contDiff_const.mul contDiff_id))
  have hsd := (PRZZKeptLiteral.dual_profile_regular Phi hPhi.continuous hsPhi T alpha beta ha hb').2
  apply arithmetic_residual_bound
  · exact h Kgrid _ J N T eCut alpha beta hN hNT hlog hbeta hzb halpha hs Phi hPhi hsPhi
  · exact h Kgrid _ J N T eCut (-beta) (-alpha) hN hNT hlog
      (by simpa using halpha) (by simpa using hza) (by simpa using hbeta)
      (by rw [show -beta+-alpha = -(alpha+beta) by ring]; exact neg_ne_zero.mpr hs)
      _ hd hsd

#print axioms scaled_shift_conditions
#print axioms frequency_positive
#print axioms positive_grid_bound
#print axioms arithmetic_residual_bound
#print axioms paired_residual_weil_di
end XiPrime8845.PRZZCentralGridWeilDI
