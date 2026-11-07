import PRZZUniformCases

/-! One arithmetic budget for the entire two-scale family. All constants
and allocation caps are selected BEFORE Q2,QM and all heights. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset
namespace XiPrime8845.PRZZUniformAggregate
set_option maxHeartbeats 10000000

private theorem list_scale {α : Type*} (s : List α) (f : α → ℝ) (r : ℝ) :
    (s.map (fun q => f q*r)).sum = (s.map f).sum*r := by
  induction s with
  | nil => simp
  | cons a s ih => simp only [List.map_cons,List.sum_cons]; rw [ih]; ring

section
open PRZZActualCases
open Finset
open PRZZActualBranchCells PRZZHBBranches PRZZAStarNu PRZZNuCoefficient
theorem case_retained
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (ks js : List ℕ) (eps eta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (F0 F2 FM : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM) :
    ∃ Cs Ci Cg Cd Cr Cp Cv : ℝ,
      0 < Cs ∧ 0 < Ci ∧ 0 < Cg ∧ 0 < Cd ∧ 0 < Cr ∧ 0 < Cp ∧ 0 < Cv ∧
      ∀ Q2 QM : ℝ, ∀ N d j l h : ℕ, ∀ b ∈ branches ⌊(PRZZRowWindow.hi N d h j:ℝ)^((K:ℝ)⁻¹)⌋₊ K ks,
      ∀ k : Fin b.2.length → ℕ, ∀ n : ℕ, n ≤ N →
      PRZZRowWindow.lo h j ≤ n → n ≤ PRZZRowWindow.hi N d h j → group N b k univ n ≠ 0 →
      ∀ T Q D H x y0 t : ℝ, ∀ alpha beta : ℂ,
      0 < N → 0 < d → 0 < h → 1 < T → (N:ℝ)+1 ≤ T → (d:ℝ) ≤ T → (h:ℝ) ≤ T →
      1 ≤ (PRZZActualSignedBranches.frequencyBound d D H:ℝ) →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z → |beta.re| ≤ S/Real.log T →
      let c : ℝ := 2^((ks.length+1)*(2*K))
      let X : ℝ := (2:ℝ)^j/c
      let A : ℝ := PRZZActualSignedBranches.frequencyBound d D H
      ‖PRZZSignedSourceCell.source N d j l h A b k
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (PRZZMellinSeparation.scaledCutoff F0 Q) (PRZZMellinSeparation.scaledCutoff F2 Q2) (PRZZMellinSeparation.scaledCutoff FM QM) alpha beta x t
        (fun a => nu (frequencies d D H) x y0 (a:ℤ))
        (fun a => nu (frequencies d D H) x y0 (-(a:ℤ)))‖ ≤
      Cs*T^eta*A^eta*A*((2:ℝ)^(l+1)) +
      Ci*(c*T)^eta*(1+|t|)*(T^eta*T^eta*T^eta)*A^eta*((2:ℝ)^(l+1))^eps*
        (PRZZCombinedBudget.typeI X A ((2:ℝ)^l)/(h:ℝ)^(1/4:ℝ)) +
      PRZZCommonCellBound.budget Cg Cd Cr Cp Cv eps eta N T A t *
        (((2*c)*(2*c^2)^2)*(PRZZCombinedBudget.total X A (PRZZDyadicModulus.bound N l)/(h:ℝ)^(1/4:ℝ))) := by
  obtain ⟨Cs,hCs,hs⟩ := PRZZUniformCases.small_source F0 F2 FM hf.continuous hc hF hcF hM hcM K ks js eta S heta hS
  obtain ⟨Ci,hCi,hi⟩ := PRZZUniformTypeI.typeI_retained hWeil F0 F2 FM hf hc hF hcF hM hcM
    K hK ks js eps eta S Z heps heta hS hZ
  obtain ⟨Cg,Cd,Cr,Cp,Cv,hCg,hCd,hCr,hCp,hCv,hii⟩ :=
    PRZZUniformCases.di_actual hDI K hK ks js eps eta S Z heps heta hS hZ
      F0 F2 FM hf hc hF hcF hM hcM
  refine ⟨Cs,Ci,Cg,Cd,Cr,Cp,Cv,hCs,hCi,hCg,hCd,hCr,hCp,hCv,?_⟩
  intro Q2 QM N d j l h b hb k n hn hl hu hnz T Q D H x y0 t alpha beta hN hd hh hT hNT hdT hhT hA ha hz hbeta
  let F2 := PRZZMellinSeparation.scaledCutoff F2 Q2
  let FM := PRZZMellinSeparation.scaledCutoff FM QM
  dsimp only
  let U : ℝ := ∏ a, (2:ℝ)^(k a)
  let c : ℝ := 2^((ks.length+1)*(2*K))
  have hlog : 0 ≤ Real.log ((N:ℝ)+1) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
  have hsmall0 : 0 ≤ Cs*T^eta*(PRZZActualSignedBranches.frequencyBound d D H:ℝ)^eta*
      (PRZZActualSignedBranches.frequencyBound d D H:ℝ)*((2:ℝ)^(l+1)) := by positivity
  have hlarge0 : 0 ≤ Ci*(c*T)^eta*(1+|t|)*(T^eta*T^eta*T^eta)*
      (PRZZActualSignedBranches.frequencyBound d D H:ℝ)^eta*((2:ℝ)^(l+1))^eps*
      (PRZZCombinedBudget.typeI ((2:ℝ)^j/c) (PRZZActualSignedBranches.frequencyBound d D H)
        ((2:ℝ)^l)/(h:ℝ)^(1/4:ℝ)) := by unfold PRZZCombinedBudget.typeI; positivity
  have hII0 : 0 ≤ PRZZCommonCellBound.budget Cg Cd Cr Cp Cv eps eta N T
      (PRZZActualSignedBranches.frequencyBound d D H) t *
      (((2*c)*(2*c^2)^2)*(PRZZCombinedBudget.total ((2:ℝ)^j/c)
        (PRZZActualSignedBranches.frequencyBound d D H) (PRZZDyadicModulus.bound N l)/(h:ℝ)^(1/4:ℝ))) := by
    unfold PRZZCommonCellBound.budget PRZZCombinedBudget.total PRZZCombinedBudget.typeI PRZZDISeven.envelope
    positivity
  by_cases hsmall : U ≤ 2*c
  · have hbnd := hs Q2 QM N _ d j l h b hb k U T Q x y0 t D H _ alpha beta rfl hsmall hN hd hT
      (by linarith) hA ha hbeta
    exact hbnd.trans (by dsimp [c] at *; linarith)
  · rcases hii Q2 QM N d j l h b hN hd hh hb k U rfl n hn hl hu hnz T Q D H x y0 t _
      hT hNT hhT hA alpha beta ha hz hbeta with hs' | hf' | hbnd
    · exact (hsmall hs').elim
    · obtain ⟨i,_,hbig,hrest⟩ := hf'
      have hbnd := hi Q2 QM N d j l h b hb k i U T Q x y0 t D H alpha beta rfl hrest
        (lt_of_not_ge hsmall) hbig n hl hu hnz hN hd hh hdT hT hNT ha hz hbeta
      have hsupport := complementary_support N _ K ks b hb k i n hn hnz T (by linarith)
      have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ ∏ a ∈ univ.erase i, (2:ℝ)^(k a+1)) hsupport heta.le
      have hbound : _ ≤ Ci*(c*T)^eta*(1+|t|)*(T^eta*T^eta*T^eta)*
          (PRZZActualSignedBranches.frequencyBound d D H:ℝ)^eta*((2:ℝ)^(l+1))^eps*
          (PRZZCombinedBudget.typeI ((2:ℝ)^j/c) (PRZZActualSignedBranches.frequencyBound d D H)
            ((2:ℝ)^l)/(h:ℝ)^(1/4:ℝ)) := hbnd.trans (by
        unfold PRZZCombinedBudget.typeI
        gcongr)
      exact hbound.trans (by dsimp [c] at *; linarith)
    · exact hbnd.trans (by dsimp [c] at *; linarith)

end

#print axioms case_retained

section
open PRZZActualCases
open Finset
open PRZZActualBranchCells PRZZHBBranches PRZZAStarNu PRZZNuCoefficient
theorem case_source
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (ks js : List ℕ) (eps eta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (F0 F2 FM : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM) :
    ∃ Cs Ci Cg Cd Cr Cp Cv : ℝ,
      0 < Cs ∧ 0 < Ci ∧ 0 < Cg ∧ 0 < Cd ∧ 0 < Cr ∧ 0 < Cp ∧ 0 < Cv ∧
      ∀ Q2 QM : ℝ, ∀ N d j l h : ℕ, ∀ b ∈ branches ⌊(PRZZRowWindow.hi N d h j:ℝ)^((K:ℝ)⁻¹)⌋₊ K ks,
      ∀ k : Fin b.2.length → ℕ,
      ∀ T Q D H x y0 t : ℝ, ∀ alpha beta : ℂ,
      0 < N → 0 < d → 0 < h → 1 < T → (N:ℝ)+1 ≤ T → (d:ℝ) ≤ T → (h:ℝ) ≤ T →
      1 ≤ (PRZZActualSignedBranches.frequencyBound d D H:ℝ) →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z → |beta.re| ≤ S/Real.log T →
      let c : ℝ := 2^((ks.length+1)*(2*K))
      let X : ℝ := (2:ℝ)^j/c
      let A : ℝ := PRZZActualSignedBranches.frequencyBound d D H
      ‖PRZZSignedSourceCell.source N d j l h A b k
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (PRZZMellinSeparation.scaledCutoff F0 Q) (PRZZMellinSeparation.scaledCutoff F2 Q2) (PRZZMellinSeparation.scaledCutoff FM QM) alpha beta x t
        (fun a => nu (frequencies d D H) x y0 (a:ℤ))
        (fun a => nu (frequencies d D H) x y0 (-(a:ℤ)))‖ ≤
      Cs*T^eta*A^eta*A*((2:ℝ)^(l+1)) +
      Ci*(c*T)^eta*(1+|t|)*(T^eta*T^eta*T^eta)*A^eta*((2:ℝ)^(l+1))^eps*
        (PRZZCombinedBudget.typeI X A ((2:ℝ)^l)/(h:ℝ)^(1/4:ℝ)) +
      PRZZCommonCellBound.budget Cg Cd Cr Cp Cv eps eta N T A t *
        (((2*c)*(2*c^2)^2)*(PRZZCombinedBudget.total X A (PRZZDyadicModulus.bound N l)/(h:ℝ)^(1/4:ℝ))) := by
  obtain ⟨Cs,Ci,Cg,Cd,Cr,Cp,Cv,hCs,hCi,hCg,hCd,hCr,hCp,hCv,hbnd⟩ :=
    case_retained hWeil hDI K hK ks js eps eta S Z heps heta hS hZ F0 F2 FM hf hc hF hcF hM hcM
  refine ⟨Cs,Ci,Cg,Cd,Cr,Cp,Cv,hCs,hCi,hCg,hCd,hCr,hCp,hCv,?_⟩
  intro Q2 QM N d j l h b hb k T Q D H x y0 t alpha beta hN hd hh hT hNT hdT hhT hA ha hz hbeta
  let F2 := PRZZMellinSeparation.scaledCutoff F2 Q2
  let FM := PRZZMellinSeparation.scaledCutoff FM QM
  dsimp only
  apply bound_of_retained N d j l h hd hh
  · have hlog : 0 ≤ Real.log ((N:ℝ)+1) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
    unfold PRZZCommonCellBound.budget PRZZCombinedBudget.total PRZZCombinedBudget.typeI PRZZDISeven.envelope
    positivity
  · intro n hn hl hu hnz
    exact hbnd Q2 QM N d j l h b hb k n hn hl hu hnz T Q D H x y0 t alpha beta hN hd hh hT hNT hdT hhT hA ha hz hbeta

end

#print axioms case_source

section
open PRZZActualAggregate
open Finset
open PRZZActualCaseSum PRZZAllSignedSources PRZZCoefficientSeparation
open PRZZSupportedSplit PRZZGCoefficient PRZZAStarNu
theorem actual_blocks
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (ks js : List ℕ) (eps eta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (F0 F2 FM : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM) :
    ∃ c : Caps, ∃ C : ℝ, 0 < C ∧
      ∀ Q2 QM : ℝ, ∀ N d h j l : ℕ, ∀ T Q D H x y t : ℝ, ∀ alpha beta : ℂ,
      0 < N → 0 < d → 0 < h → 1 < T → (N:ℝ)+1 ≤ T →
      (d:ℝ) ≤ T → (h:ℝ) ≤ T → 1 ≤ Real.log T →
      1 ≤ (PRZZActualSignedBranches.frequencyBound d D H:ℝ) →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z → |beta.re| ≤ S/Real.log T →
      ‖blocks N d h j l K ks js D H x y t
        (PRZZMellinSeparation.scaledCutoff F0 Q) (PRZZMellinSeparation.scaledCutoff F2 Q2) (PRZZMellinSeparation.scaledCutoff FM QM) alpha beta‖ ≤
      C*T^eta*row c eps eta T (PRZZActualSignedBranches.frequencyBound d D H) N K j l ks*(1+|t|) := by
  obtain ⟨Cs,Ci,Cg,Cd,Cr,Cp,Cv,hs,hi,hg,hd,hr,hp,hv,hsource⟩ :=
    case_source hWeil hDI K hK ks js eps eta S Z heps heta hS hZ F0 F2 FM hf hc hF hcF hM hcM
  let c : Caps := ⟨Cs,Ci,Cg,Cd,Cr,Cp,Cv,hs,hi,hg,hd,hr,hp,hv⟩
  obtain ⟨C,hC,hblocks⟩ := blocks_bound K ks eta heta
  refine ⟨c,C,hC,?_⟩
  intro Q2 QM N d h j l T Q D H x y t alpha beta hN hd0 hh hT hNT hdT hhT hlog hA ha hz hb
  let F2 := PRZZMellinSeparation.scaledCutoff F2 Q2
  let FM := PRZZMellinSeparation.scaledCutoff FM QM
  let A : ℝ := PRZZActualSignedBranches.frequencyBound d D H
  have hrow := row_nonneg c eps eta T A N K j l ks (by linarith) (by dsimp [A]; positivity)
  have hlarge : 0 ≤ largeBudget Ci Cg Cd Cr Cp Cv eps eta T A t N K j l ks := by
    have hln : 0 ≤ Real.log ((N:ℝ)+1) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
    unfold largeBudget PRZZCommonCellBound.budget PRZZCombinedBudget.total PRZZCombinedBudget.typeI PRZZDISeven.envelope
    dsimp [A]
    positivity
  have hden : 1 ≤ (h:ℝ)^(1/4:ℝ) := Real.one_le_rpow (by exact_mod_cast hh) (by norm_num)
  have hbound := hblocks N d h j l hN T
    (row c eps eta T A N K j l ks*(1+|t|)) (by linarith) hlog (by positivity)
    js D H x y t _ F2 FM alpha beta (by
      intro b hbr k
      have hh' := hsource Q2 QM N d j l h b hbr (fun i => (k i).val) T Q D H x y t alpha beta
        hN hd0 hh hT hNT hdT hhT hA ha hz hb
      have he : _ ≤ smallBudget Cs T A eta l+
          largeBudget Ci Cg Cd Cr Cp Cv eps eta T A t N K j l ks/(h:ℝ)^(1/4:ℝ) := hh'.trans_eq (by
        dsimp [smallBudget,largeBudget,A]; ring)
      apply he.trans
      apply (add_le_add_right (div_le_self hlarge hden) _).trans
      exact budget_linear_le Cs Ci Cg Cd Cr Cp Cv eps eta T A t N K j l ks (by
        dsimp [smallBudget,A]; positivity))
  exact hbound.trans_eq (by ring)

end

#print axioms actual_blocks

section
open PRZZActualAggregate
open Finset
open PRZZActualCaseSum PRZZAllSignedSources PRZZCoefficientSeparation
open PRZZSupportedSplit PRZZGCoefficient PRZZAStarNu
theorem signedSum_bound
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js : List ℕ) (eps eta beta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hbeta : 0 < beta) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (F0 F2 FM : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM) :
    ∃ caps : (List ℕ × List ℕ) → Caps, ∃ w : (List ℕ × List ℕ) → ℝ,
      ∃ C : ℝ, 0 < C ∧ (∀ q, 0 < w q) ∧
      ∀ Q2 QM : ℝ, ∀ N d : ℕ, ∀ T Q D H x y t : ℝ, ∀ alpha betaShift : ℂ,
      0 < N → 0 < d → 1 < T → (N:ℝ)+1 ≤ T → (d:ℝ) ≤ T → 1 ≤ Real.log T →
      1 ≤ (PRZZActualSignedBranches.frequencyBound d D H:ℝ) →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z → |betaShift.re| ≤ S/Real.log T →
      ‖signedSum N d D H (fun n => (coefficient js n:ℂ))
        (PRZZMellinSeparation.scaledCutoff F0 Q) (PRZZMellinSeparation.scaledCutoff F2 Q2) (PRZZMellinSeparation.scaledCutoff FM QM) alpha betaShift x y t‖ ≤
      totalBudget C w caps js eps eta beta T
        (PRZZActualSignedBranches.frequencyBound d D H) N d K*(1+|t|) := by
  choose caps w hw hblocks using fun q : List ℕ × List ℕ =>
    actual_blocks hWeil hDI K hK q.2 js eps eta S Z heps heta hS hZ F0 F2 FM hf hc hF hcF hM hcM
  obtain ⟨C,hC,halloc⟩ := PRZZAllCellsBound.allocation_bound js eta beta heta hbeta
  refine ⟨caps,w,C,hC,hw,?_⟩
  intro Q2 QM N d T Q D H x y t alpha betaShift hN hd hT hNT hdT hlog hA ha hz hb
  let F2 := PRZZMellinSeparation.scaledCutoff F2 Q2
  let FM := PRZZMellinSeparation.scaledCutoff FM QM
  let A : ℝ := PRZZActualSignedBranches.frequencyBound d D H
  rw [PRZZAllSignedSources.signedSum_eq N d K hd (by omega)]
  unfold totalBudget
  rw [sum_mul]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro j hj
  rw [sum_mul]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro l hl
  have hnq (q : List ℕ × List ℕ) :
      0 ≤ w q*T^eta*row (caps q) eps eta T A N K j l q.2 :=
    mul_nonneg (mul_nonneg (hw q).le (Real.rpow_nonneg (by linarith) eta))
      (row_nonneg _ _ _ _ _ _ _ _ _ _ (by linarith) (by dsimp [A]; positivity))
  have hh := halloc d N hd hN
    (fun q => (w q*T^eta*row (caps q) eps eta T A N K j l q.2)*(1+|t|))
    (fun q h => blocks N d h j l K q.2 js D H x y t
      (PRZZMellinSeparation.scaledCutoff F0 Q) F2 FM alpha betaShift)
    (fun q _ => mul_nonneg (hnq q) (by positivity)) (by
      intro q hq h hh
      have hs := mem_hSupport N d h hh
      have hhn : h ≤ N := by nlinarith [hs.2.1]
      exact hblocks q Q2 QM N d h j l T Q D H x y t alpha betaShift hN hd hs.1 hT hNT hdT
        ((by exact_mod_cast hhn : (h:ℝ) ≤ N).trans (by linarith)) hlog hA ha hz hb)
  rw [list_scale] at hh
  exact hh.trans_eq (by ring)

end

#print axioms signedSum_bound

end XiPrime8845.PRZZUniformAggregate
