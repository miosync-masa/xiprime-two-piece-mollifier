import PRZZClassTypeI
import PRZZActualCases

/-! Three actual analytic cases with constants fixed before the three
quantitative class members. Uses the original retained-root classifier;
empty rows vanish before classification. Weil and DI remain hypotheses. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset
namespace XiPrime8845.PRZZClassCases
open PRZZActualBranchCells PRZZHBBranches PRZZAStarNu PRZZNuCoefficient
open PRZZActualSupportBoxes PRZZCombinedBudget PRZZDISeven
open PRZZActualBudgetLayout PRZZActualCases
set_option maxHeartbeats 10000000

theorem actual_source_bound (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (ks js : List ℕ) (eps eta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (width : ℝ) (jets : ℕ → ℝ) (hjets : ∀ n, 0 ≤ jets n) :
    ∃ Cg Cd Cr Cp Cv : ℝ, 0 < Cg ∧ 0 < Cd ∧ 0 < Cr ∧ 0 < Cp ∧ 0 < Cv ∧
      ∀ F0 F2 FM : ℝ → ℂ, PRZZProfileMellin.Member width jets F0 →
      PRZZProfileMellin.Member width jets F2 → PRZZProfileMellin.Member width jets FM →
      ∀ (N d j l h : ℕ) (b : Branch), 1 ≤ N → 1 ≤ d → 1 ≤ h →
      b ∈ branches ⌊(PRZZRowWindow.hi N d h j:ℝ)^((K:ℝ)⁻¹)⌋₊ K ks → ∀ k : Fin b.2.length → ℕ,
      ∀ U : ℝ, (∏ i, (2:ℝ)^(k i)) = U →
      ∀ n : ℕ, n ≤ N → PRZZRowWindow.lo h j ≤ n →
      n ≤ PRZZRowWindow.hi N d h j → group N b k univ n ≠ 0 → ∀ T Q D H x y0 t A : ℝ,
      1 < T → (N:ℝ)+1 ≤ T → (h:ℝ) ≤ T → 1 ≤ A →
      ∀ alpha beta : ℂ, |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z →
      |beta.re| ≤ S/Real.log T →
      let c : ℝ := 2^((ks.length+1)*(2*K))
      let X : ℝ := (2:ℝ)^j/c
      U ≤ 2*c ∨ freeCase b k U ∨
      ‖PRZZSignedSourceCell.source N d j l h A b k
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (PRZZMellinSeparation.scaledCutoff F0 Q) F2 FM alpha beta x t
        (fun a => PRZZNuCoefficient.nu (PRZZAStarNu.frequencies d D H) x y0 (a:ℤ))
        (fun a => PRZZNuCoefficient.nu (PRZZAStarNu.frequencies d D H) x y0 (-(a:ℤ)))‖ ≤
      PRZZCommonCellBound.budget Cg Cd Cr Cp Cv eps eta N T A t *
        (((2*c)*(2*c^2)^2)*(total X A (PRZZDyadicModulus.bound N l)/(h:ℝ)^(1/4:ℝ))) := by
  obtain ⟨Cg,Cd,Cr,Cp,Cv,hg,hcd,hr,hcp,hcv,hbound⟩ :=
    PRZZClassDI.source_bound hDI K ks js eps eta S Z heps heta hS hZ
      width jets hjets
  refine ⟨Cg,Cd,Cr,Cp,Cv,hg,hcd,hr,hcp,hcv,?_⟩
  intro F0 F2 FM hf0 hf2 hfM N d j l h b hN hd hh hb k U hp n hn hl hu hnz T Q D H x y0 t A hT hNT hhT hA alpha beta ha hz hbeta
  dsimp only
  rcases actual_budget_layout N d h j K ks (by omega) (by omega) hK b hb k U hp n hn hl hu hnz
    A (PRZZDyadicModulus.bound N l) (by linarith) (Nat.cast_nonneg _) with hs | hf | ⟨s,hs⟩
  · exact Or.inl hs
  · exact Or.inr (Or.inl hf)
  · apply Or.inr ∘ Or.inr
    have hbnd := hbound F0 F2 FM hf0 hf2 hfM N d _ j l h b hN hd hh hb k s T Q D H x y0 t A hT hNT hhT hA alpha beta ha hz hbeta
    apply hbnd.trans
    have hU : 0 ≤ U := hp ▸ (by positivity)
    have ht : 0 ≤ typeI U A (PRZZDyadicModulus.bound N l) := by unfold typeI; positivity
    have hs' := (le_add_of_nonneg_left ht).trans hs
    apply mul_le_mul_of_nonneg_left hs'
    have hlog : 0 ≤ Real.log ((N:ℝ)+1) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
    unfold PRZZCommonCellBound.budget
    positivity

theorem retained_source_bound
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (ks js : List ℕ) (eps eta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (width : ℝ) (jets : ℕ → ℝ) (hjets : ∀ n, 0 ≤ jets n) :
    ∃ Cs Ci Cg Cd Cr Cp Cv : ℝ,
      0 < Cs ∧ 0 < Ci ∧ 0 < Cg ∧ 0 < Cd ∧ 0 < Cr ∧ 0 < Cp ∧ 0 < Cv ∧
      ∀ F0 F2 FM : ℝ → ℂ, PRZZProfileMellin.Member width jets F0 →
      PRZZProfileMellin.Member width jets F2 → PRZZProfileMellin.Member width jets FM →
      ∀ N d j l h : ℕ, ∀ b ∈ branches ⌊(PRZZRowWindow.hi N d h j:ℝ)^((K:ℝ)⁻¹)⌋₊ K ks,
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
        (PRZZMellinSeparation.scaledCutoff F0 Q) F2 FM alpha beta x t
        (fun a => nu (frequencies d D H) x y0 (a:ℤ))
        (fun a => nu (frequencies d D H) x y0 (-(a:ℤ)))‖ ≤
      Cs*T^eta*A^eta*A*((2:ℝ)^(l+1)) +
      Ci*(c*T)^eta*(1+|t|)*(T^eta*T^eta*T^eta)*A^eta*((2:ℝ)^(l+1))^eps*
        (PRZZCombinedBudget.typeI X A ((2:ℝ)^l)/(h:ℝ)^(1/4:ℝ)) +
      PRZZCommonCellBound.budget Cg Cd Cr Cp Cv eps eta N T A t *
        (((2*c)*(2*c^2)^2)*(PRZZCombinedBudget.total X A (PRZZDyadicModulus.bound N l)/(h:ℝ)^(1/4:ℝ))) := by
  obtain ⟨Cs,hCs,hs⟩ := PRZZClassSources.small_source_class K ks js eta S width heta hS jets hjets
  obtain ⟨Ci,hCi,hi⟩ := PRZZClassTypeI.retained_source_bound hWeil width jets hjets
    K hK ks js eps eta S Z heps heta hS hZ
  obtain ⟨Cg,Cd,Cr,Cp,Cv,hCg,hCd,hCr,hCp,hCv,hii⟩ :=
    actual_source_bound hDI K hK ks js eps eta S Z heps heta hS hZ
      width jets hjets
  refine ⟨Cs,Ci,Cg,Cd,Cr,Cp,Cv,hCs,hCi,hCg,hCd,hCr,hCp,hCv,?_⟩
  intro F0 F2 FM hf0 hf2 hfM N d j l h b hb k n hn hl hu hnz T Q D H x y0 t alpha beta hN hd hh hT hNT hdT hhT hA ha hz hbeta
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
  · have hbnd := hs F0 F2 FM hf0 hf2 hfM N _ d j l h b hb k U T Q x y0 t D H _ alpha beta rfl hsmall hN hd hT
      (by linarith) hA ha hbeta
    exact hbnd.trans (by dsimp [c] at *; linarith)
  · rcases hii F0 F2 FM hf0 hf2 hfM N d j l h b hN hd hh hb k U rfl n hn hl hu hnz T Q D H x y0 t _
      hT hNT hhT hA alpha beta ha hz hbeta with hs' | hf' | hbnd
    · exact (hsmall hs').elim
    · obtain ⟨i,_,hbig,hrest⟩ := hf'
      have hbnd := hi F0 F2 FM hf0 hf2 hfM N d j l h b hb k i U T Q x y0 t D H alpha beta rfl hrest
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

theorem source_bound
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (ks js : List ℕ) (eps eta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (width : ℝ) (jets : ℕ → ℝ) (hjets : ∀ n, 0 ≤ jets n) :
    ∃ Cs Ci Cg Cd Cr Cp Cv : ℝ,
      0 < Cs ∧ 0 < Ci ∧ 0 < Cg ∧ 0 < Cd ∧ 0 < Cr ∧ 0 < Cp ∧ 0 < Cv ∧
      ∀ F0 F2 FM : ℝ → ℂ, PRZZProfileMellin.Member width jets F0 →
      PRZZProfileMellin.Member width jets F2 → PRZZProfileMellin.Member width jets FM →
      ∀ N d j l h : ℕ, ∀ b ∈ branches ⌊(PRZZRowWindow.hi N d h j:ℝ)^((K:ℝ)⁻¹)⌋₊ K ks,
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
        (PRZZMellinSeparation.scaledCutoff F0 Q) F2 FM alpha beta x t
        (fun a => nu (frequencies d D H) x y0 (a:ℤ))
        (fun a => nu (frequencies d D H) x y0 (-(a:ℤ)))‖ ≤
      Cs*T^eta*A^eta*A*((2:ℝ)^(l+1)) +
      Ci*(c*T)^eta*(1+|t|)*(T^eta*T^eta*T^eta)*A^eta*((2:ℝ)^(l+1))^eps*
        (PRZZCombinedBudget.typeI X A ((2:ℝ)^l)/(h:ℝ)^(1/4:ℝ)) +
      PRZZCommonCellBound.budget Cg Cd Cr Cp Cv eps eta N T A t *
        (((2*c)*(2*c^2)^2)*(PRZZCombinedBudget.total X A (PRZZDyadicModulus.bound N l)/(h:ℝ)^(1/4:ℝ))) := by
  obtain ⟨Cs,Ci,Cg,Cd,Cr,Cp,Cv,hCs,hCi,hCg,hCd,hCr,hCp,hCv,hbnd⟩ :=
    retained_source_bound hWeil hDI K hK ks js eps eta S Z heps heta hS hZ width jets hjets
  refine ⟨Cs,Ci,Cg,Cd,Cr,Cp,Cv,hCs,hCi,hCg,hCd,hCr,hCp,hCv,?_⟩
  intro F0 F2 FM hf0 hf2 hfM N d j l h b hb k T Q D H x y0 t alpha beta hN hd hh hT hNT hdT hhT hA ha hz hbeta
  dsimp only
  apply bound_of_retained N d j l h hd hh
  · have hlog : 0 ≤ Real.log ((N:ℝ)+1) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
    unfold PRZZCommonCellBound.budget PRZZCombinedBudget.total PRZZCombinedBudget.typeI PRZZDISeven.envelope
    positivity
  · intro n hn hl hu hnz
    exact hbnd F0 F2 FM hf0 hf2 hfM N d j l h b hb k n hn hl hu hnz T Q D H x y0 t alpha beta hN hd hh hT hNT hdT hhT hA ha hz hbeta

#print axioms actual_source_bound
#print axioms retained_source_bound
#print axioms source_bound
end XiPrime8845.PRZZClassCases
