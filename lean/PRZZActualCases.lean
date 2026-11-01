import PRZZActualSmall

/-! Join the three analytic cases on the original retained HB rows.
The two deep estimates are explicit inputs. No CellBound premise is used.
The small part and the decaying large part are kept separate. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset
namespace XiPrime8845.PRZZActualCases
open PRZZActualBranchCells PRZZHBBranches PRZZAStarNu PRZZNuCoefficient
set_option maxHeartbeats 3000000

/-- An empty retained row is literally zero, including all frequency
fibers. This closes the zero alternative before classifying live cells. -/
theorem source_zero (N d j l h : ℕ) (hd : 0 < d) (hh : 0 < h)
    (A : ℝ) (b : Branch) (k : Fin b.2.length → ℕ)
    (right : ℕ → ℂ) (F1 F2 FM : ℝ → ℂ) (alpha beta : ℂ)
    (x t : ℝ) (np nm : ℕ → ℂ)
    (hz : ∀ n ≤ N, PRZZRowWindow.lo h j ≤ n → n ≤ PRZZRowWindow.hi N d h j →
      group N b k univ n = 0) :
    PRZZSignedSourceCell.source N d j l h A b k right F1 F2 FM alpha beta x t np nm = 0 := by
  have hrow (v : ℤ) : (∑ n ∈ Icc 1 N,
      if d.Coprime n ∧ d*(h*n) ≤ N then
        (group N b k univ n:ℂ)*PRZZSupportedBranches.row N d j l (fun _ => 1)
          right F1 F2 FM alpha beta x t v (h*n) else 0) = 0 := by
    apply sum_eq_zero; intro n hn
    split_ifs with hcut
    · by_cases hm : h*n ∈ PRZZDyadic.cell N j
      · have hw := (PRZZRowWindow.test N d h j n hd hh).mp ⟨hm,hcut.2⟩
        simp [hz n (mem_Icc.mp hn).2 hw.1 hw.2]
      · simp [PRZZSupportedBranches.row,hm]
    · rfl
  simp only [PRZZSignedSourceCell.source,hrow,mul_zero,sum_const_zero,add_zero]

theorem bound_of_retained (N d j l h : ℕ) (hd : 0 < d) (hh : 0 < h)
    (A : ℝ) (b : Branch) (k : Fin b.2.length → ℕ)
    (right : ℕ → ℂ) (F1 F2 FM : ℝ → ℂ) (alpha beta : ℂ)
    (x t : ℝ) (np nm : ℕ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ n ≤ N, PRZZRowWindow.lo h j ≤ n → n ≤ PRZZRowWindow.hi N d h j →
      group N b k univ n ≠ 0 →
      ‖PRZZSignedSourceCell.source N d j l h A b k right F1 F2 FM alpha beta x t np nm‖ ≤ B) :
    ‖PRZZSignedSourceCell.source N d j l h A b k right F1 F2 FM alpha beta x t np nm‖ ≤ B := by
  by_cases he : ∃ n ≤ N, PRZZRowWindow.lo h j ≤ n ∧ n ≤ PRZZRowWindow.hi N d h j ∧ group N b k univ n ≠ 0
  · obtain ⟨n,hn,hl,hu,hz⟩ := he
    exact hb n hn hl hu hz
  · rw [source_zero N d j l h hd hh A b k right F1 F2 FM alpha beta x t np nm (by
      intro n hn hl hu
      by_contra hz
      exact he ⟨n,hn,hl,hu,hz⟩),norm_zero]
    exact hB

theorem complementary_support (N y K : ℕ) (ks : List ℕ) (b : Branch)
    (hb : b ∈ branches y K ks) (k : Fin b.2.length → ℕ)
    (i : Fin b.2.length) (n : ℕ) (hn : n ≤ N) (hz : group N b k univ n ≠ 0)
    (T : ℝ) (hNT : (N:ℝ) ≤ T) :
    (∏ a ∈ univ.erase i, (2:ℝ)^(k a+1)) ≤ 2^((ks.length+1)*(2*K))*T := by
  have hs : (∏ a ∈ univ.erase i, (2:ℝ)^(k a)) ≤ ∏ a, (2:ℝ)^(k a) :=
    prod_le_prod_of_subset_of_one_le (erase_subset _ _)
      (fun a _ => by positivity) (fun a _ _ => one_le_pow₀ (by norm_num))
  have hl : (∏ a, (2:ℝ)^(k a)) ≤ n := by exact_mod_cast (group_support N b k univ n hz).1
  exact PRZZCellMass.upper_support y K ks b hb k _ T
    (hs.trans (hl.trans ((by exact_mod_cast hn : (n:ℝ) ≤ N).trans hNT)))

theorem retained_source_bound
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (ks js : List ℕ) (eps eta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (F0 F2 FM : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM) :
    ∃ Cs Ci Cg Cd Cr Cp Cv : ℝ,
      0 < Cs ∧ 0 < Ci ∧ 0 < Cg ∧ 0 < Cd ∧ 0 < Cr ∧ 0 < Cp ∧ 0 < Cv ∧
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
  obtain ⟨Cs,hCs,hs⟩ := PRZZActualSmall.small_source F0 F2 FM hf.continuous hc hF hcF hM hcM K ks js eta S heta hS
  obtain ⟨Ci,hCi,hi⟩ := PRZZActualTypeI.retained_source_bound hWeil F0 F2 FM hf hc hF hcF hM hcM
    K hK ks js eps eta S Z heps heta hS hZ
  obtain ⟨Cg,Cd,Cr,Cp,Cv,hCg,hCd,hCr,hCp,hCv,hii⟩ :=
    PRZZActualBudgetLayout.actual_source_bound hDI K hK ks js eps eta S Z heps heta hS hZ
      F0 F2 FM hf hc hF hcF hM hcM
  refine ⟨Cs,Ci,Cg,Cd,Cr,Cp,Cv,hCs,hCi,hCg,hCd,hCr,hCp,hCv,?_⟩
  intro N d j l h b hb k n hn hl hu hnz T Q D H x y0 t alpha beta hN hd hh hT hNT hdT hhT hA ha hz hbeta
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
  · have hbnd := hs N _ d j l h b hb k U T Q x y0 t D H _ alpha beta rfl hsmall hN hd hT
      (by linarith) hA ha hbeta
    exact hbnd.trans (by dsimp [c] at *; linarith)
  · rcases hii N d j l h b hN hd hh hb k U rfl n hn hl hu hnz T Q D H x y0 t _
      hT hNT hhT hA alpha beta ha hz hbeta with hs' | hf' | hbnd
    · exact (hsmall hs').elim
    · obtain ⟨i,_,hbig,hrest⟩ := hf'
      have hbnd := hi N d j l h b hb k i U T Q x y0 t D H alpha beta rfl hrest
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

#print axioms complementary_support
#print axioms retained_source_bound
#print axioms source_zero
#print axioms bound_of_retained
theorem source_bound
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (ks js : List ℕ) (eps eta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (F0 F2 FM : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM) :
    ∃ Cs Ci Cg Cd Cr Cp Cv : ℝ,
      0 < Cs ∧ 0 < Ci ∧ 0 < Cg ∧ 0 < Cd ∧ 0 < Cr ∧ 0 < Cp ∧ 0 < Cv ∧
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
    retained_source_bound hWeil hDI K hK ks js eps eta S Z heps heta hS hZ F0 F2 FM hf hc hF hcF hM hcM
  refine ⟨Cs,Ci,Cg,Cd,Cr,Cp,Cv,hCs,hCi,hCg,hCd,hCr,hCp,hCv,?_⟩
  intro N d j l h b hb k T Q D H x y0 t alpha beta hN hd hh hT hNT hdT hhT hA ha hz hbeta
  dsimp only
  apply bound_of_retained N d j l h hd hh
  · have hlog : 0 ≤ Real.log ((N:ℝ)+1) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
    unfold PRZZCommonCellBound.budget PRZZCombinedBudget.total PRZZCombinedBudget.typeI PRZZDISeven.envelope
    positivity
  · intro n hn hl hu hnz
    exact hbnd N d j l h b hb k n hn hl hu hnz T Q D H x y0 t alpha beta hN hd hh hT hNT hdT hhT hA ha hz hbeta

#print axioms source_bound

end XiPrime8845.PRZZActualCases
