import PRZZDyadicCellBound

/-! Actual DI cells with supplied smooth variation, followed by the
balanced seven-term comparison. Balance remains an explicit geometric
condition, not a claimed classification of all HB branches. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset
namespace XiPrime8845.PRZZBalancedCellEnvelope
open PRZZActualBranchCells PRZZActualSupportBoxes PRZZHBBranches PRZZAStarNu PRZZNuCoefficient
open PRZZCommonCellBound (budget)
set_option maxHeartbeats 3000000

theorem balanced_source_bound (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (ks js : List ℕ) (eps eta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (F0 F2 FM : ℝ → ℂ) (hF0 : ContDiff ℝ ∞ F0) (hc0 : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM) :
    ∃ Cg Cd Cr Cp Cv : ℝ, 0 < Cg ∧ 0 < Cd ∧ 0 < Cr ∧ 0 < Cp ∧ 0 < Cv ∧
      ∀ (N d y j l h : ℕ) (b : Branch), 1 ≤ N → 1 ≤ d → 1 ≤ h →
      b ∈ branches y K ks → ∀ k : Fin b.2.length → ℕ,
      ∀ s : Finset (Fin b.2.length), ∀ T Q D H x y0 t A : ℝ,
      1 < T → (N:ℝ)+1 ≤ T → (h:ℝ) ≤ T → 1 ≤ A →
      ∀ alpha beta : ℂ, |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z →
      |beta.re| ≤ S/Real.log T →
      (let E : ℝ := upper N b k s
       let U : ℝ := E*(upper N b k (univ \ s):ℝ)
       U^(1/4:ℝ) ≤ E ∧ E ≤ U^(1/2:ℝ)) →
      ‖PRZZSignedSourceCell.source N d j l h A b k
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (PRZZMellinSeparation.scaledCutoff F0 Q) F2 FM alpha beta x t
        (fun a => nu (frequencies d D H) x y0 (a:ℤ))
        (fun a => nu (frequencies d D H) x y0 (-(a:ℤ)))‖ ≤
      budget Cg Cd Cr Cp Cv eps eta N T A t *
        (∑ i : Fin 7, (h:ℝ)^(PRZZDISeven.hp i)*A^(PRZZDISeven.ap i)*
          ((upper N b k s:ℝ)*(upper N b k (univ \ s):ℝ))^(PRZZDISeven.balancedPower i)*
          (PRZZDyadicModulus.bound N l:ℝ)^(PRZZDISeven.vp i)) := by
  obtain ⟨Cg,Cd,Cr,Cp,Cv,hg,hd0,hr,hp,hv,hbound⟩ :=
    PRZZDyadicCellBound.source_bound hDI K ks js eps eta S Z heps heta hS hZ
      F0 F2 FM hF0 hc0 hF hcF hM hcM
  refine ⟨Cg,Cd,Cr,Cp,Cv,hg,hd0,hr,hp,hv,?_⟩
  intro N d y j l h b hN hd hh hb k s T Q D H x y0 t A hT hNT hhT hA alpha beta ha hz hbeta hbal
  have h := hbound N d y j l h b hN hd hh hb k s T Q D H x y0 t A
    hT hNT hhT hA alpha beta ha hz hbeta
  apply h.trans
  have he : (0:ℝ) < upper N b k s := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (bounds N hN b k s).1)
  have hf : (0:ℝ) < upper N b k (univ \ s) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (bounds N hN b k (univ \ s)).1)
  apply mul_le_mul_of_nonneg_left
    (PRZZDISeven.seven_balanced _ _ _ _ _ (Nat.cast_nonneg _) (by linarith)
      (mul_pos he hf) (Nat.cast_nonneg _) hbal.1 hbal.2)
  have hlog : 0 ≤ Real.log ((N:ℝ)+1) := Real.log_nonneg (by
    have := Nat.cast_nonneg (α := ℝ) N
    linarith)
  unfold budget
  positivity

#print axioms balanced_source_bound
end XiPrime8845.PRZZBalancedCellEnvelope
