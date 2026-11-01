import PRZZSignedSourceCell
import PRZZZeroExtension

/-! A common prefactor for all actual signed HB cells. Both frequency
coefficients and the literal smooth row are supplied, including variation
on the zero-extended interval. The seven-term factor remains visible;
this does not identify the small-scale or free Type I alternatives with DI. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset
namespace XiPrime8845.PRZZCommonCellBound
open PRZZActualBranchCells PRZZActualSupportBoxes PRZZHBBranches PRZZAStarNu PRZZNuCoefficient
set_option maxHeartbeats 3000000

def budget (Cg Cd Cr Cp Cv eps eta N T A t : ℝ) : ℝ :=
  2*((1+2*Real.log (N+1))*
    ((Cr*T^eta)*(Cg*N^eta)*((Cp*A^eta)*(Cg*N^eta))*Cd*
      ((N*N*A*N)^eps)))*(Cv*(1+|t|)*T^eta)

theorem source_bound (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
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
      ‖PRZZSignedSourceCell.source N d j l h A b k
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (PRZZMellinSeparation.scaledCutoff F0 Q) F2 FM alpha beta x t
        (fun a => nu (frequencies d D H) x y0 (a:ℤ))
        (fun a => nu (frequencies d D H) x y0 (-(a:ℤ)))‖ ≤
      budget Cg Cd Cr Cp Cv eps eta N T A t *
        PRZZDISeven.seven h (upper N b k s) A
          ((upper N b k s:ℝ)*(upper N b k (univ \ s):ℝ)) N := by
  obtain ⟨Cg,Cd,Cr,Cp,hCg,hCd,hCr,hCp,hb⟩ := PRZZSignedSourceCell.source_seven
    hDI K ks js eps eta S heps heta hS F2 FM hF hcF hM hcM
  obtain ⟨Cv,hCv,hv⟩ := PRZZZeroExtension.full_variation F0 hF0 hc0 eta S Z heta hS hZ
  refine ⟨Cg,Cd,Cr,Cp,Cv,hCg,hCd,hCr,hCp,hCv,?_⟩
  intro N d y j l h b hN hd hh hmem k s T Q D H x y0 t A hT hNT hhT hA alpha beta ha hz hbeta
  have hv' := hv N d h j T Q t alpha (by omega) (by omega) hT hNT hhT ha hz
  have hv0 : 0 ≤ PRZZTypeI.variation
      (fun n => PRZZResidualRow.weight N d j h (PRZZMellinSeparation.scaledCutoff F0 Q) alpha t (n+1)) N := by
    unfold PRZZTypeI.variation; positivity
  have hlog0 : 0 ≤ Real.log ((N:ℝ)+1) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
  have hb' := hb N d y j l b hN hd hmem k s T D H x y0 t A hT
    (by linarith) hA (PRZZMellinSeparation.scaledCutoff F0 Q) alpha beta hbeta h hh
  dsimp only at hb'
  have he : (upper N b k s:ℝ) ≤ N := by exact_mod_cast (bounds N hN b k s).2
  have hf : (upper N b k (univ \ s):ℝ) ≤ N := by
    exact_mod_cast (bounds N hN b k (univ \ s)).2
  have hseven : 0 ≤ PRZZDISeven.seven h (upper N b k s) A
      ((upper N b k s:ℝ)*(upper N b k (univ \ s):ℝ)) N := by
    unfold PRZZDISeven.seven; positivity
  have hlog : Real.log ((upper N b k (univ \ s):ℝ)+1) ≤ Real.log ((N:ℝ)+1) :=
    Real.log_le_log (by positivity) (by linarith)
  simp only [Nat.floor_natCast] at hb'
  apply hb'.trans
  unfold budget
  calc
    _ ≤ 2*((1+2*Real.log ((N:ℝ)+1))*
      ((Cr*T^eta)*(Cg*(N:ℝ)^eta)*((Cp*A^eta)*(Cg*(N:ℝ)^eta))*Cd*
        (((N:ℝ)*N*A*N)^eps*PRZZDISeven.seven h (upper N b k s) A
          ((upper N b k s:ℝ)*(upper N b k (univ \ s):ℝ)) N)))*
            (Cv*(1+|t|)*T^eta) := by
      gcongr <;> positivity
    _ = _ := by ring

#print axioms source_bound
end XiPrime8845.PRZZCommonCellBound
