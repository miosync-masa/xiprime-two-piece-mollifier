import PRZZPositiveRow

/-! The actual signed source cell, with both original frequencies, is
identified with the pair of DI matrices before applying the supplied
arithmetic envelopes. Physical balanced scale allocation is separate. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZSignedSourceCell
open PRZZActualBranchCells PRZZActualSupportBoxes PRZZHBBranches PRZZAStarNu PRZZNuCoefficient
set_option maxHeartbeats 3000000

def source (N d j l h : ℕ) (A : ℝ) (b : Branch)
    (k : Fin b.2.length → ℕ) (right : ℕ → ℂ) (F1 F2 FM : ℝ → ℂ)
    (alpha beta : ℂ) (x t : ℝ) (np nm : ℕ → ℂ) : ℂ :=
  (∑ a ∈ Icc 1 ⌊A⌋₊, np a*∑ n ∈ Icc 1 N,
    if d.Coprime n ∧ d*(h*n) ≤ N then
      (group N b k univ n:ℂ)*PRZZSupportedBranches.row N d j l (fun _ => 1)
        right F1 F2 FM alpha beta x t (a:ℤ) (h*n) else 0)+
  (∑ a ∈ Icc 1 ⌊A⌋₊, nm a*∑ n ∈ Icc 1 N,
    if d.Coprime n ∧ d*(h*n) ≤ N then
      (group N b k univ n:ℂ)*PRZZSupportedBranches.row N d j l (fun _ => 1)
        right F1 F2 FM alpha beta x t (-(a:ℤ)) (h*n) else 0)

theorem source_eq (N d j l h : ℕ) (A : ℝ) (b : Branch)
    (k : Fin b.2.length → ℕ) (s : Finset (Fin b.2.length))
    (right : ℕ → ℂ) (F1 F2 FM : ℝ → ℂ) (alpha beta : ℂ)
    (x t : ℝ) (np nm : ℕ → ℂ) :
    source N d j l h A b k right F1 F2 FM alpha beta x t np nm =
      PRZZWeightedDI.negative N N (upper N b k (univ \ s)) A (upper N b k s) h
        (PRZZAStarRectangles.secondCoeff N d l right F2 FM beta x t)
        (PRZZActualBranchDI.coefficient N b k (univ \ s) {n | d.Coprime n} (fun _ => 1)) np
        (PRZZActualBranchDI.coefficient N b k s {n | d.Coprime n} (fun _ => 1))
        (PRZZResidualRow.weight N d j h F1 alpha t)+
      PRZZWeightedDI.weighted N N (upper N b k (univ \ s)) A (upper N b k s) h
        (PRZZAStarRectangles.secondCoeff N d l right F2 FM beta x t)
        (PRZZActualBranchDI.coefficient N b k (univ \ s) {n | d.Coprime n} (fun _ => 1)) nm
        (PRZZActualBranchDI.coefficient N b k s {n | d.Coprime n} (fun _ => 1))
        (PRZZResidualRow.weight N d j h F1 alpha t) := by
  rw [source,PRZZPositiveRow.actual_row_eq N d j l h A b k s,
    PRZZActualRowRectangle.row_eq N d j l h A b k s]

theorem source_seven (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (ks js : List ℕ) (eps eta S : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S)
    (F2 FM : ℝ → ℂ) (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM) :
    ∃ Cg Cd Cr Cp : ℝ, 0 < Cg ∧ 0 < Cd ∧ 0 < Cr ∧ 0 < Cp ∧
      ∀ (N d y j l : ℕ) (b : Branch), 1 ≤ N → 1 ≤ d → b ∈ branches y K ks →
      ∀ k : Fin b.2.length → ℕ, ∀ s : Finset (Fin b.2.length),
      ∀ T D H x y0 t A : ℝ, 1 < T → (N:ℝ) ≤ T → 1 ≤ A →
      ∀ (rightF : ℝ → ℂ) (alpha beta : ℂ), |beta.re| ≤ S/Real.log T → ∀ h : ℕ, 1 ≤ h →
      let E : ℝ := upper N b k s
      let F : ℝ := upper N b k (univ \ s)
      ‖source N d j l h A b k (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) rightF F2 FM alpha beta x t
          (fun a => nu (frequencies d D H) x y0 (a:ℤ))
          (fun a => nu (frequencies d D H) x y0 (-(a:ℤ)))‖ ≤
        2*((1+2*Real.log ((⌊F⌋₊:ℝ)+1))*
          ((Cr*T^eta)*(Cg*F^eta)*((Cp*A^eta)*(Cg*E^eta))*Cd*
            (((N:ℝ)*F*A*E)^eps*PRZZDISeven.seven h E A (E*F) N)))*
              PRZZTypeI.variation (fun n => PRZZResidualRow.weight N d j h rightF alpha t (n+1)) N := by
  obtain ⟨Cg,Cd,Cr,Cp,hCg,hCd,hCr,hCp,hbound⟩ :=
    PRZZSourceGroupDI.source_seven hDI K ks js eps eta S heps heta hS F2 FM hF hcF hM hcM
  refine ⟨Cg,Cd,Cr,Cp,hCg,hCd,hCr,hCp,?_⟩
  intro N d y j l b hN hd hb k s T D H x y0 t A hT hNT hA rightF alpha beta hbeta h hh
  dsimp only
  have ht := hbound N d y l b hN hd hb k s T D H x y0 t N A hT hNT (by exact_mod_cast hN) hA beta hbeta h hh
    (PRZZResidualRow.weight N d j h rightF alpha t)
  rw [source_eq N d j l h A b k s]
  -- The source modulus range is the literal N, so specialize V=N.
  exact ht

#print axioms source_eq
#print axioms source_seven
end XiPrime8845.PRZZSignedSourceCell
