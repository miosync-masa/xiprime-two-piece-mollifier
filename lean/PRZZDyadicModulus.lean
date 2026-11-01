import PRZZSignedSourceCell

/-! The actual modulus support of a signed source cell. Only the modulus
summation endpoint changes; the sharp product cutoff, coefficient masks,
coprimality and both phases remain unchanged. DI is an explicit input. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZDyadicModulus
open PRZZActualBranchCells PRZZActualSupportBoxes PRZZHBBranches
open PRZZAStarNu PRZZNuCoefficient PRZZSignedSourceCell
set_option maxHeartbeats 2000000

def bound (N l : ℕ) : ℕ := min N (2^(l+1))

theorem bound_pos (N l : ℕ) (hN : 1 ≤ N) : 1 ≤ bound N l :=
  le_min hN (Nat.one_le_pow _ _ (by norm_num))

theorem second_zero (N d l : ℕ) (a : ℕ → ℂ) (F2 FM : ℝ → ℂ)
    (beta : ℂ) (x t : ℝ) (n : ℕ) (hn : bound N l < n) :
    PRZZAStarRectangles.secondCoeff N d l a F2 FM beta x t n = 0 := by
  unfold PRZZAStarRectangles.secondCoeff
  apply if_neg
  intro hs
  rw [PRZZDyadic.mem_cell] at hs
  have hh : n ≤ bound N l := le_min (mem_Icc.mp hs.1.1).2 hs.1.2.2.le
  omega

theorem weighted_restrict (N M Q : ℕ) (hMQ : M ≤ Q) (F A E : ℝ) (h : ℕ)
    (r beta nu alpha w : ℕ → ℂ) (hr : ∀ n, M < n → r n = 0) :
    PRZZWeightedDI.weighted N Q F A E h r beta nu alpha w =
      PRZZWeightedDI.weighted N M F A E h r beta nu alpha w := by
  unfold PRZZWeightedDI.weighted
  simp only [Nat.floor_natCast]
  symm
  apply sum_subset (Icc_subset_Icc le_rfl hMQ)
  intro n hn hnot
  have hz : r n = 0 := hr n (by have := (mem_Icc.mp hn).1; simp only [mem_Icc] at hnot; omega)
  simp [hz]

theorem negative_restrict (N M Q : ℕ) (hMQ : M ≤ Q) (F A E : ℝ) (h : ℕ)
    (r beta nu alpha w : ℕ → ℂ) (hr : ∀ n, M < n → r n = 0) :
    PRZZWeightedDI.negative N Q F A E h r beta nu alpha w =
      PRZZWeightedDI.negative N M F A E h r beta nu alpha w := by
  rw [PRZZWeightedDI.negative_eq,PRZZWeightedDI.negative_eq,
    weighted_restrict N M Q hMQ]
  intro n hn
  simp [hr n hn]

theorem source_eq_dyadic (N d j l h : ℕ) (A : ℝ) (b : Branch)
    (k : Fin b.2.length → ℕ) (s : Finset (Fin b.2.length))
    (right : ℕ → ℂ) (F1 F2 FM : ℝ → ℂ) (alpha beta : ℂ)
    (x t : ℝ) (np nm : ℕ → ℂ) :
    source N d j l h A b k right F1 F2 FM alpha beta x t np nm =
      PRZZWeightedDI.negative N (bound N l) (upper N b k (univ \ s)) A (upper N b k s) h
        (PRZZAStarRectangles.secondCoeff N d l right F2 FM beta x t)
        (PRZZActualBranchDI.coefficient N b k (univ \ s) {n | d.Coprime n} (fun _ => 1)) np
        (PRZZActualBranchDI.coefficient N b k s {n | d.Coprime n} (fun _ => 1))
        (PRZZResidualRow.weight N d j h F1 alpha t)+
      PRZZWeightedDI.weighted N (bound N l) (upper N b k (univ \ s)) A (upper N b k s) h
        (PRZZAStarRectangles.secondCoeff N d l right F2 FM beta x t)
        (PRZZActualBranchDI.coefficient N b k (univ \ s) {n | d.Coprime n} (fun _ => 1)) nm
        (PRZZActualBranchDI.coefficient N b k s {n | d.Coprime n} (fun _ => 1))
        (PRZZResidualRow.weight N d j h F1 alpha t) := by
  rw [source_eq,negative_restrict N (bound N l) N (min_le_left _ _),
    weighted_restrict N (bound N l) N (min_le_left _ _)]
  all_goals exact second_zero N d l right F2 FM beta x t

theorem source_seven_dyadic (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
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
      let V : ℝ := bound N l
      ‖source N d j l h A b k (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) rightF F2 FM alpha beta x t
          (fun a => nu (frequencies d D H) x y0 (a:ℤ))
          (fun a => nu (frequencies d D H) x y0 (-(a:ℤ)))‖ ≤
        2*((1+2*Real.log ((⌊F⌋₊:ℝ)+1))*
          ((Cr*T^eta)*(Cg*F^eta)*((Cp*A^eta)*(Cg*E^eta))*Cd*
            ((V*F*A*E)^eps*PRZZDISeven.seven h E A (E*F) V)))*
              PRZZTypeI.variation (fun n => PRZZResidualRow.weight N d j h rightF alpha t (n+1)) N := by
  obtain ⟨Cg,Cd,Cr,Cp,hCg,hCd,hCr,hCp,hbound⟩ :=
    PRZZSourceGroupDI.source_seven hDI K ks js eps eta S heps heta hS F2 FM hF hcF hM hcM
  refine ⟨Cg,Cd,Cr,Cp,hCg,hCd,hCr,hCp,?_⟩
  intro N d y j l b hN hd hb k s T D H x y0 t A hT hNT hA rightF alpha beta hbeta h hh
  dsimp only
  rw [source_eq_dyadic N d j l h A b k s]
  exact hbound N d y l b hN hd hb k s T D H x y0 t (bound N l) A hT hNT
    (by exact_mod_cast bound_pos N l hN) hA beta hbeta h hh _

#print axioms bound_pos
#print axioms second_zero
#print axioms weighted_restrict
#print axioms negative_restrict
#print axioms source_eq_dyadic
#print axioms source_seven_dyadic
end XiPrime8845.PRZZDyadicModulus
