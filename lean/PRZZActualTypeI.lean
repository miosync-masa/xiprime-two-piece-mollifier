import PRZZActualBudgetLayout
import PRZZTypeIScaleSupplier
import PRZZActualSignedBranches

/-! Literal signed-source Type I evaluation. Both signs and frequency
fiber multiplicities are preserved; the original retained row supplies
the root-cutoff condition. Weil is an explicit hypothesis. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset
namespace XiPrime8845.PRZZActualTypeI
open PRZZActualBranchCells PRZZHBBranches PRZZActualSignedBranches
open PRZZAStarNu PRZZNuCoefficient
set_option maxHeartbeats 3000000

theorem source_eq_signed (N d j l h : ℕ) (b : Branch)
    (k : Fin b.2.length → ℕ) (js : List ℕ) (F0 F2 FM : ℝ → ℂ)
    (Q x y t D H : ℝ) (alpha beta : ℂ) :
    PRZZSignedSourceCell.source N d j l h (frequencyBound d D H) b k
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
      (PRZZMellinSeparation.scaledCutoff F0 Q) F2 FM alpha beta x t
      (fun a => nu (frequencies d D H) x y (a:ℤ))
      (fun a => nu (frequencies d D H) x y (-(a:ℤ))) =
    ∑ v ∈ (frequencies d D H).image freq, nu (frequencies d D H) x y v *
      PRZZFreeCell.cell N d j l h b k js F0 F2 FM Q x t alpha beta v := by
  rw [frequency_pair]
  simp only [PRZZSignedSourceCell.source,PRZZFreeCell.cell,Nat.floor_natCast]

theorem source_bound (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (F0 F2 FM : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM)
    (K : ℕ) (ks js : List ℕ) (eps eta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ N y d j l h : ℕ, ∀ b ∈ branches y K ks,
      ∀ k : Fin b.2.length → ℕ, ∀ i : Fin b.2.length,
      group N b k univ ≠ 0 → (y:ℝ) < (2:ℝ)^(k i) →
      ∀ U T Q x y0 t D H : ℝ, ∀ alpha beta : ℂ,
      (∏ a, (2:ℝ)^(k a)) = U →
      (∏ a ∈ univ.erase i, (2:ℝ)^(k a)) < U^(1/4:ℝ) →
      0 < N → 0 < d → 0 < h → (d:ℝ) ≤ T →
      1 < T → (N:ℝ)+1 ≤ T → |alpha.re| ≤ S/Real.log T →
      1+‖alpha‖ ≤ Z → |beta.re| ≤ S/Real.log T →
      ‖PRZZSignedSourceCell.source N d j l h (frequencyBound d D H) b k
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (PRZZMellinSeparation.scaledCutoff F0 Q) F2 FM alpha beta x t
        (fun a => nu (frequencies d D H) x y0 (a:ℤ))
        (fun a => nu (frequencies d D H) x y0 (-(a:ℤ)))‖ ≤
        C*(∏ a ∈ univ.erase i, (2:ℝ)^(k a+1))^eta*(1+|t|)*
          (T^eta*T^eta*T^eta)*
          (((⌈D/d⌉.natAbs*⌊H⌋₊:ℕ):ℝ)^eta*((⌈D/d⌉.natAbs*⌊H⌋₊:ℕ):ℝ))*
          (((2:ℝ)^(l+1))^(1/2+eps)*((2:ℝ)^l*U^(1/4:ℝ)+U)) := by
  obtain ⟨C,hC,hbound⟩ := PRZZTypeIScaleSupplier.signed_cell hWeil F0 F2 FM hf hc
    hF hcF hM hcM K ks js eps eta S Z heps heta hS hZ
  refine ⟨C,hC,?_⟩
  intro N y d j l h b hb k i hn hi U T Q x y0 t D H alpha beta hp hs hN hd hh hdT hT hNT ha hz hbeta
  rw [source_eq_signed]
  exact hbound N y d j l h b hb k i hn hi U T Q x y0 t D H alpha beta hp hs hN hd hh hdT hT hNT ha hz hbeta

#print axioms source_eq_signed
#print axioms source_bound
theorem retained_source_bound (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (F0 F2 FM : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM)
    (K : ℕ) (hK : 4 ≤ K) (ks js : List ℕ) (eps eta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ N d j l h : ℕ, ∀ b ∈ branches ⌊(PRZZRowWindow.hi N d h j:ℝ)^((K:ℝ)⁻¹)⌋₊ K ks,
      ∀ k : Fin b.2.length → ℕ, ∀ i : Fin b.2.length,
      ∀ U T Q x y0 t D H : ℝ, ∀ alpha beta : ℂ,
      (∏ a, (2:ℝ)^(k a)) = U →
      (∏ a ∈ univ.erase i, (2:ℝ)^(k a)) < U^(1/4:ℝ) →
      2*((2:ℝ)^((ks.length+1)*(2*K))) < U →
      U/U^(1/4:ℝ) < (2:ℝ)^(k i) →
      ∀ n : ℕ, PRZZRowWindow.lo h j ≤ n → n ≤ PRZZRowWindow.hi N d h j →
      group N b k univ n ≠ 0 →
      0 < N → 0 < d → 0 < h → (d:ℝ) ≤ T →
      1 < T → (N:ℝ)+1 ≤ T → |alpha.re| ≤ S/Real.log T →
      1+‖alpha‖ ≤ Z → |beta.re| ≤ S/Real.log T →
      ‖PRZZSignedSourceCell.source N d j l h (frequencyBound d D H) b k
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (PRZZMellinSeparation.scaledCutoff F0 Q) F2 FM alpha beta x t
        (fun a => nu (frequencies d D H) x y0 (a:ℤ))
        (fun a => nu (frequencies d D H) x y0 (-(a:ℤ)))‖ ≤
        C*(∏ a ∈ univ.erase i, (2:ℝ)^(k a+1))^eta*(1+|t|)*
          (T^eta*T^eta*T^eta)*
          ((frequencyBound d D H:ℝ)^eta)*((2:ℝ)^(l+1))^eps*
          (PRZZCombinedBudget.typeI ((2:ℝ)^j/2^((ks.length+1)*(2*K)))
            (frequencyBound d D H) ((2:ℝ)^l)/(h:ℝ)^(1/4:ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := source_bound hWeil F0 F2 FM hf hc hF hcF hM hcM
    K ks js eps eta S Z heps heta hS hZ
  let c : ℝ := 2^((ks.length+1)*(2*K))
  have hc0 : 0 < c := by dsimp [c]; positivity
  refine ⟨C*(2*c),by positivity,?_⟩
  intro N d j l h b hb k i U T Q x y0 t D H alpha beta hp hs hlarge hi n hl hu hnz hN hd hh hdT hT hNT ha hz hbeta
  have hn : group N b k univ ≠ 0 := by intro he; exact hnz (by rw [he]; rfl)
  have hy := PRZZTypeIScaleSupplier.retained_root_short N d h j K ks hh hK b hb k U hp hlarge n hl hu hnz
  have hbnd := hbound N _ d j l h b hb k i hn (hy.trans_lt hi) U T Q x y0 t D H alpha beta
    hp hs hN hd hh hdT hT hNT ha hz hbeta
  have htrans := PRZZActualBudgetLayout.retained_typeI_decay N d h j _ K ks hd hh b hb k U hp n hl hu hnz
    (frequencyBound d D H) ((2:ℝ)^l) (Nat.cast_nonneg _) (by positivity)
  let A : ℝ := frequencyBound d D H
  let L : ℝ := ∏ a ∈ univ.erase i, (2:ℝ)^(k a+1)
  let P : ℝ := C*L^eta*(1+|t|)*(T^eta*T^eta*T^eta)*A^eta*((2:ℝ)^(l+1))^eps
  have hP : 0 ≤ P := by dsimp [P,A,L]; positivity
  have he : C*L^eta*(1+|t|)*(T^eta*T^eta*T^eta)*(A^eta*A)*
      (((2:ℝ)^(l+1))^(1/2+eps)*((2:ℝ)^l*U^(1/4:ℝ)+U)) =
      P*PRZZCombinedBudget.typeI U A ((2:ℝ)^l) := by
    rw [Real.rpow_add (by positivity : (0:ℝ) < (2:ℝ)^(l+1))]
    have hpow : (2:ℝ)^(l+1) = 2*(2:ℝ)^l := by rw [pow_succ]; ring
    rw [hpow]
    dsimp [P,PRZZCombinedBudget.typeI]
    rw [hpow]
    ring
  change _ ≤ C*L^eta*(1+|t|)*(T^eta*T^eta*T^eta)*(A^eta*A)*
      (((2:ℝ)^(l+1))^(1/2+eps)*((2:ℝ)^l*U^(1/4:ℝ)+U)) at hbnd
  rw [he] at hbnd
  exact (hbnd.trans (mul_le_mul_of_nonneg_left htrans hP)).trans_eq (by dsimp [P,A,L,c]; ring)

#print axioms retained_source_bound

end XiPrime8845.PRZZActualTypeI
