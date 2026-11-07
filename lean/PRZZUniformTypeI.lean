import PRZZActualAggregate

/-! Scale-uniform Type I suppliers. Constants precede BOTH rescalings
of the second arithmetic profile and spatial profile. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset
namespace XiPrime8845.PRZZUniformTypeI
set_option maxHeartbeats 6000000

section
open PRZZFreeLengthCoefficient
open Finset
open PRZZFreeSource PRZZMellinSeparation PRZZKloostermanInputs PRZZFreeLength
theorem length_slice (hWeil : WeilIncomplete)
    (F0 F2 FM : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM)
    (js : List ℕ) (J : ℕ) (eps eta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q2 QM : ℝ, ∀ N d j l h e r m : ℕ, ∀ T Q x t : ℝ,
      ∀ alpha beta : ℂ, ∀ k : ℤ,
      0 < N → 0 < d → 0 < h → 0 < e → m ≤ J →
      1 < T → (N:ℝ)+1 ≤ T → |alpha.re| ≤ S/Real.log T →
      1+‖alpha‖ ≤ Z → |beta.re| ≤ S/Real.log T →
      ‖PRZZFreeCoefficient.slice N d j l h e r m js F0 (PRZZMellinSeparation.scaledCutoff F2 Q2) (PRZZMellinSeparation.scaledCutoff FM QM) Q x t alpha beta k‖ ≤
        C*(1+|t|)*(T^eta*T^eta)*budget eps N d l (endpoint N d h e r) k := by
  obtain ⟨Cw,hCw,hw⟩ := PRZZFreeLength.transformed_bound hWeil F0 hf hc J eps eta S Z
    heps heta hS hZ
  obtain ⟨Cr,hCr,hr⟩ := PRZZSourceCoefficients.second_coefficient_scaled js eta S heta hS
    F2 FM hF hcF hM hcM
  refine ⟨Cr*Cw,mul_pos hCr hCw,?_⟩
  intro Q2 QM N d j l h e r m T Q x t alpha beta k hN hd hh he hm hT hNT ha hz hb
  let F2 := PRZZMellinSeparation.scaledCutoff F2 Q2
  let FM := PRZZMellinSeparation.scaledCutoff FM QM
  rw [PRZZFreeCoefficient.slice,PRZZFreeSource.slice_eq]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ q ∈ PRZZDyadic.cell N l,
        (Cr*T^eta)*(Cw*Real.rpow q (1/2+eps)*(d.divisors.card:ℝ)*
          (k.natAbs.gcd q:ℝ)*(1+(endpoint N d h e r:ℝ)/q)*(1+|t|)*T^eta) := by
      apply sum_le_sum
      intro q hq
      by_cases hg : d.Coprime e ∧ (h*e).Coprime q ∧ d*q ≤ N
      · rw [if_pos hg,norm_mul]
        have hrq := hr Q2 QM N d l hN hd T x t hT (by linarith) beta hb q
        rw [PRZZAStarRectangles.secondCoeff,if_pos (And.intro hq hg.2.2)] at hrq
        exact mul_le_mul hrq
          (hw N d j h e r m q T Q t alpha k hd hh he hm
            (mem_Icc.mp (mem_filter.mp hq).1).1 hg.2.1 hT hNT ha hz)
          (norm_nonneg _) (by positivity)
      · rw [if_neg hg,norm_zero]
        have hp := Real.rpow_nonneg (Nat.cast_nonneg q) (1/2+eps)
        positivity
    _ = _ := by
      unfold budget
      rw [mul_sum]
      apply sum_congr rfl
      intro q hq
      ring

end

#print axioms length_slice

section
open PRZZFreeLengthCoefficient
open Finset
open PRZZFreeSource PRZZMellinSeparation PRZZKloostermanInputs PRZZFreeLength
theorem length_nu (hWeil : WeilIncomplete)
    (F0 F2 FM : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM)
    (js : List ℕ) (J : ℕ) (eps eta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q2 QM : ℝ, ∀ N d j l h e r m : ℕ, ∀ T Q x y t D H : ℝ,
      ∀ alpha beta : ℂ, ∀ k : ℤ,
      0 < N → 0 < d → 0 < h → 0 < e → m ≤ J →
      1 < T → (N:ℝ)+1 ≤ T → |alpha.re| ≤ S/Real.log T →
      1+‖alpha‖ ≤ Z → |beta.re| ≤ S/Real.log T → k ≠ 0 →
      ‖PRZZNuCoefficient.nu (PRZZAStarNu.frequencies d D H) x y k *
        PRZZFreeCoefficient.slice N d j l h e r m js F0 (PRZZMellinSeparation.scaledCutoff F2 Q2) (PRZZMellinSeparation.scaledCutoff FM QM) Q x t alpha beta k‖ ≤
        C*(k.natAbs:ℝ)^eta*(1+|t|)*(T^eta*T^eta)*budget eps N d l (endpoint N d h e r) k := by
  obtain ⟨C,hC,hbound⟩ := length_slice hWeil F0 F2 FM hf hc hF hcF hM hcM js J eps eta S Z
    heps heta hS hZ
  obtain ⟨D,hD,hn⟩ := PRZZNuBounds.nu_subpower eta heta
  refine ⟨D*C,mul_pos hD hC,?_⟩
  intro Q2 QM N d j l h e r m T Q x y t D0 H alpha beta k hN hd hh he hm hT hNT ha hz hb hk
  let F2 := PRZZMellinSeparation.scaledCutoff F2 Q2
  let FM := PRZZMellinSeparation.scaledCutoff FM QM
  rw [norm_mul]
  exact (mul_le_mul
    (hn _ (PRZZAStarNu.frequency_positive_h d D0 H) x y k hk)
    (hbound Q2 QM N d j l h e r m T Q x t alpha beta k hN hd hh he hm hT hNT ha hz hb)
    (norm_nonneg _) (by positivity)).trans_eq (by ring)

end

#print axioms length_nu

section
open PRZZFreeLengthCoefficient
open Finset
open PRZZFreeSource PRZZMellinSeparation PRZZKloostermanInputs PRZZFreeLength
theorem length_signed (hWeil : WeilIncomplete)
    (F0 F2 FM : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM)
    (js : List ℕ) (J : ℕ) (eps eta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q2 QM : ℝ, ∀ N d j l h e r m : ℕ, ∀ T Q x y t D H : ℝ,
      ∀ alpha beta : ℂ,
      0 < N → 0 < d → 0 < h → 0 < e → m ≤ J →
      1 < T → (N:ℝ)+1 ≤ T → |alpha.re| ≤ S/Real.log T →
      1+‖alpha‖ ≤ Z → |beta.re| ≤ S/Real.log T →
      ‖∑ k ∈ (PRZZAStarNu.frequencies d D H).image PRZZNuCoefficient.freq,
        PRZZNuCoefficient.nu (PRZZAStarNu.frequencies d D H) x y k *
          PRZZFreeCoefficient.slice N d j l h e r m js F0 (PRZZMellinSeparation.scaledCutoff F2 Q2) (PRZZMellinSeparation.scaledCutoff FM QM) Q x t alpha beta k‖ ≤
        C*(1+|t|)*(T^eta*T^eta)*
          ∑ k ∈ (PRZZAStarNu.frequencies d D H).image PRZZNuCoefficient.freq,
            (k.natAbs:ℝ)^eta*budget eps N d l (endpoint N d h e r) k := by
  obtain ⟨C,hC,hbound⟩ := length_nu hWeil F0 F2 FM hf hc hF hcF hM hcM
    js J eps eta S Z heps heta hS hZ
  refine ⟨C,hC,?_⟩
  intro Q2 QM N d j l h e r m T Q x y t D H alpha beta hN hd hh he hm hT hNT ha hz hb
  let F2 := PRZZMellinSeparation.scaledCutoff F2 Q2
  let FM := PRZZMellinSeparation.scaledCutoff FM QM
  apply (norm_sum_le _ _).trans
  rw [mul_sum]
  apply sum_le_sum
  intro k hk
  exact (hbound Q2 QM N d j l h e r m T Q x y t D H alpha beta k hN hd hh he hm
    hT hNT ha hz hb (PRZZAStarNu.frequency_ne_zero d D H k hk)).trans_eq (by ring)

end

#print axioms length_signed

section
open PRZZFreeLengthCell
open Finset
open PRZZActualBranchCells PRZZHBBranches PRZZFreeCoefficient
open PRZZFreeLength PRZZFreeLengthCoefficient
theorem free_cell (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (F0 F2 FM : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM)
    (K : ℕ) (ks js : List ℕ) (eps eta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q2 QM : ℝ, ∀ N y d j l h : ℕ, ∀ b ∈ branches y K ks,
      ∀ k : Fin b.2.length → ℕ, ∀ i : Fin b.2.length,
      group N b k univ ≠ 0 → (y:ℝ) < (2:ℝ)^(k i) →
      ∀ T Q x y0 t D H L : ℝ, ∀ alpha beta : ℂ,
      0 < N → 0 < d → 0 < h → 1 ≤ L →
      (∏ a ∈ univ.erase i, (2:ℝ)^(k a+1)) ≤ L →
      1 < T → (N:ℝ)+1 ≤ T → |alpha.re| ≤ S/Real.log T →
      1+‖alpha‖ ≤ Z → |beta.re| ≤ S/Real.log T →
      ‖∑ v ∈ (PRZZAStarNu.frequencies d D H).image PRZZNuCoefficient.freq,
        PRZZNuCoefficient.nu (PRZZAStarNu.frequencies d D H) x y0 v *
          PRZZFreeCell.cell N d j l h b k js F0 (PRZZMellinSeparation.scaledCutoff F2 Q2) (PRZZMellinSeparation.scaledCutoff FM QM) Q x t alpha beta v‖ ≤
        C*L^eta*L*(1+|t|)*(T^eta*T^eta)*
          ∑ v ∈ (PRZZAStarNu.frequencies d D H).image PRZZNuCoefficient.freq,
            (v.natAbs:ℝ)^eta*budget eps N d l (endpoint N d h 1 (k i)) v := by
  obtain ⟨Cs,hCs,hs⟩ := length_signed hWeil F0 F2 FM hf hc hF hcF hM hcM
    js (ks.sum+1) eps eta S Z heps heta hS hZ
  obtain ⟨Cg,hCg,hg⟩ := PRZZCellMass.weighted_mass K ks eta heta
  refine ⟨Cg*Cs,mul_pos hCg hCs,?_⟩
  intro Q2 QM N y d j l h b hb k i hn hi T Q x y0 t D H L alpha beta hN hd hh hL hsup
    hT hNT ha hz hbeta
  let F2 := PRZZMellinSeparation.scaledCutoff F2 Q2
  let FM := PRZZMellinSeparation.scaledCutoff FM QM
  obtain ⟨m,hm,hp⟩ := PRZZBareFactors.large_piece N y K ks b hb k i hn hi
  change ‖∑ v ∈ (PRZZAStarNu.frequencies d D H).image PRZZNuCoefficient.freq,
    PRZZNuCoefficient.nu (PRZZAStarNu.frequencies d D H) x y0 v *
      PRZZFreeCell.cell N d j l h b k js F0 F2 FM Q x t alpha beta v‖ ≤ _
  simp_rw [PRZZFreeCell.cell,PRZZFreeCell.cell_eq N d j l h hd hh b k i m hp js F0 F2 FM Q x t alpha beta]
  simp only [mul_sum]
  rw [sum_comm]
  have heq : (∑ e ∈ Icc 1 N,
      ∑ v ∈ (PRZZAStarNu.frequencies d D H).image PRZZNuCoefficient.freq,
        PRZZNuCoefficient.nu (PRZZAStarNu.frequencies d D H) x y0 v *
          ((group N b k (univ.erase i) e:ℂ) *
            slice N d j l h e (k i) m js F0 F2 FM Q x t alpha beta v)) =
      ∑ e ∈ Icc 1 N, (group N b k (univ.erase i) e:ℂ) *
        ∑ v ∈ (PRZZAStarNu.frequencies d D H).image PRZZNuCoefficient.freq,
          PRZZNuCoefficient.nu (PRZZAStarNu.frequencies d D H) x y0 v *
            slice N d j l h e (k i) m js F0 F2 FM Q x t alpha beta v := by
    simp only [mul_sum]; apply sum_congr rfl; intro e he
    apply sum_congr rfl; intro v hv; ring
  rw [heq]
  have hbudget : 0 ≤ ∑ v ∈ (PRZZAStarNu.frequencies d D H).image PRZZNuCoefficient.freq,
      (v.natAbs:ℝ)^eta*budget eps N d l (endpoint N d h 1 (k i)) v :=
    sum_nonneg (fun v _ => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (budget_nonneg eps N d l (endpoint N d h 1 (k i)) v))
  apply (hg N y b hb k (univ.erase i) L
    (Cs*(1+|t|)*(T^eta*T^eta)*
      ∑ v ∈ (PRZZAStarNu.frequencies d D H).image PRZZNuCoefficient.freq,
        (v.natAbs:ℝ)^eta*budget eps N d l (endpoint N d h 1 (k i)) v)
    hL (by positivity) hsup _ ?_).trans_eq
  · simp only [mul_sum]
    apply sum_congr rfl
    intro v hv
    ring
  · intro e he
    apply (hs Q2 QM N d j l h e (k i) m T Q x y0 t D H alpha beta hN hd hh
      (mem_Icc.mp he).1 hm hT hNT ha hz hbeta).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply sum_le_sum
    intro v hv
    exact mul_le_mul_of_nonneg_left
      (budget_mono eps N d l _ _ v (endpoint_le N d h e (k i) hd hh (mem_Icc.mp he).1))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)


end

#print axioms free_cell

section
open PRZZLengthBudget
open Finset
open PRZZFreeLengthCoefficient
open PRZZModulusBudget (weighted_gcd)
open PRZZActualBranchCells PRZZHBBranches PRZZFreeLength
theorem length_average (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (F0 F2 FM : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM)
    (K : ℕ) (ks js : List ℕ) (eps eta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q2 QM : ℝ, ∀ N y d j l h : ℕ, ∀ b ∈ branches y K ks,
      ∀ k : Fin b.2.length → ℕ, ∀ i : Fin b.2.length,
      group N b k univ ≠ 0 → (y:ℝ) < (2:ℝ)^(k i) →
      ∀ T Q x y0 t D H L : ℝ, ∀ alpha beta : ℂ,
      0 < N → 0 < d → 0 < h → 1 ≤ L →
      (∏ a ∈ univ.erase i, (2:ℝ)^(k a+1)) ≤ L →
      1 < T → (N:ℝ)+1 ≤ T → |alpha.re| ≤ S/Real.log T →
      1+‖alpha‖ ≤ Z → |beta.re| ≤ S/Real.log T →
      ‖∑ v ∈ (PRZZAStarNu.frequencies d D H).image PRZZNuCoefficient.freq,
        PRZZNuCoefficient.nu (PRZZAStarNu.frequencies d D H) x y0 v *
          PRZZFreeCell.cell N d j l h b k js F0 (PRZZMellinSeparation.scaledCutoff F2 Q2) (PRZZMellinSeparation.scaledCutoff FM QM) Q x t alpha beta v‖ ≤
        C*L^eta*L*(1+|t|)*(T^eta*T^eta)*
          (2*((⌈D/d⌉.natAbs*⌊H⌋₊:ℕ):ℝ)^eta*((⌈D/d⌉.natAbs*⌊H⌋₊:ℕ):ℝ)*
            averaged eps N d l (endpoint N d h 1 (k i))) := by
  obtain ⟨C,hC,hbound⟩ := free_cell hWeil F0 F2 FM
    hf hc hF hcF hM hcM K ks js eps eta S Z heps heta hS hZ
  refine ⟨C,hC,?_⟩
  intro Q2 QM N y d j l h b hb k i hn hi T Q x y0 t D H L alpha beta hN hd hh hL hsup hT hNT ha hz hbeta
  let F2 := PRZZMellinSeparation.scaledCutoff F2 Q2
  let FM := PRZZMellinSeparation.scaledCutoff FM QM
  apply (hbound Q2 QM N y d j l h b hb k i hn hi T Q x y0 t D H L alpha beta
    hN hd hh hL hsup hT hNT ha hz hbeta).trans
  exact mul_le_mul_of_nonneg_left (source_budget eps eta heta.le N d l _ D H)
    (by positivity)

end

#print axioms length_average

section
open PRZZTypeIScaleSupplier
open Finset
open PRZZActualBranchCells PRZZHBBranches
theorem typeI_cell (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (F0 F2 FM : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM)
    (K : ℕ) (ks js : List ℕ) (eps eta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q2 QM : ℝ, ∀ N y d j l h : ℕ, ∀ b ∈ branches y K ks,
      ∀ k : Fin b.2.length → ℕ, ∀ i : Fin b.2.length,
      group N b k univ ≠ 0 → (y:ℝ) < (2:ℝ)^(k i) →
      ∀ U T Q x y0 t D H : ℝ, ∀ alpha beta : ℂ,
      (∏ a, (2:ℝ)^(k a)) = U →
      (∏ a ∈ univ.erase i, (2:ℝ)^(k a)) < U^(1/4:ℝ) →
      0 < N → 0 < d → 0 < h → (d:ℝ) ≤ T →
      1 < T → (N:ℝ)+1 ≤ T → |alpha.re| ≤ S/Real.log T →
      1+‖alpha‖ ≤ Z → |beta.re| ≤ S/Real.log T →
      ‖∑ v ∈ (PRZZAStarNu.frequencies d D H).image PRZZNuCoefficient.freq,
        PRZZNuCoefficient.nu (PRZZAStarNu.frequencies d D H) x y0 v *
          PRZZFreeCell.cell N d j l h b k js F0 (PRZZMellinSeparation.scaledCutoff F2 Q2) (PRZZMellinSeparation.scaledCutoff FM QM) Q x t alpha beta v‖ ≤
        C*(∏ a ∈ univ.erase i, (2:ℝ)^(k a+1))^eta*(1+|t|)*
          (T^eta*T^eta*T^eta)*
          (((⌈D/d⌉.natAbs*⌊H⌋₊:ℕ):ℝ)^eta*((⌈D/d⌉.natAbs*⌊H⌋₊:ℕ):ℝ))*
          (((2:ℝ)^(l+1))^(1/2+eps)*((2:ℝ)^l*U^(1/4:ℝ)+U)) := by
  obtain ⟨C0,hC0,hcell⟩ := length_average hWeil F0 F2 FM
    hf hc hF hcF hM hcM K ks js eps eta S Z heps heta hS hZ
  obtain ⟨C1,hC1,hscale⟩ := PRZZModulusScale.actual_averaged_typeI eta heta
  let c : ℝ := 2^((ks.length+1)*(2*K))
  have hcpos : 0 < c := by dsimp [c]; positivity
  refine ⟨2*C0*C1*c,by positivity,?_⟩
  intro Q2 QM N y d j l h b hb k i hn hi U T Q x y0 t D H alpha beta hp hs hN hd hh hdT hT hNT ha hz hbeta
  let F2 := PRZZMellinSeparation.scaledCutoff F2 Q2
  let FM := PRZZMellinSeparation.scaledCutoff FM QM
  let L : ℝ := ∏ a ∈ univ.erase i, (2:ℝ)^(k a+1)
  have hL : 1 ≤ L := Finset.one_le_prod (fun a _ => one_le_pow₀ (by norm_num))
  have hbnd := hcell Q2 QM N y d j l h b hb k i hn hi T Q x y0 t D H L alpha beta
    hN hd hh hL le_rfl hT hNT ha hz hbeta
  have hsc := hscale N d h y K l ks b hb k i U T eps hp hs hd hdT (by linarith) heps.le
  let A : ℝ := ((⌈D/d⌉.natAbs*⌊H⌋₊:ℕ):ℝ)
  have hA : 0 ≤ A := Nat.cast_nonneg _
  have hT0 : 0 < T := by linarith
  have hfactor : 0 ≤ C0*L^eta*(1+|t|)*(T^eta*T^eta)*(2*A^eta*A) := by positivity
  apply hbnd.trans
  calc
    _ = (C0*L^eta*(1+|t|)*(T^eta*T^eta)*(2*A^eta*A))*
        (L*PRZZLengthBudget.averaged eps N d l (PRZZFreeLength.endpoint N d h 1 (k i))) := by
      dsimp [A]; ring
    _ ≤ (C0*L^eta*(1+|t|)*(T^eta*T^eta)*(2*A^eta*A))*
        (C1*T^eta*c*(((2:ℝ)^(l+1))^(1/2+eps)*((2:ℝ)^l*U^(1/4:ℝ)+U))) :=
      mul_le_mul_of_nonneg_left hsc hfactor
    _ = _ := by dsimp [A,L,c]; ring

end

#print axioms typeI_cell

section
open PRZZActualTypeI
open Finset
open PRZZActualBranchCells PRZZHBBranches PRZZActualSignedBranches
open PRZZAStarNu PRZZNuCoefficient
theorem typeI_source (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (F0 F2 FM : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM)
    (K : ℕ) (ks js : List ℕ) (eps eta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q2 QM : ℝ, ∀ N y d j l h : ℕ, ∀ b ∈ branches y K ks,
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
        (PRZZMellinSeparation.scaledCutoff F0 Q) (PRZZMellinSeparation.scaledCutoff F2 Q2) (PRZZMellinSeparation.scaledCutoff FM QM) alpha beta x t
        (fun a => nu (frequencies d D H) x y0 (a:ℤ))
        (fun a => nu (frequencies d D H) x y0 (-(a:ℤ)))‖ ≤
        C*(∏ a ∈ univ.erase i, (2:ℝ)^(k a+1))^eta*(1+|t|)*
          (T^eta*T^eta*T^eta)*
          (((⌈D/d⌉.natAbs*⌊H⌋₊:ℕ):ℝ)^eta*((⌈D/d⌉.natAbs*⌊H⌋₊:ℕ):ℝ))*
          (((2:ℝ)^(l+1))^(1/2+eps)*((2:ℝ)^l*U^(1/4:ℝ)+U)) := by
  obtain ⟨C,hC,hbound⟩ := typeI_cell hWeil F0 F2 FM hf hc
    hF hcF hM hcM K ks js eps eta S Z heps heta hS hZ
  refine ⟨C,hC,?_⟩
  intro Q2 QM N y d j l h b hb k i hn hi U T Q x y0 t D H alpha beta hp hs hN hd hh hdT hT hNT ha hz hbeta
  let F2 := PRZZMellinSeparation.scaledCutoff F2 Q2
  let FM := PRZZMellinSeparation.scaledCutoff FM QM
  rw [source_eq_signed]
  exact hbound Q2 QM N y d j l h b hb k i hn hi U T Q x y0 t D H alpha beta hp hs hN hd hh hdT hT hNT ha hz hbeta

end

#print axioms typeI_source

section
open PRZZActualTypeI
open Finset
open PRZZActualBranchCells PRZZHBBranches PRZZActualSignedBranches
open PRZZAStarNu PRZZNuCoefficient
theorem typeI_retained (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (F0 F2 FM : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM)
    (K : ℕ) (hK : 4 ≤ K) (ks js : List ℕ) (eps eta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q2 QM : ℝ, ∀ N d j l h : ℕ, ∀ b ∈ branches ⌊(PRZZRowWindow.hi N d h j:ℝ)^((K:ℝ)⁻¹)⌋₊ K ks,
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
        (PRZZMellinSeparation.scaledCutoff F0 Q) (PRZZMellinSeparation.scaledCutoff F2 Q2) (PRZZMellinSeparation.scaledCutoff FM QM) alpha beta x t
        (fun a => nu (frequencies d D H) x y0 (a:ℤ))
        (fun a => nu (frequencies d D H) x y0 (-(a:ℤ)))‖ ≤
        C*(∏ a ∈ univ.erase i, (2:ℝ)^(k a+1))^eta*(1+|t|)*
          (T^eta*T^eta*T^eta)*
          ((frequencyBound d D H:ℝ)^eta)*((2:ℝ)^(l+1))^eps*
          (PRZZCombinedBudget.typeI ((2:ℝ)^j/2^((ks.length+1)*(2*K)))
            (frequencyBound d D H) ((2:ℝ)^l)/(h:ℝ)^(1/4:ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := typeI_source hWeil F0 F2 FM hf hc hF hcF hM hcM
    K ks js eps eta S Z heps heta hS hZ
  let c : ℝ := 2^((ks.length+1)*(2*K))
  have hc0 : 0 < c := by dsimp [c]; positivity
  refine ⟨C*(2*c),by positivity,?_⟩
  intro Q2 QM N d j l h b hb k i U T Q x y0 t D H alpha beta hp hs hlarge hi n hl hu hnz hN hd hh hdT hT hNT ha hz hbeta
  let F2 := PRZZMellinSeparation.scaledCutoff F2 Q2
  let FM := PRZZMellinSeparation.scaledCutoff FM QM
  have hn : group N b k univ ≠ 0 := by intro he; exact hnz (by rw [he]; rfl)
  have hy := PRZZTypeIScaleSupplier.retained_root_short N d h j K ks hh hK b hb k U hp hlarge n hl hu hnz
  have hbnd := hbound Q2 QM N _ d j l h b hb k i hn (hy.trans_lt hi) U T Q x y0 t D H alpha beta
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

end

#print axioms typeI_retained

end XiPrime8845.PRZZUniformTypeI
