/- Spatial cutoff support is unrestricted here: only its common norm cap is used. -/
import PRZZClassFreeLength

/-! Literal free-factor Type I estimates uniform over a quantitative cutoff
class. The effective free endpoint, right coefficient, signed frequencies,
complementary HB mass and modulus averaging retain their original masks.
Weil is an explicit hypothesis. Constants precede all cutoff choices. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset
namespace XiPrime8845.PRZZClassSpatialTypeI
open PRZZFreeSource PRZZMellinSeparation PRZZKloostermanInputs PRZZFreeLength
open PRZZFreeLengthCoefficient PRZZActualBranchCells PRZZHBBranches PRZZFreeCoefficient
open PRZZLengthBudget PRZZActualSignedBranches PRZZAStarNu PRZZNuCoefficient
open PRZZActualTypeI
set_option maxHeartbeats 10000000

theorem slice_bound (hWeil : WeilIncomplete)
    (width : ℝ) (jets : ℕ → ℝ) (hjets : ∀ n, 0 ≤ jets n)
    (js : List ℕ) (J : ℕ) (eps eta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ F0 F2 FM : ℝ → ℂ,
      PRZZProfileMellin.Member width jets F0 → PRZZProfileMellin.Member width jets F2 →
      (∀ x, ‖FM x‖ ≤ jets 0) → ∀ N d j l h e r m : ℕ, ∀ T Q x t : ℝ,
      ∀ alpha beta : ℂ, ∀ k : ℤ,
      0 < N → 0 < d → 0 < h → 0 < e → m ≤ J →
      1 < T → (N:ℝ)+1 ≤ T → |alpha.re| ≤ S/Real.log T →
      1+‖alpha‖ ≤ Z → |beta.re| ≤ S/Real.log T →
      ‖PRZZFreeCoefficient.slice N d j l h e r m js F0 F2 FM Q x t alpha beta k‖ ≤
        C*(1+|t|)*(T^eta*T^eta)*budget eps N d l (endpoint N d h e r) k := by
  obtain ⟨Cw,hCw,hw⟩ := PRZZClassFreeLength.transformed_bound hWeil width jets hjets J eps eta S Z
    heps heta hS hZ
  obtain ⟨Cr,hCr,hr⟩ := PRZZClassSources.second_coefficient js eta S heta hS
    (jets 0) (jets 0) (hjets 0) (hjets 0)
  refine ⟨Cr*Cw,mul_pos hCr hCw,?_⟩
  intro F0 F2 FM hf0 hf2 hfM N d j l h e r m T Q x t alpha beta k hN hd hh he hm hT hNT ha hz hb
  have hr := hr F2 FM (PRZZClassSources.member_sup width jets F2 hf2)
    hfM
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
        have hrq := hr N d l hN hd T x t hT (by linarith) beta hb q
        rw [PRZZAStarRectangles.secondCoeff,if_pos (And.intro hq hg.2.2)] at hrq
        exact mul_le_mul hrq
          (hw F0 hf0 N d j h e r m q T Q t alpha k hd hh he hm
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

theorem nu_slice_bound (hWeil : WeilIncomplete)
    (width : ℝ) (jets : ℕ → ℝ) (hjets : ∀ n, 0 ≤ jets n)
    (js : List ℕ) (J : ℕ) (eps eta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ F0 F2 FM : ℝ → ℂ,
      PRZZProfileMellin.Member width jets F0 → PRZZProfileMellin.Member width jets F2 →
      (∀ x, ‖FM x‖ ≤ jets 0) → ∀ N d j l h e r m : ℕ, ∀ T Q x y t D H : ℝ,
      ∀ alpha beta : ℂ, ∀ k : ℤ,
      0 < N → 0 < d → 0 < h → 0 < e → m ≤ J →
      1 < T → (N:ℝ)+1 ≤ T → |alpha.re| ≤ S/Real.log T →
      1+‖alpha‖ ≤ Z → |beta.re| ≤ S/Real.log T → k ≠ 0 →
      ‖PRZZNuCoefficient.nu (PRZZAStarNu.frequencies d D H) x y k *
        PRZZFreeCoefficient.slice N d j l h e r m js F0 F2 FM Q x t alpha beta k‖ ≤
        C*(k.natAbs:ℝ)^eta*(1+|t|)*(T^eta*T^eta)*budget eps N d l (endpoint N d h e r) k := by
  obtain ⟨C,hC,hbound⟩ := slice_bound hWeil width jets hjets js J eps eta S Z
    heps heta hS hZ
  obtain ⟨D,hD,hn⟩ := PRZZNuBounds.nu_subpower eta heta
  refine ⟨D*C,mul_pos hD hC,?_⟩
  intro F0 F2 FM hf0 hf2 hfM N d j l h e r m T Q x y t D0 H alpha beta k hN hd hh he hm hT hNT ha hz hb hk
  rw [norm_mul]
  exact (mul_le_mul
    (hn _ (PRZZAStarNu.frequency_positive_h d D0 H) x y k hk)
    (hbound F0 F2 FM hf0 hf2 hfM N d j l h e r m T Q x t alpha beta k hN hd hh he hm hT hNT ha hz hb)
    (norm_nonneg _) (by positivity)).trans_eq (by ring)

theorem signed_slice_bound (hWeil : WeilIncomplete)
    (width : ℝ) (jets : ℕ → ℝ) (hjets : ∀ n, 0 ≤ jets n)
    (js : List ℕ) (J : ℕ) (eps eta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ F0 F2 FM : ℝ → ℂ,
      PRZZProfileMellin.Member width jets F0 → PRZZProfileMellin.Member width jets F2 →
      (∀ x, ‖FM x‖ ≤ jets 0) → ∀ N d j l h e r m : ℕ, ∀ T Q x y t D H : ℝ,
      ∀ alpha beta : ℂ,
      0 < N → 0 < d → 0 < h → 0 < e → m ≤ J →
      1 < T → (N:ℝ)+1 ≤ T → |alpha.re| ≤ S/Real.log T →
      1+‖alpha‖ ≤ Z → |beta.re| ≤ S/Real.log T →
      ‖∑ k ∈ (PRZZAStarNu.frequencies d D H).image PRZZNuCoefficient.freq,
        PRZZNuCoefficient.nu (PRZZAStarNu.frequencies d D H) x y k *
          PRZZFreeCoefficient.slice N d j l h e r m js F0 F2 FM Q x t alpha beta k‖ ≤
        C*(1+|t|)*(T^eta*T^eta)*
          ∑ k ∈ (PRZZAStarNu.frequencies d D H).image PRZZNuCoefficient.freq,
            (k.natAbs:ℝ)^eta*budget eps N d l (endpoint N d h e r) k := by
  obtain ⟨C,hC,hbound⟩ := nu_slice_bound hWeil width jets hjets
    js J eps eta S Z heps heta hS hZ
  refine ⟨C,hC,?_⟩
  intro F0 F2 FM hf0 hf2 hfM N d j l h e r m T Q x y t D H alpha beta hN hd hh he hm hT hNT ha hz hb
  apply (norm_sum_le _ _).trans
  rw [mul_sum]
  apply sum_le_sum
  intro k hk
  exact (hbound F0 F2 FM hf0 hf2 hfM N d j l h e r m T Q x y t D H alpha beta k hN hd hh he hm
    hT hNT ha hz hb (PRZZAStarNu.frequency_ne_zero d D H k hk)).trans_eq (by ring)

theorem cell_bound (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (width : ℝ) (jets : ℕ → ℝ) (hjets : ∀ n, 0 ≤ jets n)
    (K : ℕ) (ks js : List ℕ) (eps eta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ F0 F2 FM : ℝ → ℂ,
      PRZZProfileMellin.Member width jets F0 → PRZZProfileMellin.Member width jets F2 →
      (∀ x, ‖FM x‖ ≤ jets 0) → ∀ N y d j l h : ℕ, ∀ b ∈ branches y K ks,
      ∀ k : Fin b.2.length → ℕ, ∀ i : Fin b.2.length,
      group N b k univ ≠ 0 → (y:ℝ) < (2:ℝ)^(k i) →
      ∀ T Q x y0 t D H L : ℝ, ∀ alpha beta : ℂ,
      0 < N → 0 < d → 0 < h → 1 ≤ L →
      (∏ a ∈ univ.erase i, (2:ℝ)^(k a+1)) ≤ L →
      1 < T → (N:ℝ)+1 ≤ T → |alpha.re| ≤ S/Real.log T →
      1+‖alpha‖ ≤ Z → |beta.re| ≤ S/Real.log T →
      ‖∑ v ∈ (PRZZAStarNu.frequencies d D H).image PRZZNuCoefficient.freq,
        PRZZNuCoefficient.nu (PRZZAStarNu.frequencies d D H) x y0 v *
          PRZZFreeCell.cell N d j l h b k js F0 F2 FM Q x t alpha beta v‖ ≤
        C*L^eta*L*(1+|t|)*(T^eta*T^eta)*
          ∑ v ∈ (PRZZAStarNu.frequencies d D H).image PRZZNuCoefficient.freq,
            (v.natAbs:ℝ)^eta*budget eps N d l (endpoint N d h 1 (k i)) v := by
  obtain ⟨Cs,hCs,hs⟩ := signed_slice_bound hWeil width jets hjets
    js (ks.sum+1) eps eta S Z heps heta hS hZ
  obtain ⟨Cg,hCg,hg⟩ := PRZZCellMass.weighted_mass K ks eta heta
  refine ⟨Cg*Cs,mul_pos hCg hCs,?_⟩
  intro F0 F2 FM hf0 hf2 hfM N y d j l h b hb k i hn hi T Q x y0 t D H L alpha beta hN hd hh hL hsup
    hT hNT ha hz hbeta
  obtain ⟨m,hm,hp⟩ := PRZZBareFactors.large_piece N y K ks b hb k i hn hi
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
    apply (hs F0 F2 FM hf0 hf2 hfM N d j l h e (k i) m T Q x y0 t D H alpha beta hN hd hh
      (mem_Icc.mp he).1 hm hT hNT ha hz hbeta).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply sum_le_sum
    intro v hv
    exact mul_le_mul_of_nonneg_left
      (budget_mono eps N d l _ _ v (endpoint_le N d h e (k i) hd hh (mem_Icc.mp he).1))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem cell_averaged (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (width : ℝ) (jets : ℕ → ℝ) (hjets : ∀ n, 0 ≤ jets n)
    (K : ℕ) (ks js : List ℕ) (eps eta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ F0 F2 FM : ℝ → ℂ,
      PRZZProfileMellin.Member width jets F0 → PRZZProfileMellin.Member width jets F2 →
      (∀ x, ‖FM x‖ ≤ jets 0) → ∀ N y d j l h : ℕ, ∀ b ∈ branches y K ks,
      ∀ k : Fin b.2.length → ℕ, ∀ i : Fin b.2.length,
      group N b k univ ≠ 0 → (y:ℝ) < (2:ℝ)^(k i) →
      ∀ T Q x y0 t D H L : ℝ, ∀ alpha beta : ℂ,
      0 < N → 0 < d → 0 < h → 1 ≤ L →
      (∏ a ∈ univ.erase i, (2:ℝ)^(k a+1)) ≤ L →
      1 < T → (N:ℝ)+1 ≤ T → |alpha.re| ≤ S/Real.log T →
      1+‖alpha‖ ≤ Z → |beta.re| ≤ S/Real.log T →
      ‖∑ v ∈ (PRZZAStarNu.frequencies d D H).image PRZZNuCoefficient.freq,
        PRZZNuCoefficient.nu (PRZZAStarNu.frequencies d D H) x y0 v *
          PRZZFreeCell.cell N d j l h b k js F0 F2 FM Q x t alpha beta v‖ ≤
        C*L^eta*L*(1+|t|)*(T^eta*T^eta)*
          (2*((⌈D/d⌉.natAbs*⌊H⌋₊:ℕ):ℝ)^eta*((⌈D/d⌉.natAbs*⌊H⌋₊:ℕ):ℝ)*
            averaged eps N d l (endpoint N d h 1 (k i))) := by
  obtain ⟨C,hC,hbound⟩ := cell_bound hWeil width jets hjets K ks js eps eta S Z heps heta hS hZ
  refine ⟨C,hC,?_⟩
  intro F0 F2 FM hf0 hf2 hfM N y d j l h b hb k i hn hi T Q x y0 t D H L alpha beta hN hd hh hL hsup hT hNT ha hz hbeta
  apply (hbound F0 F2 FM hf0 hf2 hfM N y d j l h b hb k i hn hi T Q x y0 t D H L alpha beta
    hN hd hh hL hsup hT hNT ha hz hbeta).trans
  exact mul_le_mul_of_nonneg_left (source_budget eps eta heta.le N d l _ D H)
    (by positivity)

theorem signed_cell (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (width : ℝ) (jets : ℕ → ℝ) (hjets : ∀ n, 0 ≤ jets n)
    (K : ℕ) (ks js : List ℕ) (eps eta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ F0 F2 FM : ℝ → ℂ,
      PRZZProfileMellin.Member width jets F0 → PRZZProfileMellin.Member width jets F2 →
      (∀ x, ‖FM x‖ ≤ jets 0) → ∀ N y d j l h : ℕ, ∀ b ∈ branches y K ks,
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
          PRZZFreeCell.cell N d j l h b k js F0 F2 FM Q x t alpha beta v‖ ≤
        C*(∏ a ∈ univ.erase i, (2:ℝ)^(k a+1))^eta*(1+|t|)*
          (T^eta*T^eta*T^eta)*
          (((⌈D/d⌉.natAbs*⌊H⌋₊:ℕ):ℝ)^eta*((⌈D/d⌉.natAbs*⌊H⌋₊:ℕ):ℝ))*
          (((2:ℝ)^(l+1))^(1/2+eps)*((2:ℝ)^l*U^(1/4:ℝ)+U)) := by
  obtain ⟨C0,hC0,hcell⟩ := cell_averaged hWeil width jets hjets K ks js eps eta S Z heps heta hS hZ
  obtain ⟨C1,hC1,hscale⟩ := PRZZModulusScale.actual_averaged_typeI eta heta
  let c : ℝ := 2^((ks.length+1)*(2*K))
  have hcpos : 0 < c := by dsimp [c]; positivity
  refine ⟨2*C0*C1*c,by positivity,?_⟩
  intro F0 F2 FM hf0 hf2 hfM N y d j l h b hb k i hn hi U T Q x y0 t D H alpha beta hp hs hN hd hh hdT hT hNT ha hz hbeta
  let L : ℝ := ∏ a ∈ univ.erase i, (2:ℝ)^(k a+1)
  have hL : 1 ≤ L := Finset.one_le_prod (fun a _ => one_le_pow₀ (by norm_num))
  have hbnd := hcell F0 F2 FM hf0 hf2 hfM N y d j l h b hb k i hn hi T Q x y0 t D H L alpha beta
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

theorem source_bound (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (width : ℝ) (jets : ℕ → ℝ) (hjets : ∀ n, 0 ≤ jets n)
    (K : ℕ) (ks js : List ℕ) (eps eta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ F0 F2 FM : ℝ → ℂ,
      PRZZProfileMellin.Member width jets F0 → PRZZProfileMellin.Member width jets F2 →
      (∀ x, ‖FM x‖ ≤ jets 0) → ∀ N y d j l h : ℕ, ∀ b ∈ branches y K ks,
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
  obtain ⟨C,hC,hbound⟩ := signed_cell hWeil width jets hjets K ks js eps eta S Z heps heta hS hZ
  refine ⟨C,hC,?_⟩
  intro F0 F2 FM hf0 hf2 hfM N y d j l h b hb k i hn hi U T Q x y0 t D H alpha beta hp hs hN hd hh hdT hT hNT ha hz hbeta
  rw [source_eq_signed]
  exact hbound F0 F2 FM hf0 hf2 hfM N y d j l h b hb k i hn hi U T Q x y0 t D H alpha beta hp hs hN hd hh hdT hT hNT ha hz hbeta

theorem retained_source_bound (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (width : ℝ) (jets : ℕ → ℝ) (hjets : ∀ n, 0 ≤ jets n)
    (K : ℕ) (hK : 4 ≤ K) (ks js : List ℕ) (eps eta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ F0 F2 FM : ℝ → ℂ,
      PRZZProfileMellin.Member width jets F0 → PRZZProfileMellin.Member width jets F2 →
      (∀ x, ‖FM x‖ ≤ jets 0) → ∀ N d j l h : ℕ, ∀ b ∈ branches ⌊(PRZZRowWindow.hi N d h j:ℝ)^((K:ℝ)⁻¹)⌋₊ K ks,
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
  obtain ⟨C,hC,hbound⟩ := source_bound hWeil width jets hjets
    K ks js eps eta S Z heps heta hS hZ
  let c : ℝ := 2^((ks.length+1)*(2*K))
  have hc0 : 0 < c := by dsimp [c]; positivity
  refine ⟨C*(2*c),by positivity,?_⟩
  intro F0 F2 FM hf0 hf2 hfM N d j l h b hb k i U T Q x y0 t D H alpha beta hp hs hlarge hi n hl hu hnz hN hd hh hdT hT hNT ha hz hbeta
  have hn : group N b k univ ≠ 0 := by intro he; exact hnz (by rw [he]; rfl)
  have hy := PRZZTypeIScaleSupplier.retained_root_short N d h j K ks hh hK b hb k U hp hlarge n hl hu hnz
  have hbnd := hbound F0 F2 FM hf0 hf2 hfM N _ d j l h b hb k i hn (hy.trans_lt hi) U T Q x y0 t D H alpha beta
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

#print axioms slice_bound
#print axioms nu_slice_bound
#print axioms signed_slice_bound
#print axioms cell_bound
#print axioms cell_averaged
#print axioms signed_cell
#print axioms source_bound
#print axioms retained_source_bound
end XiPrime8845.PRZZClassSpatialTypeI
