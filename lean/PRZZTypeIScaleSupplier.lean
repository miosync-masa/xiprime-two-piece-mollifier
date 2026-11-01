import PRZZModulusScale

/-! Actual signed Type I cells with the dyadic modulus scale supplied.
Weil remains an explicit hypothesis. Both signs, nu, the right coefficient,
coprimality and the sharp product cutoff are retained. This is a Type I
supplier, not a bound for all signedCells or the original A-star. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset
namespace XiPrime8845.PRZZTypeIScaleSupplier
open PRZZActualBranchCells PRZZHBBranches
set_option maxHeartbeats 2000000

/-- For the ORIGINAL row-local HB cutoff, a retained sample supplies the
short-root condition. Thus the classifier's large free factor really lies
beyond the truncated Moebius support. No replacement branch list is used. -/
theorem retained_root_short (N d h j K : ℕ) (ks : List ℕ)
    (hh : 0 < h) (hK : 4 ≤ K) (b : Branch)
    (hb : b ∈ branches ⌊(PRZZRowWindow.hi N d h j:ℝ)^((K:ℝ)⁻¹)⌋₊ K ks)
    (k : Fin b.2.length → ℕ) (U : ℝ) (hp : ∏ a, (2:ℝ)^(k a) = U)
    (hlarge : 2*((2:ℝ)^((ks.length+1)*(2*K))) < U)
    (n : ℕ) (hl : PRZZRowWindow.lo h j ≤ n)
    (hu : n ≤ PRZZRowWindow.hi N d h j) (hz : group N b k univ n ≠ 0) :
    (⌊(PRZZRowWindow.hi N d h j:ℝ)^((K:ℝ)⁻¹)⌋₊:ℝ) ≤ U/U^(1/4:ℝ) := by
  have hc : (1:ℝ) ≤ 2^((ks.length+1)*(2*K)) := one_le_pow₀ (by norm_num)
  have hU : 1 < U := by linarith
  have hx : (1:ℝ) ≤ PRZZRowWindow.hi N d h j := by
    exact_mod_cast (show 1 ≤ PRZZRowWindow.hi N d h j from
      (show 1 ≤ PRZZRowWindow.lo h j from Nat.succ_le_succ (Nat.zero_le _)).trans (hl.trans hu))
  have hbnd := PRZZRowCellLayout.cutoff_le N d h j K ks hh b hb k U hp n hl hz
  have hshort := PRZZSourceScales.local_root_short K _ U hK hx hU.le (by nlinarith)
  exact (PRZZSourceScales.quarter_conditions U _ hU hshort).2.2

/-- All analytic and arithmetic costs of a genuine free-factor cell are
inserted before the Type I two-term scale. Constants are chosen before
height, dyadic cells, local HB cutoff and the chosen branch. -/
theorem signed_cell (hWeil : PRZZKloostermanInputs.WeilIncomplete)
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
      ‖∑ v ∈ (PRZZAStarNu.frequencies d D H).image PRZZNuCoefficient.freq,
        PRZZNuCoefficient.nu (PRZZAStarNu.frequencies d D H) x y0 v *
          PRZZFreeCell.cell N d j l h b k js F0 F2 FM Q x t alpha beta v‖ ≤
        C*(∏ a ∈ univ.erase i, (2:ℝ)^(k a+1))^eta*(1+|t|)*
          (T^eta*T^eta*T^eta)*
          (((⌈D/d⌉.natAbs*⌊H⌋₊:ℕ):ℝ)^eta*((⌈D/d⌉.natAbs*⌊H⌋₊:ℕ):ℝ))*
          (((2:ℝ)^(l+1))^(1/2+eps)*((2:ℝ)^l*U^(1/4:ℝ)+U)) := by
  obtain ⟨C0,hC0,hcell⟩ := PRZZLengthBudget.signed_cell_averaged hWeil F0 F2 FM
    hf hc hF hcF hM hcM K ks js eps eta S Z heps heta hS hZ
  obtain ⟨C1,hC1,hscale⟩ := PRZZModulusScale.actual_averaged_typeI eta heta
  let c : ℝ := 2^((ks.length+1)*(2*K))
  have hcpos : 0 < c := by dsimp [c]; positivity
  refine ⟨2*C0*C1*c,by positivity,?_⟩
  intro N y d j l h b hb k i hn hi U T Q x y0 t D H alpha beta hp hs hN hd hh hdT hT hNT ha hz hbeta
  let L : ℝ := ∏ a ∈ univ.erase i, (2:ℝ)^(k a+1)
  have hL : 1 ≤ L := Finset.one_le_prod (fun a _ => one_le_pow₀ (by norm_num))
  have hbnd := hcell N y d j l h b hb k i hn hi T Q x y0 t D H L alpha beta
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

#print axioms signed_cell
#print axioms retained_root_short
end XiPrime8845.PRZZTypeIScaleSupplier
