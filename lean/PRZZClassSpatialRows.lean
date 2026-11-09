/- Spatial cutoff support is unrestricted here: only its common norm cap is used. -/
import PRZZClassSpatialCases
import PRZZFiniteFamilyRows

/-! Class-uniform actual HB branch, grid and allocation sums with independent
left/right arithmetic labels. No analytic cell-bound premise is introduced.
Explicit finite row budgets are retained; full mixed AFE assembly is separate. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset Complex
namespace XiPrime8845.PRZZClassSpatialRows
open PRZZActualCaseSum PRZZActualAggregate PRZZAllSignedSources PRZZCoefficientSeparation
open PRZZSupportedSplit PRZZGCoefficient PRZZAStarNu PRZZNuCoefficient
open PRZZSupportedBranches PRZZSupportedSource PRZZSupportedAllocation
open PRZZMellinSeparation PRZZHBRectangles PRZZFiniteFamilyRows
set_option maxHeartbeats 10000000

theorem actual_blocks
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (ks js : List ℕ) (eps eta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (width : ℝ) (jets : ℕ → ℝ) (hjets : ∀ n, 0 ≤ jets n) :
    ∃ c : Caps, ∃ C : ℝ, 0 < C ∧
      ∀ F0 F2 FM : ℝ → ℂ, PRZZProfileMellin.Member width jets F0 →
      PRZZProfileMellin.Member width jets F2 → (∀ x, ‖FM x‖ ≤ jets 0) →
      ∀ N d h j l : ℕ, ∀ T Q D H x y t : ℝ, ∀ alpha beta : ℂ,
      0 < N → 0 < d → 0 < h → 1 < T → (N:ℝ)+1 ≤ T →
      (d:ℝ) ≤ T → (h:ℝ) ≤ T → 1 ≤ Real.log T →
      1 ≤ (PRZZActualSignedBranches.frequencyBound d D H:ℝ) →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z → |beta.re| ≤ S/Real.log T →
      ‖blocks N d h j l K ks js D H x y t
        (PRZZMellinSeparation.scaledCutoff F0 Q) F2 FM alpha beta‖ ≤
      C*T^eta*row c eps eta T (PRZZActualSignedBranches.frequencyBound d D H) N K j l ks*(1+|t|) := by
  obtain ⟨Cs,Ci,Cg,Cd,Cr,Cp,Cv,hs,hi,hg,hd,hr,hp,hv,hsource⟩ :=
    PRZZClassSpatialCases.source_bound hWeil hDI K hK ks js eps eta S Z heps heta hS hZ width jets hjets
  let c : Caps := ⟨Cs,Ci,Cg,Cd,Cr,Cp,Cv,hs,hi,hg,hd,hr,hp,hv⟩
  obtain ⟨C,hC,hblocks⟩ := blocks_bound K ks eta heta
  refine ⟨c,C,hC,?_⟩
  intro F0 F2 FM hf0 hf2 hfM N d h j l T Q D H x y t alpha beta hN hd0 hh hT hNT hdT hhT hlog hA ha hz hb
  let A : ℝ := PRZZActualSignedBranches.frequencyBound d D H
  have hrow := row_nonneg c eps eta T A N K j l ks (by linarith) (by dsimp [A]; positivity)
  have hlarge : 0 ≤ largeBudget Ci Cg Cd Cr Cp Cv eps eta T A t N K j l ks := by
    have hln : 0 ≤ Real.log ((N:ℝ)+1) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
    unfold largeBudget PRZZCommonCellBound.budget PRZZCombinedBudget.total PRZZCombinedBudget.typeI PRZZDISeven.envelope
    dsimp [A]
    positivity
  have hden : 1 ≤ (h:ℝ)^(1/4:ℝ) := Real.one_le_rpow (by exact_mod_cast hh) (by norm_num)
  have hbound := hblocks N d h j l hN T
    (row c eps eta T A N K j l ks*(1+|t|)) (by linarith) hlog (by positivity)
    js D H x y t _ F2 FM alpha beta (by
      intro b hbr k
      have hh' := hsource F0 F2 FM hf0 hf2 hfM N d j l h b hbr (fun i => (k i).val) T Q D H x y t alpha beta
        hN hd0 hh hT hNT hdT hhT hA ha hz hb
      have he : _ ≤ smallBudget Cs T A eta l+
          largeBudget Ci Cg Cd Cr Cp Cv eps eta T A t N K j l ks/(h:ℝ)^(1/4:ℝ) := hh'.trans_eq (by
        dsimp [smallBudget,largeBudget,A]; ring)
      apply he.trans
      apply (add_le_add_right (div_le_self hlarge hden) _).trans
      exact budget_linear_le Cs Ci Cg Cd Cr Cp Cv eps eta T A t N K j l ks (by
        dsimp [smallBudget,A]; positivity))
  exact hbound.trans_eq (by ring)

theorem basis_bound
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js ks : List ℕ) (eps eta beta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hbeta : 0 < beta) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (width : ℝ) (jets : ℕ → ℝ) (hjets : ∀ n, 0 ≤ jets n) :
    ∃ caps : (List ℕ × List ℕ) → Caps, ∃ w : (List ℕ × List ℕ) → ℝ,
      ∃ C : ℝ, 0 < C ∧ (∀ q, 0 < w q) ∧
      ∀ F0 F2 FM : ℝ → ℂ, PRZZProfileMellin.Member width jets F0 →
      PRZZProfileMellin.Member width jets F2 → (∀ x, ‖FM x‖ ≤ jets 0) →
      ∀ N d j l : ℕ, ∀ T Q D H x y t : ℝ, ∀ alpha betaShift : ℂ,
      0 < N → 0 < d → 1 < T → (N:ℝ)+1 ≤ T → (d:ℝ) ≤ T → 1 ≤ Real.log T →
      1 ≤ (PRZZActualSignedBranches.frequencyBound d D H:ℝ) →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z → |betaShift.re| ≤ S/Real.log T →
      ‖signedRow N d j l D H (fun n => (coefficient js n:ℂ))
        (fun n => (coefficient ks n:ℂ)) (scaledCutoff F0 Q) F2 FM alpha betaShift x y t‖ ≤
      budget C w caps js eps eta beta T
        (PRZZActualSignedBranches.frequencyBound d D H) N d K j l*(1+|t|) := by
  choose caps w hw hblocks using fun q : List ℕ × List ℕ =>
    actual_blocks hWeil hDI K hK q.2 ks eps eta S Z heps heta hS hZ
      width jets hjets
  obtain ⟨C,hC,halloc⟩ := PRZZAllCellsBound.allocation_bound js eta beta heta hbeta
  refine ⟨caps,w,C,hC,hw,?_⟩
  intro F0 F2 FM hf0 hf2 hfM N d j l T Q D H x y t alpha betaShift hN hd hT hNT hdT hlog hA ha hz hb
  let A : ℝ := PRZZActualSignedBranches.frequencyBound d D H
  rw [mixed_blocks N d j l K hd (by omega)]
  have hnq (q : List ℕ × List ℕ) :
      0 ≤ w q*T^eta*PRZZActualAggregate.row (caps q) eps eta T A N K j l q.2 :=
    mul_nonneg (mul_nonneg (hw q).le (Real.rpow_nonneg (by linarith) eta))
      (row_nonneg _ _ _ _ _ _ _ _ _ _ (by linarith) (by dsimp [A]; positivity))
  have hh := halloc d N hd hN
    (fun q => (w q*T^eta*PRZZActualAggregate.row (caps q) eps eta T A N K j l q.2)*(1+|t|))
    (fun q h => blocks N d h j l K q.2 ks D H x y t (scaledCutoff F0 Q) F2 FM alpha betaShift)
    (fun q _ => mul_nonneg (hnq q) (by positivity)) (by
      intro q hq h hh
      have hs := mem_hSupport N d h hh
      have hhn : h ≤ N := by nlinarith [hs.2.1]
      exact hblocks q F0 F2 FM hf0 hf2 hfM N d h j l T Q D H x y t alpha betaShift hN hd hs.1 hT hNT hdT
        ((by exact_mod_cast hhn : (h:ℝ) ≤ N).trans (by linarith)) hlog hA ha hz hb)
  have hscale (qs : List (List ℕ × List ℕ)) (f : (List ℕ × List ℕ) → ℝ) (r : ℝ) :
      (qs.map (fun q => f q*r)).sum = (qs.map f).sum*r := by
    induction qs with
    | nil => simp
    | cons q qs ih => simp only [List.map_cons,List.sum_cons,ih]; ring
  rw [hscale] at hh
  exact hh.trans_eq (by dsimp [budget,A]; ring)

def signedSum (N d : ℕ) (D H : ℝ) (a b : ℕ → ℂ)
    (F1 F2 FM : ℝ → ℂ) (alpha beta : ℂ) (x y t : ℝ) : ℂ :=
  ∑ j ∈ range (Nat.log 2 N+1), ∑ l ∈ range (Nat.log 2 N+1),
    PRZZFiniteFamilyRows.signedRow N d j l D H a b F1 F2 FM alpha beta x y t

/-- Both complete dyadic grids use the same function-independent constants. -/
theorem signedSum_bound
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js ks : List ℕ) (eps eta beta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hbeta : 0 < beta) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (width : ℝ) (jets : ℕ → ℝ) (hjets : ∀ n, 0 ≤ jets n) :
    ∃ caps : (List ℕ × List ℕ) → Caps, ∃ w : (List ℕ × List ℕ) → ℝ,
      ∃ C : ℝ, 0 < C ∧ (∀ q, 0 < w q) ∧
      ∀ F0 F2 FM : ℝ → ℂ, PRZZProfileMellin.Member width jets F0 →
      PRZZProfileMellin.Member width jets F2 → (∀ x, ‖FM x‖ ≤ jets 0) →
      ∀ N d : ℕ, ∀ T Q D H x y t : ℝ, ∀ alpha betaShift : ℂ,
      0 < N → 0 < d → 1 < T → (N:ℝ)+1 ≤ T → (d:ℝ) ≤ T → 1 ≤ Real.log T →
      1 ≤ (PRZZActualSignedBranches.frequencyBound d D H:ℝ) →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z → |betaShift.re| ≤ S/Real.log T →
      ‖signedSum N d D H (fun n => (coefficient js n:ℂ))
        (fun n => (coefficient ks n:ℂ)) (scaledCutoff F0 Q) F2 FM alpha betaShift x y t‖ ≤
      totalBudget C w caps js eps eta beta T
        (PRZZActualSignedBranches.frequencyBound d D H) N d K*(1+|t|) := by
  obtain ⟨caps,w,C,hC,hw,h⟩ := basis_bound hWeil hDI K hK js ks eps eta beta S Z
    heps heta hbeta hS hZ width jets hjets
  refine ⟨caps,w,C,hC,hw,?_⟩
  intro F0 F2 FM hf0 hf2 hfM N d T Q D H x y t alpha betaShift hN hd hT hNT hdT hlog hA ha hz hb
  unfold signedSum totalBudget
  rw [sum_mul]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro j hj
  rw [sum_mul]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro l hl
  exact h F0 F2 FM hf0 hf2 hfM N d j l T Q D H x y t alpha betaShift
    hN hd hT hNT hdT hlog hA ha hz hb

#print axioms actual_blocks
#print axioms basis_bound
#print axioms signedSum_bound
end XiPrime8845.PRZZClassSpatialRows
