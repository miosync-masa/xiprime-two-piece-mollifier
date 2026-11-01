import PRZZActualCaseSum
import PRZZAllCellsBound
import PRZZLinearOuter

/-! Actual three-case estimates through labelled HB branches and allocations.
The dyadic budgets are retained as explicit finite sums. No CellBound is an
input, and no optimal PRZZ exponent is claimed for the unsimplified budget. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset
namespace XiPrime8845.PRZZActualAggregate
open PRZZActualCaseSum PRZZAllSignedSources PRZZCoefficientSeparation
open PRZZSupportedSplit PRZZGCoefficient PRZZAStarNu
set_option maxHeartbeats 4000000

structure Caps where
  small : ℝ
  typeI : ℝ
  g : ℝ
  di : ℝ
  right : ℝ
  phase : ℝ
  variation : ℝ
  positive : 0 < small ∧ 0 < typeI ∧ 0 < g ∧ 0 < di ∧
    0 < right ∧ 0 < phase ∧ 0 < variation

def row (c : Caps) (eps eta T A : ℝ) (N K j l : ℕ) (ks : List ℕ) : ℝ :=
  smallBudget c.small T A eta l+
    largeBudget c.typeI c.g c.di c.right c.phase c.variation eps eta T A 0 N K j l ks

theorem row_nonneg (c : Caps) (eps eta T A : ℝ) (N K j l : ℕ) (ks : List ℕ)
    (hT : 0 ≤ T) (hA : 0 ≤ A) : 0 ≤ row c eps eta T A N K j l ks := by
  rcases c.positive with ⟨hs,hi,hg,hd,hr,hp,hv⟩
  have hlog : 0 ≤ Real.log ((N:ℝ)+1) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
  unfold row smallBudget largeBudget PRZZCommonCellBound.budget
    PRZZCombinedBudget.total PRZZCombinedBudget.typeI PRZZDISeven.envelope
  positivity

/-- The branch and grid multiplicities are supplied, uniformly in h and its
root cutoff. The explicit row budget has no Mellin-frequency dependence. -/
theorem actual_blocks
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (ks js : List ℕ) (eps eta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (F0 F2 FM : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM) :
    ∃ c : Caps, ∃ C : ℝ, 0 < C ∧
      ∀ N d h j l : ℕ, ∀ T Q D H x y t : ℝ, ∀ alpha beta : ℂ,
      0 < N → 0 < d → 0 < h → 1 < T → (N:ℝ)+1 ≤ T →
      (d:ℝ) ≤ T → (h:ℝ) ≤ T → 1 ≤ Real.log T →
      1 ≤ (PRZZActualSignedBranches.frequencyBound d D H:ℝ) →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z → |beta.re| ≤ S/Real.log T →
      ‖blocks N d h j l K ks js D H x y t
        (PRZZMellinSeparation.scaledCutoff F0 Q) F2 FM alpha beta‖ ≤
      C*T^eta*row c eps eta T (PRZZActualSignedBranches.frequencyBound d D H) N K j l ks*(1+|t|) := by
  obtain ⟨Cs,Ci,Cg,Cd,Cr,Cp,Cv,hs,hi,hg,hd,hr,hp,hv,hsource⟩ :=
    PRZZActualCases.source_bound hWeil hDI K hK ks js eps eta S Z heps heta hS hZ F0 F2 FM hf hc hF hcF hM hcM
  let c : Caps := ⟨Cs,Ci,Cg,Cd,Cr,Cp,Cv,hs,hi,hg,hd,hr,hp,hv⟩
  obtain ⟨C,hC,hblocks⟩ := blocks_bound K ks eta heta
  refine ⟨c,C,hC,?_⟩
  intro N d h j l T Q D H x y t alpha beta hN hd0 hh hT hNT hdT hhT hlog hA ha hz hb
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
      have hh' := hsource N d j l h b hbr (fun i => (k i).val) T Q D H x y t alpha beta
        hN hd0 hh hT hNT hdT hhT hA ha hz hb
      have he : _ ≤ smallBudget Cs T A eta l+
          largeBudget Ci Cg Cd Cr Cp Cv eps eta T A t N K j l ks/(h:ℝ)^(1/4:ℝ) := hh'.trans_eq (by
        dsimp [smallBudget,largeBudget,A]; ring)
      apply he.trans
      apply (add_le_add_right (div_le_self hlarge hden) _).trans
      exact budget_linear_le Cs Ci Cg Cd Cr Cp Cv eps eta T A t N K j l ks (by
        dsimp [smallBudget,A]; positivity))
  exact hbound.trans_eq (by ring)

#print axioms row_nonneg
#print axioms actual_blocks

/-- Explicit finite budget: allocation labels and both dyadic scales remain
visible. C and w are height-independent constants, not cell-bound premises. -/
def totalBudget (C : ℝ) (w : (List ℕ × List ℕ) → ℝ)
    (caps : (List ℕ × List ℕ) → Caps) (js : List ℕ)
    (eps eta beta T A : ℝ) (N d K : ℕ) : ℝ :=
  ∑ j ∈ range (Nat.log 2 N+1), ∑ l ∈ range (Nat.log 2 N+1),
    C*(d:ℝ)^eta*(N:ℝ)^beta*((allocations js).map (fun q =>
      w q*T^eta*row (caps q) eps eta T A N K j l q.2)).sum

theorem totalBudget_nonneg (C : ℝ) (w : (List ℕ × List ℕ) → ℝ)
    (caps : (List ℕ × List ℕ) → Caps) (js : List ℕ)
    (eps eta beta T A : ℝ) (N d K : ℕ)
    (hC : 0 ≤ C) (hw : ∀ q, 0 ≤ w q) (hT : 0 ≤ T) (hA : 0 ≤ A) :
    0 ≤ totalBudget C w caps js eps eta beta T A N d K := by
  apply sum_nonneg; intro j hj
  apply sum_nonneg; intro l hl
  apply mul_nonneg (by positivity)
  apply List.sum_nonneg; intro v hv
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hv
  exact mul_nonneg (mul_nonneg (hw q) (Real.rpow_nonneg hT eta))
    (row_nonneg _ _ _ _ _ _ _ _ _ _ hT hA)

private theorem list_scale {α : Type*} (s : List α) (f : α → ℝ) (r : ℝ) :
    (s.map (fun q => f q*r)).sum = (s.map f).sum*r := by
  induction s with
  | nil => simp
  | cons a s ih => simp only [List.map_cons,List.sum_cons,ih]; ring

/-- All actual branches, supported h, allocation multiplicities and j,l sums.
Weil and DI are the only analytic estimate inputs. The resulting explicit
finite budget is not yet reduced to the optimal PRZZ power of N and T. -/
theorem signedSum_bound
    (hWeil : PRZZKloostermanInputs.WeilIncomplete)
    (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (js : List ℕ) (eps eta beta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hbeta : 0 < beta) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (F0 F2 FM : ℝ → ℂ) (hf : ContDiff ℝ ∞ F0) (hc : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM) :
    ∃ caps : (List ℕ × List ℕ) → Caps, ∃ w : (List ℕ × List ℕ) → ℝ,
      ∃ C : ℝ, 0 < C ∧ (∀ q, 0 < w q) ∧
      ∀ N d : ℕ, ∀ T Q D H x y t : ℝ, ∀ alpha betaShift : ℂ,
      0 < N → 0 < d → 1 < T → (N:ℝ)+1 ≤ T → (d:ℝ) ≤ T → 1 ≤ Real.log T →
      1 ≤ (PRZZActualSignedBranches.frequencyBound d D H:ℝ) →
      |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z → |betaShift.re| ≤ S/Real.log T →
      ‖signedSum N d D H (fun n => (coefficient js n:ℂ))
        (PRZZMellinSeparation.scaledCutoff F0 Q) F2 FM alpha betaShift x y t‖ ≤
      totalBudget C w caps js eps eta beta T
        (PRZZActualSignedBranches.frequencyBound d D H) N d K*(1+|t|) := by
  choose caps w hw hblocks using fun q : List ℕ × List ℕ =>
    actual_blocks hWeil hDI K hK q.2 js eps eta S Z heps heta hS hZ F0 F2 FM hf hc hF hcF hM hcM
  obtain ⟨C,hC,halloc⟩ := PRZZAllCellsBound.allocation_bound js eta beta heta hbeta
  refine ⟨caps,w,C,hC,hw,?_⟩
  intro N d T Q D H x y t alpha betaShift hN hd hT hNT hdT hlog hA ha hz hb
  let A : ℝ := PRZZActualSignedBranches.frequencyBound d D H
  rw [PRZZAllSignedSources.signedSum_eq N d K hd (by omega)]
  unfold totalBudget
  rw [sum_mul]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro j hj
  rw [sum_mul]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro l hl
  have hnq (q : List ℕ × List ℕ) :
      0 ≤ w q*T^eta*row (caps q) eps eta T A N K j l q.2 :=
    mul_nonneg (mul_nonneg (hw q).le (Real.rpow_nonneg (by linarith) eta))
      (row_nonneg _ _ _ _ _ _ _ _ _ _ (by linarith) (by dsimp [A]; positivity))
  have hh := halloc d N hd hN
    (fun q => (w q*T^eta*row (caps q) eps eta T A N K j l q.2)*(1+|t|))
    (fun q h => blocks N d h j l K q.2 js D H x y t
      (PRZZMellinSeparation.scaledCutoff F0 Q) F2 FM alpha betaShift)
    (fun q _ => mul_nonneg (hnq q) (by positivity)) (by
      intro q hq h hh
      have hs := mem_hSupport N d h hh
      have hhn : h ≤ N := by nlinarith [hs.2.1]
      exact hblocks q N d h j l T Q D H x y t alpha betaShift hN hd hs.1 hT hNT hdT
        ((by exact_mod_cast hhn : (h:ℝ) ≤ N).trans (by linarith)) hlog hA ha hz hb)
  rw [list_scale] at hh
  exact hh.trans_eq (by ring)

#print axioms totalBudget_nonneg
#print axioms signedSum_bound
end XiPrime8845.PRZZActualAggregate
