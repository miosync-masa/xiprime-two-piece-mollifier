import PRZZRowCellLayout
import PRZZRetainedScale
import PRZZCombinedBudget
import PRZZDyadicCellBound

/-! The original row-local classifier supplies inflated balance on a common
row scale. The two Type I monomials and seven DI monomials retain h^-1/4
decay. Small and free-factor alternatives are kept explicit. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset
namespace XiPrime8845.PRZZActualBudgetLayout
open PRZZActualBranchCells PRZZActualSupportBoxes PRZZHBBranches
open PRZZCombinedBudget PRZZDISeven
set_option maxHeartbeats 3000000

def freeCase (b : Branch) (k : Fin b.2.length → ℕ) (U : ℝ) : Prop :=
  ∃ i, (∃ J a, PRZZTypedClassification.Free a ∧
    PRZZBranchGrouping.factor b i = PRZZWeightedHeathBrown.weight J (PRZZGroupBounds.atom a)) ∧
    U/U^(1/4:ℝ) < (2:ℝ)^(k i) ∧
    (∏ r ∈ univ.erase i, (2:ℝ)^(k r)) < U^(1/4:ℝ)

theorem typeI_inflate (U Z A V c : ℝ) (hU : 0 ≤ U) (hZ : 0 ≤ Z)
    (hA : 0 ≤ A) (hV : 0 ≤ V) (hc : 1 ≤ c) (hu : U ≤ c*Z) :
    typeI U A V ≤ c*typeI Z A V := by
  have hc0 : 0 ≤ c := by linarith
  have hp : U^(1/4:ℝ) ≤ c*Z^(1/4:ℝ) := by
    calc
      _ ≤ (c*Z)^(1/4:ℝ) := Real.rpow_le_rpow hU hu (by norm_num)
      _ = c^(1/4:ℝ)*Z^(1/4:ℝ) := Real.mul_rpow hc0 hZ
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by simpa using Real.rpow_le_rpow_of_exponent_le hc (show (1/4:ℝ) ≤ 1 by norm_num))
        (Real.rpow_nonneg hZ _)
  unfold typeI
  have h := mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hp hV) hu)
    (show 0 ≤ A*(2*V)^(1/2:ℝ) by positivity)
  exact h.trans_eq (by ring)

/-- No balance premise is required: the original branch cutoff and a
retained sample supply the entire Type II placement. The common X depends
only on j,K,ks, never on the chosen branch or grid. -/
theorem actual_budget_layout (N d h j K : ℕ) (ks : List ℕ)
    (hd : 0 < d) (hh : 0 < h) (hK : 4 ≤ K) (b : Branch)
    (hb : b ∈ branches ⌊(PRZZRowWindow.hi N d h j:ℝ)^((K:ℝ)⁻¹)⌋₊ K ks)
    (k : Fin b.2.length → ℕ) (U : ℝ) (hp : ∏ i, (2:ℝ)^(k i) = U)
    (n : ℕ) (hn : n ≤ N) (hl : PRZZRowWindow.lo h j ≤ n)
    (hu : n ≤ PRZZRowWindow.hi N d h j) (hz : group N b k univ n ≠ 0)
    (A V : ℝ) (hA : 0 ≤ A) (hV : 0 ≤ V) :
    let c : ℝ := 2^((ks.length+1)*(2*K))
    let X : ℝ := (2:ℝ)^j/c
    U ≤ 2*c ∨ freeCase b k U ∨
      ∃ s : Finset (Fin b.2.length),
        typeI U A V+seven h (upper N b k s) A
          ((upper N b k s:ℝ)*(upper N b k (univ \ s):ℝ)) V ≤
          ((2*c)*(2*c^2)^2)*(total X A V/(h:ℝ)^(1/4:ℝ)) := by
  dsimp only
  let c : ℝ := 2^((ks.length+1)*(2*K))
  let X : ℝ := (2:ℝ)^j/c
  have hc : 1 ≤ c := one_le_pow₀ (by norm_num)
  have hX : 0 < X := by dsimp [X,c]; positivity
  have hhR : (1:ℝ) ≤ h := by exact_mod_cast hh
  have hh0 : (0:ℝ) < h := by exact_mod_cast hh
  have hU : 0 ≤ U := hp ▸ (by positivity)
  rcases PRZZRowCellLayout.actual_layout N d h j K ks hh hK b hb k U hp n hn hl hu hz with
    hs | hf | ⟨s,hY,hlo,hhi,hprod,hsplit⟩
  · exact Or.inl hs
  · exact Or.inr (Or.inl hf)
  · apply Or.inr ∘ Or.inr
    refine ⟨s,?_⟩
    have hr := PRZZRetainedScale.retained_scale N d h j _ K ks hd hh b hb k U hp n hl hu hz
    change X/(h:ℝ) ≤ U ∧ U ≤ (2*c)*(X/(h:ℝ)) at hr
    have hboxes := PRZZRetainedScale.balanced_boxes (X/h) U _ _ c
      (div_nonneg hX.le hh0.le) hc hr.1 hr.2 hlo hhi hprod
    have hdI := combined_decay (h:ℝ) (upper N b k s) X _ A V (2*c^2)
      hhR hX hY hA hV (by nlinarith [sq_nonneg (c-1)])
      hboxes.1 hboxes.2.1 hboxes.2.2
    have ht := typeI_inflate U (X/h) A V (2*c) hU (by positivity) hA hV (by linarith) hr.2
    have hs0 : 0 ≤ seven h (upper N b k s) A
        ((upper N b k s:ℝ)*(upper N b k (univ \ s):ℝ)) V := by unfold seven; positivity
    have hsle : seven h (upper N b k s) A
        ((upper N b k s:ℝ)*(upper N b k (univ \ s):ℝ)) V ≤
        (2*c)*seven h (upper N b k s) A
        ((upper N b k s:ℝ)*(upper N b k (univ \ s):ℝ)) V :=
      le_mul_of_one_le_left hs0 (by linarith)
    calc
      _ ≤ (2*c)*(typeI (X/h) A V+seven h (upper N b k s) A
          ((upper N b k s:ℝ)*(upper N b k (univ \ s):ℝ)) V) :=
        (add_le_add ht hsle).trans_eq (by ring)
      _ ≤ (2*c)*((2*c^2)^2*(total X A V/(h:ℝ)^(1/4:ℝ))) :=
        mul_le_mul_of_nonneg_left hdI (by positivity)
      _ = _ := by ring

#print axioms typeI_inflate
#print axioms actual_budget_layout
theorem actual_source_bound (hDI : PRZZKloostermanInputs.DeshouillersIwaniecLemma1)
    (K : ℕ) (hK : 4 ≤ K) (ks js : List ℕ) (eps eta S Z : ℝ)
    (heps : 0 < eps) (heta : 0 < eta) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (F0 F2 FM : ℝ → ℂ) (hF0 : ContDiff ℝ ∞ F0) (hc0 : HasCompactSupport F0)
    (hF : Continuous F2) (hcF : HasCompactSupport F2)
    (hM : Continuous FM) (hcM : HasCompactSupport FM) :
    ∃ Cg Cd Cr Cp Cv : ℝ, 0 < Cg ∧ 0 < Cd ∧ 0 < Cr ∧ 0 < Cp ∧ 0 < Cv ∧
      ∀ (N d j l h : ℕ) (b : Branch), 1 ≤ N → 1 ≤ d → 1 ≤ h →
      b ∈ branches ⌊(PRZZRowWindow.hi N d h j:ℝ)^((K:ℝ)⁻¹)⌋₊ K ks → ∀ k : Fin b.2.length → ℕ,
      ∀ U : ℝ, (∏ i, (2:ℝ)^(k i)) = U →
      ∀ n : ℕ, n ≤ N → PRZZRowWindow.lo h j ≤ n →
      n ≤ PRZZRowWindow.hi N d h j → group N b k univ n ≠ 0 → ∀ T Q D H x y0 t A : ℝ,
      1 < T → (N:ℝ)+1 ≤ T → (h:ℝ) ≤ T → 1 ≤ A →
      ∀ alpha beta : ℂ, |alpha.re| ≤ S/Real.log T → 1+‖alpha‖ ≤ Z →
      |beta.re| ≤ S/Real.log T →
      let c : ℝ := 2^((ks.length+1)*(2*K))
      let X : ℝ := (2:ℝ)^j/c
      U ≤ 2*c ∨ freeCase b k U ∨
      ‖PRZZSignedSourceCell.source N d j l h A b k
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (PRZZMellinSeparation.scaledCutoff F0 Q) F2 FM alpha beta x t
        (fun a => PRZZNuCoefficient.nu (PRZZAStarNu.frequencies d D H) x y0 (a:ℤ))
        (fun a => PRZZNuCoefficient.nu (PRZZAStarNu.frequencies d D H) x y0 (-(a:ℤ)))‖ ≤
      PRZZCommonCellBound.budget Cg Cd Cr Cp Cv eps eta N T A t *
        (((2*c)*(2*c^2)^2)*(total X A (PRZZDyadicModulus.bound N l)/(h:ℝ)^(1/4:ℝ))) := by
  obtain ⟨Cg,Cd,Cr,Cp,Cv,hg,hcd,hr,hcp,hcv,hbound⟩ :=
    PRZZDyadicCellBound.source_bound hDI K ks js eps eta S Z heps heta hS hZ
      F0 F2 FM hF0 hc0 hF hcF hM hcM
  refine ⟨Cg,Cd,Cr,Cp,Cv,hg,hcd,hr,hcp,hcv,?_⟩
  intro N d j l h b hN hd hh hb k U hp n hn hl hu hnz T Q D H x y0 t A hT hNT hhT hA alpha beta ha hz hbeta
  dsimp only
  rcases actual_budget_layout N d h j K ks (by omega) (by omega) hK b hb k U hp n hn hl hu hnz
    A (PRZZDyadicModulus.bound N l) (by linarith) (Nat.cast_nonneg _) with hs | hf | ⟨s,hs⟩
  · exact Or.inl hs
  · exact Or.inr (Or.inl hf)
  · apply Or.inr ∘ Or.inr
    have hbnd := hbound N d _ j l h b hN hd hh hb k s T Q D H x y0 t A hT hNT hhT hA alpha beta ha hz hbeta
    apply hbnd.trans
    have hU : 0 ≤ U := hp ▸ (by positivity)
    have ht : 0 ≤ typeI U A (PRZZDyadicModulus.bound N l) := by unfold typeI; positivity
    have hs' := (le_add_of_nonneg_left ht).trans hs
    apply mul_le_mul_of_nonneg_left hs'
    have hlog : 0 ≤ Real.log ((N:ℝ)+1) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
    unfold PRZZCommonCellBound.budget
    positivity

#print axioms actual_source_bound

/-- The actual Type I product scale uses the SAME branch-independent X.
This transports its two monomials, not an assumed bound on the cell. -/
theorem retained_typeI_decay (N d h j y K : ℕ) (ks : List ℕ)
    (hd : 0 < d) (hh : 0 < h) (b : Branch) (hb : b ∈ branches y K ks)
    (k : Fin b.2.length → ℕ) (U : ℝ) (hp : ∏ i, (2:ℝ)^(k i) = U)
    (n : ℕ) (hl : PRZZRowWindow.lo h j ≤ n)
    (hu : n ≤ PRZZRowWindow.hi N d h j) (hz : group N b k univ n ≠ 0)
    (A V : ℝ) (hA : 0 ≤ A) (hV : 0 ≤ V) :
    let c : ℝ := 2^((ks.length+1)*(2*K))
    let X : ℝ := (2:ℝ)^j/c
    typeI U A V ≤ (2*c)*(typeI X A V/(h:ℝ)^(1/4:ℝ)) := by
  dsimp only
  have hc : (1:ℝ) ≤ 2^((ks.length+1)*(2*K)) := one_le_pow₀ (by norm_num)
  have hr := PRZZRetainedScale.retained_scale N d h j y K ks hd hh b hb k U hp n hl hu hz
  have hU : 0 ≤ U := hp ▸ (by positivity)
  have ht := typeI_inflate U _ A V _ hU (by positivity) hA hV (by linarith) hr.2
  exact ht.trans (mul_le_mul_of_nonneg_left
    (typeI_decay h _ A V (by exact_mod_cast hh) (by positivity) hA hV) (by positivity))

/-- Bounded-small actual cells lie in the high-h tail of the common row
scale. This is the threshold needed by the existing split h average. -/
theorem small_retained_threshold (N d h j y K : ℕ) (ks : List ℕ)
    (hd : 0 < d) (hh : 0 < h) (b : Branch) (hb : b ∈ branches y K ks)
    (k : Fin b.2.length → ℕ) (U : ℝ) (hp : ∏ i, (2:ℝ)^(k i) = U)
    (n : ℕ) (hl : PRZZRowWindow.lo h j ≤ n)
    (hu : n ≤ PRZZRowWindow.hi N d h j) (hz : group N b k univ n ≠ 0)
    (hs : U ≤ 2*((2:ℝ)^((ks.length+1)*(2*K)))) :
    ((2:ℝ)^j/2^((ks.length+1)*(2*K)))/(2*2^((ks.length+1)*(2*K))) ≤ h := by
  have hr := PRZZRetainedScale.retained_scale N d h j y K ks hd hh b hb k U hp n hl hu hz
  have h0 : (0:ℝ) < h := by exact_mod_cast hh
  apply (div_le_iff₀ (by positivity)).mpr
  have hb := (div_le_iff₀ h0).mp (hr.1.trans hs)
  simpa only [mul_comm] using hb

#print axioms retained_typeI_decay
#print axioms small_retained_threshold
end XiPrime8845.PRZZActualBudgetLayout
