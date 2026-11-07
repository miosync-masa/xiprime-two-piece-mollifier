import PRZZLocalCentralTransfer
import PRZZLargeResolvedPruning
import PRZZGammaBudgetAbsorption

/-! The boundary M=T^b belongs only to the small side. Strict large-M
pruning is reduced exactly to the next dyadic threshold, not estimated
by the norm of a larger complex sum. The complete resolved large family
is bounded collectively; no isolated Fourier component is declared small. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset Filter Set MeasureTheory Complex
namespace XiPrime8845.PRZZDisjointSpatialJoin
open PRZZMellinSeparation PRZZRetainedNative PRZZLocalCentralTransfer
set_option maxHeartbeats 8000000
attribute [local instance] Classical.propDecidable

theorem exists_dyadic (X : ℝ) : ∃ n : ℕ, X < (2:ℝ)^n := by
  obtain ⟨n,hn⟩ := exists_nat_gt X
  have hh : n ≤ 2^n := Nat.le_of_lt Nat.lt_two_pow_self
  exact ⟨n,hn.trans_le (by exact_mod_cast hh)⟩

def nextIndex (X : ℝ) : ℕ := Nat.find (exists_dyadic X)
def nextScale (X : ℝ) : ℝ := (2:ℝ)^(nextIndex X)

theorem lt_next (X : ℝ) : X < nextScale X := Nat.find_spec (exists_dyadic X)

theorem strict_iff (X : ℝ) (s : ℕ) : X < (2:ℝ)^s ↔ nextScale X ≤ (2:ℝ)^s := by
  constructor
  · intro h
    have hn : nextIndex X ≤ s := Nat.find_min' (exists_dyadic X) h
    exact pow_le_pow_right₀ (by norm_num) hn
  · intro h
    exact (lt_next X).trans_le h

def strictLarge (L J N : ℕ) (F G H : ℝ → ℂ) (a : ℕ → ℂ)
    (X : ℝ) (alpha beta : ℂ) (t : ℝ) : ℂ :=
  PRZZResolvedComplement.masked L J N F G H a (fun s _ => X < (2:ℝ)^s) alpha beta t

theorem strictLarge_eq (L J N : ℕ) (F G H : ℝ → ℂ) (a : ℕ → ℂ)
    (X : ℝ) (alpha beta : ℂ) (t : ℝ) :
    strictLarge L J N F G H a X alpha beta t =
      PRZZResolvedComplement.masked L J N F G H a
        (fun s _ => nextScale X ≤ (2:ℝ)^s) alpha beta t := by
  simp only [strictLarge,strict_iff]

theorem uniform (P : ℝ → ℝ) (hm : Antitone P)
    (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ))) (js : List ℕ) (S r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (L J N : ℕ) (A B : ℂ) (t X : ℝ),
      1 ≤ N → (N:ℝ) ≤ T → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      t ∈ Icc T (2*T) → 0 < X →
      ‖strictLarge L J N (fun x => (P x:ℂ)) (fun _ => 1) (fun _ => 1)
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) X
        (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t‖ ≤ C*T^6/X^2 := by
  obtain ⟨C,hC,h⟩ := PRZZLargeResolvedPruning.masked_uniform P hm hlo hhi hl hright hP js S r hr
  refine ⟨C,hC,?_⟩
  filter_upwards [h,eventually_gt_atTop (0:ℝ)] with T h hT
  intro L J N A B t X hN hNT hA hB hsep ht hX
  rw [strictLarge_eq]
  apply (h L J N A B t (nextScale X) hN hNT hA hB hsep ht
    (hX.trans (lt_next X))).trans
  gcongr
  exact (lt_next X).le

/-- No spatial endpoint is counted twice. -/
theorem family_split (L J N : ℕ) (F G H : ℝ → ℂ) (a : ℕ → ℂ)
    (X : ℝ) (alpha beta : ℂ) (t : ℝ) :
    PRZZAllPoissonRows.family L J N F G H a alpha beta t =
      PRZZSourceMaskFamily.selectedFamily L J N F G H a
        (fun s _ => (2:ℝ)^s ≤ X) alpha beta t+
      strictLarge L J N F G H a X alpha beta t := by
  have hh := PRZZResolvedComplement.exhaustive L J N F G H a
    (fun s _ => (2:ℝ)^s ≤ X) alpha beta t
  simpa only [not_le,strictLarge,PRZZResolvedComplement.masked,
    PRZZSourceMaskFamily.selectedFamily] using hh

/-- Same masks as the local transfer. The small discarded branch is
kept exact, and the large branch is a complete resolved family. -/
theorem source_split (L J N : ℕ) (F G H : ℝ → ℂ) (a : ℕ → ℂ)
    (T Q b eD : ℝ) (alpha beta : ℂ) (t : ℝ) :
    PRZZAllPoissonRows.family L J N F G H a alpha beta t =
      PRZZSourceMaskFamily.selectedFamily L J N F G H a
        (fun s z => (2:ℝ)^s ≤ T^b ∧ ¬PRZZSourceMaskFamily.discarded T Q eD s z) alpha beta t+
      PRZZSourceMaskFamily.selectedFamily L J N F G H a
        (fun s z => (2:ℝ)^s ≤ T^b ∧ PRZZSourceMaskFamily.discarded T Q eD s z) alpha beta t+
      strictLarge L J N F G H a (T^b) alpha beta t := by
  rw [family_split L J N F G H a (T^b) alpha beta t]
  congr 1
  unfold PRZZSourceMaskFamily.selectedFamily
  simp only [← sum_add_distrib]
  apply sum_congr rfl; intro s hs
  apply sum_congr rfl; intro z hz
  by_cases hg : z.2.1 ≠ 0 <;> by_cases hm : (2:ℝ)^s ≤ T^b <;>
    by_cases hd : PRZZSourceMaskFamily.discarded T Q eD s z <;> simp [hg,hm,hd]

/-- The actual full family after the disjoint spatial/source split.
This is an equality, not a bound on the remaining local central sum. -/
theorem family_local (F G W : ℝ → ℂ) (js : List ℕ) (L N J : ℕ) (dual : Bool)
    (T Q V b eD eH t : ℝ) (A B : ℂ) :
    let mask := fun s z => (2:ℝ)^s ≤ T^b ∧ ¬PRZZSourceMaskFamily.discarded T Q eD s z
    let a := fun n => (PRZZGCoefficient.coefficient js n:ℂ)
    let alpha := A/(Real.log T:ℂ)
    let beta := B/(Real.log T:ℂ)
    PRZZResolvedTailMass.branch dual A B T t *
      PRZZAllPoissonRows.family L J N W (scaledCutoff F Q) (scaledCutoff G V) a alpha beta t =
      partField .central (PRZZSelectedLocalFourier.sourceCutoff T eH) F G (PRZZWRowLimit.profile W)
        js L N dual T Q V b eD t A B+
      selectedRemainder F G W js L N J dual T Q V b eD eH t A B+
      PRZZResolvedTailMass.branch dual A B T t *
        (-selectedPart .boundary L J N W (scaledCutoff F Q) (scaledCutoff G V) a mask alpha beta t+
         selectedPart .freeze L J N W (scaledCutoff F Q) (scaledCutoff G V) a mask alpha beta t+
         selectedPart .outside L J N W (scaledCutoff F Q) (scaledCutoff G V) a mask alpha beta t)+
      PRZZResolvedTailMass.branch dual A B T t *
        PRZZSourceMaskFamily.selectedFamily L J N W (scaledCutoff F Q) (scaledCutoff G V) a
          (fun s z => (2:ℝ)^s ≤ T^b ∧ PRZZSourceMaskFamily.discarded T Q eD s z) alpha beta t+
      PRZZResolvedTailMass.branch dual A B T t *
        strictLarge L J N W (scaledCutoff F Q) (scaledCutoff G V) a (T^b) alpha beta t := by
  dsimp only
  rw [source_split L J N W (scaledCutoff F Q) (scaledCutoff G V) _ T Q b eD]
  rw [mul_add,mul_add,selected_family_decomposition]

/-- The complete strict-large family, actual time cutoff and actual
dual Gamma multiplier are paid in the common target. This applies after
arithmetic partition reconstruction, not by summing norms of windows. -/
theorem actual_large_time (P : ℝ → ℝ) (hm : Antitone P)
    (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ)))
    (Phi : ℝ → ℂ) (hPhi : Continuous Phi) (hcPhi : HasCompactSupport Phi)
    (js : List ℕ) (S r b delta : ℝ) (hS : 0 ≤ S) (hr : 0 < r)
    (hexp : 7-2*b ≤ delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (L J N : ℕ) (dual : Bool) (A B : ℂ),
      1 ≤ N → (N:ℝ) ≤ T → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      (∫ t in Icc T (2*T), ‖scaledCutoff Phi T t*
        (PRZZResolvedTailMass.branch dual A B T t *
          strictLarge L J N (fun x => (P x:ℂ)) (fun _ => 1) (fun _ => 1)
            (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) (T^b)
            (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t)‖) ≤
        C*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := uniform P hm hlo hhi hl hright hP js S r hr
  let E := Real.exp (4*S+7)
  let Z := ∫ t : ℝ, ‖Phi t‖
  have hZ : 0 ≤ Z := integral_nonneg (fun t => norm_nonneg _)
  refine ⟨C*E*(Z+1),by dsimp [E]; positivity,?_⟩
  filter_upwards [h,PRZZResolvedTailMass.branch_cap S hS,
    eventually_ge_atTop (1:ℝ)] with T h hcap hT
  intro L J N dual A B hN hNT hA hB hsep
  have ht : 0 < T := by linarith
  have hi : IntegrableOn (fun t => (C*E*T^6/(T^b)^2)*‖scaledCutoff Phi T t‖) (Icc T (2*T)) :=
    (continuous_const.mul (hPhi.comp (continuous_const.mul continuous_id)).norm).integrableOn_Icc
  have hbnd : (∫ t in Icc T (2*T), ‖scaledCutoff Phi T t*
      (PRZZResolvedTailMass.branch dual A B T t *
        strictLarge L J N (fun x => (P x:ℂ)) (fun _ => 1) (fun _ => 1)
          (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) (T^b)
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t)‖) ≤
      (C*E*T^6/(T^b)^2)*(∫ t in Icc T (2*T), ‖scaledCutoff Phi T t‖) := by
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg (Eventually.of_forall (fun t => norm_nonneg _)) hi
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t htmem
    have hg : ‖PRZZResolvedTailMass.branch dual A B T t‖ ≤ E := by
      simpa [E] using hcap dual A B t 1 hA hB htmem le_rfl hT
    have hh := h L J N A B t (T^b) hN hNT hA hB hsep htmem (by positivity)
    simp only [norm_mul]
    exact (mul_le_mul_of_nonneg_left (mul_le_mul hg hh (norm_nonneg _) (by dsimp [E]; positivity))
      (norm_nonneg _)).trans_eq (by ring)
  have hmass := PRZZGammaBudgetAbsorption.scaled_time_mass Phi hPhi hcPhi T ht
  have he : T^6/(T^b)^2*T = T^(7-2*b) := by
    calc
      _ = T^((6:ℝ)-b*2)*T := by
        rw [← Real.rpow_natCast T 6,← Real.rpow_natCast (T^b) 2,
          ← Real.rpow_mul ht.le,← Real.rpow_sub ht]
        norm_num
      _ = T^((6:ℝ)-b*2)*T^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add ht]; congr 1; ring
  have htarg : 1 ≤ PRZZOptimalPowers.target N T := by
    unfold PRZZOptimalPowers.target
    exact (Real.one_le_rpow (by exact_mod_cast hN : (1:ℝ) ≤ N) (by norm_num : (0:ℝ) ≤ 7/4)).trans
      (le_add_of_nonneg_right (by positivity))
  calc
    _ ≤ (C*E*T^6/(T^b)^2)*(T*Z) := hbnd.trans
      (mul_le_mul_of_nonneg_left hmass (by dsimp [E]; positivity))
    _ = C*E*Z*T^(7-2*b) := by rw [← he]; ring
    _ ≤ C*E*(Z+1)*T^delta := by gcongr; linarith
    _ ≤ _ := le_mul_of_one_le_right (by dsimp [E]; positivity) htarg

#print axioms exists_dyadic
#print axioms lt_next
#print axioms strict_iff
#print axioms strictLarge_eq
#print axioms uniform
#print axioms family_split
#print axioms source_split
#print axioms family_local
#print axioms actual_large_time
end XiPrime8845.PRZZDisjointSpatialJoin
