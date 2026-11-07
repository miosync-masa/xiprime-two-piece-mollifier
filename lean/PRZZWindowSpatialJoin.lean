import PRZZWindowCentralAssembly
import PRZZDisjointSpatialJoin

/-! Boundary-safe return of the fixed-window body to the full native AFE
family. The polynomial endpoint is explicit, never silently equated to
its strict version. The large family is estimated only after arithmetic
partition reconstruction, as a complete resolved family. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset Filter MeasureTheory Set Complex
namespace XiPrime8845.PRZZWindowSpatialJoin
open PRZZMellinSeparation PRZZRetainedNative PRZZLocalCentralTransfer PRZZDisjointSpatialJoin
set_option maxHeartbeats 8000000
attribute [local instance] Classical.propDecidable

theorem family_body (F G W : ℝ → ℂ) (js : List ℕ) (L N J : ℕ) (dual : Bool)
    (T Q V b eD eH t : ℝ) (A B : ℂ) :
    let mask := fun s z => (2:ℝ)^s ≤ T^b ∧ ¬PRZZSourceMaskFamily.discarded T Q eD s z
    let a := fun n => (PRZZGCoefficient.coefficient js n:ℂ)
    let alpha := A/(Real.log T:ℂ)
    let beta := B/(Real.log T:ℂ)
    PRZZResolvedTailMass.branch dual A B T t *
      PRZZAllPoissonRows.family L J N W (scaledCutoff F Q) (scaledCutoff G V) a alpha beta t =
      partField .central (PRZZWindowCentralAssembly.bodyCut T V eH) F G (PRZZWRowLimit.profile W)
        js L N dual T Q V b eD t A B+
      PRZZWindowCentralAssembly.subunit F G (PRZZWRowLimit.profile W)
        js L N dual T Q V b eD eH t A B-
      PRZZWindowCentralAssembly.transfer F G (PRZZWRowLimit.profile W)
        js L N dual T Q V b eD eH t A B+
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
  rw [PRZZDisjointSpatialJoin.family_local F G W js L N J dual T Q V b eD eH t A B,
    PRZZWindowCentralAssembly.central_decomposition]

/-- Exact boundary term between the closed local window and the strict
window used by the original moment collector. -/
theorem spatial_boundary {E : Type*} [AddCommMonoid E]
    (L : ℕ) (X : ℝ) (f : ℕ → E) :
    (∑ s ∈ (range (L+2)).filter (fun s => (2:ℝ)^s ≤ X), f s) =
    (∑ s ∈ (range (L+2)).filter (fun s => (2:ℝ)^s < X), f s)+
      ∑ s ∈ (range (L+2)).filter (fun s => (2:ℝ)^s = X), f s := by
  simp only [sum_filter,← sum_add_distrib]
  apply sum_congr rfl; intro s hs
  by_cases hl : (2:ℝ)^s < X
  · have he : (2:ℝ)^s ≠ X := ne_of_lt hl
    simp [hl,hl.le,he]
  · by_cases he : (2:ℝ)^s = X
    · simp [he]
    · have hh : ¬(2:ℝ)^s ≤ X := by intro hh; exact he (le_antisymm hh (le_of_not_gt hl))
      simp [hl,he,hh]

def closedLarge (L J N : ℕ) (F G H : ℝ → ℂ) (a : ℕ → ℂ)
    (X : ℝ) (alpha beta : ℂ) (t : ℝ) : ℂ :=
  PRZZResolvedComplement.masked L J N F G H a (fun s _ => X ≤ (2:ℝ)^s) alpha beta t

/-- The original strict-small convention pairs with closed-large. The
boundary is in one complete resolved family, not isolated central/tail norms. -/
theorem family_strict_split (L J N : ℕ) (F G H : ℝ → ℂ) (a : ℕ → ℂ)
    (X : ℝ) (alpha beta : ℂ) (t : ℝ) :
    PRZZAllPoissonRows.family L J N F G H a alpha beta t =
      PRZZSourceMaskFamily.selectedFamily L J N F G H a
        (fun s _ => (2:ℝ)^s < X) alpha beta t+
      closedLarge L J N F G H a X alpha beta t := by
  have hh := PRZZResolvedComplement.exhaustive L J N F G H a
    (fun s _ => (2:ℝ)^s < X) alpha beta t
  simpa only [not_lt,closedLarge,PRZZResolvedComplement.masked,
    PRZZSourceMaskFamily.selectedFamily] using hh

/-- Combine the evaluated local correction envelope with the complete
strict-large family, using the SAME polynomial threshold and actual time
cutoff. This is not a termwise bound on the large-M Fourier pieces. -/
theorem actual_join (P : ℝ → ℝ) (hm : Antitone P)
    (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ)))
    (Phi : ℝ → ℂ) (hPhi : Continuous Phi) (hcPhi : HasCompactSupport Phi)
    (js : List ℕ) (a b S r eD eH delta : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hS : 0 ≤ S) (hr : 0 < r)
    (heD : 0 ≤ eD) (he : eD < eH) (hexp : 7-2*b ≤ delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (L J N : ℕ) (dual : Bool) (A B : ℂ),
      1 ≤ N → (N:ℝ) ≤ T → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      PRZZWindowCentralAssembly.errorBudget (fun x => (P x:ℂ)) (fun x => (P x:ℂ))
        Phi js L N J dual T b eD eH A B+
      (∫ t in Icc T (2*T), ‖scaledCutoff Phi T t*
        (PRZZResolvedTailMass.branch dual A B T t *
          strictLarge L J N (fun x => (P x:ℂ)) (fun _ => 1) (fun _ => 1)
            (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) (T^b)
            (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t)‖) ≤
        C*T^delta*PRZZOptimalPowers.target N T := by
  have hPl : ∀ x ≤ (1/2:ℝ), (P x:ℂ) = 1 := by intro x hx; simp [hl x hx]
  have hPr : ∀ x, 1 ≤ x → (P x:ℂ) = 0 := by intro x hx; simp [hright x hx]
  obtain ⟨Ce,hCe,heval⟩ := PRZZWindowCentralAssembly.actual_partition _ _ Phi
    hP hPl hPr hP hPl hPr hPhi hcPhi js a b S r eD eH delta ha hb hS hr heD he
  obtain ⟨Cl,hCl,hlarge⟩ := actual_large_time P hm hlo hhi hl hright hP Phi hPhi hcPhi
    js S r b delta hS hr hexp
  refine ⟨Ce+Cl,by positivity,?_⟩
  filter_upwards [heval,hlarge] with T heval hlarge
  intro L J N dual A B hN hNT hA hB hsep
  exact (add_le_add (heval L N J dual A B hN hNT hA hB hsep)
    (hlarge L J N dual A B hN hNT hA hB hsep)).trans_eq (by ring)

theorem closed_large_time (P : ℝ → ℝ) (hm : Antitone P)
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
          closedLarge L J N (fun x => (P x:ℂ)) (fun _ => 1) (fun _ => 1)
            (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) (T^b)
            (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t)‖) ≤
        C*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := PRZZLargeResolvedPruning.masked_uniform P hm hlo hhi hl hright hP js S r hr
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
        closedLarge L J N (fun x => (P x:ℂ)) (fun _ => 1) (fun _ => 1)
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

/-- Strict-small moment windows pair with the evaluated CLOSED large
family. The common positive local envelope may include the endpoint;
the exact complex family split above still counts it only once. -/
theorem actual_join_strict (P : ℝ → ℝ) (hm : Antitone P)
    (hlo : ∀ x, 0 ≤ P x) (hhi : ∀ x, P x ≤ 1)
    (hl : ∀ x ≤ (1/2:ℝ), P x = 1) (hright : ∀ x, 1 ≤ x → P x = 0)
    (hP : ContDiff ℝ ∞ (fun x => (P x:ℂ)))
    (Phi : ℝ → ℂ) (hPhi : Continuous Phi) (hcPhi : HasCompactSupport Phi)
    (js : List ℕ) (a b S r eD eH delta : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hS : 0 ≤ S) (hr : 0 < r)
    (heD : 0 ≤ eD) (he : eD < eH) (hexp : 7-2*b ≤ delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (L J N : ℕ) (dual : Bool) (A B : ℂ),
      1 ≤ N → (N:ℝ) ≤ T → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      PRZZWindowCentralAssembly.errorBudget (fun x => (P x:ℂ)) (fun x => (P x:ℂ))
        Phi js L N J dual T b eD eH A B+
      (∫ t in Icc T (2*T), ‖scaledCutoff Phi T t*
        (PRZZResolvedTailMass.branch dual A B T t *
          closedLarge L J N (fun x => (P x:ℂ)) (fun _ => 1) (fun _ => 1)
            (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) (T^b)
            (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t)‖) ≤
        C*T^delta*PRZZOptimalPowers.target N T := by
  have hPl : ∀ x ≤ (1/2:ℝ), (P x:ℂ) = 1 := by intro x hx; simp [hl x hx]
  have hPr : ∀ x, 1 ≤ x → (P x:ℂ) = 0 := by intro x hx; simp [hright x hx]
  obtain ⟨Ce,hCe,heval⟩ := PRZZWindowCentralAssembly.actual_partition _ _ Phi
    hP hPl hPr hP hPl hPr hPhi hcPhi js a b S r eD eH delta ha hb hS hr heD he
  obtain ⟨Cl,hCl,hlarge⟩ := closed_large_time P hm hlo hhi hl hright hP Phi hPhi hcPhi
    js S r b delta hS hr hexp
  refine ⟨Ce+Cl,by positivity,?_⟩
  filter_upwards [heval,hlarge] with T heval hlarge
  intro L J N dual A B hN hNT hA hB hsep
  exact (add_le_add (heval L N J dual A B hN hNT hA hB hsep)
    (hlarge L J N dual A B hN hNT hA hB hsep)).trans_eq (by ring)

#print axioms closed_large_time
#print axioms actual_join_strict
#print axioms family_body
#print axioms spatial_boundary
#print axioms family_strict_split
#print axioms actual_join
end XiPrime8845.PRZZWindowSpatialJoin

