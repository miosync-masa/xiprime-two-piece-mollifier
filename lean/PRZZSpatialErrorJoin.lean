import PRZZFullFreezeBudget
import PRZZLargeResolvedPruning

/-! Exact selected window-boundary removal and a common scalar budget
for the actual full active freezing mass and collective large-M family.
Large-M components are not bounded separately. This is not an asserted
identification of the complete AFE remainder with these displayed terms. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset Filter MeasureTheory Complex
namespace XiPrime8845.PRZZSpatialErrorJoin
open PRZZMellinSeparation PRZZNativeComponents
set_option maxHeartbeats 8000000
attribute [local instance] Classical.propDecidable

def boundary (L J N : ℕ) (F G H : ℝ → ℂ) (a : ℕ → ℂ)
    (R : ℕ → PRZZAFEIndices.Label → Prop) (T b t : ℝ) (alpha beta : ℂ) : ℂ :=
  ∑ s ∈ PRZZWindowGrids.spatial L T b, ∑ d ∈ Icc 1 N, ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N,
    if PRZZDiagonalAssembly.admissible N d u v then
      ∑ delta ∈ PRZZNativeFamily.gaps L N (d*u) (d*v),
        if delta ≠ 0 ∧ R s (PRZZNativeFamily.pairLabel (d*u) (d*v) delta) then
          row .boundary L J F G H ((2:ℝ)^s) ((u,v),(-delta,1)) alpha beta a d t else 0 else 0

theorem boundary_zero (L J N : ℕ) (F G H : ℝ → ℂ) (a : ℕ → ℂ)
    (R : ℕ → PRZZAFEIndices.Label → Prop) (T b t : ℝ) (alpha beta : ℂ)
    (hN : 1 ≤ N) (hsF : Function.support F ⊆ Set.Icc (1/2:ℝ) 3)
    (hL : 4*(N:ℝ)*T^b ≤ L) :
    boundary L J N F G H a R T b t alpha beta = 0 := by
  unfold boundary
  apply sum_eq_zero; intro s hs
  apply sum_eq_zero; intro d hd
  apply sum_eq_zero; intro u hu
  apply sum_eq_zero; intro v hv
  split_ifs
  · apply sum_eq_zero; intro delta hdel
    split_ifs
    · unfold row
      dsimp only
      split_ifs with hsmall
      · have hz := PRZZResolvedBoundary.bounded_cover_zero L N (T^b) ((2:ℝ)^s) t F
          ((u,v),(-delta,1)) alpha beta (alpha+beta)
          (by exact_mod_cast hN) (by positivity) (mem_filter.mp hs).2
          (mem_Icc.mp hu).1 (mem_Icc.mp hu).2 (mem_Icc.mp hv).1 hsF hsmall hL
        simp only [hz,mul_zero]
      · rfl
    · rfl
  · rfl

theorem boundary_time_zero (L J N : ℕ) (F G H : ℝ → ℂ) (a : ℕ → ℂ)
    (R : ℕ → PRZZAFEIndices.Label → Prop) (T b : ℝ) (alpha beta : ℂ) (phi : ℝ → ℂ)
    (hN : 1 ≤ N) (hsF : Function.support F ⊆ Set.Icc (1/2:ℝ) 3)
    (hL : 4*(N:ℝ)*T^b ≤ L) :
    (∫ t in Set.Icc T (2*T), phi t*boundary L J N F G H a R T b t alpha beta) = 0 := by
  simp_rw [boundary_zero L J N F G H a R T b _ alpha beta hN hsF hL,mul_zero]
  simp

def large (S : ℝ → ℝ) (js : List ℕ) (L J N : ℕ) (dual : Bool)
    (T : ℝ) (A B : ℂ) (phi : ℝ → ℂ) : ℂ :=
  ∫ t in Set.Icc T (2*T), (phi t*PRZZResolvedTailMass.branch dual A B T t)*
    PRZZResolvedComplement.masked L J N (fun x => (S x:ℂ)) (fun _ => 1) (fun _ => 1)
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) (fun s _ => T^(4:ℝ) ≤ (2:ℝ)^s)
      (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) t

theorem large_time (S : ℝ → ℝ) (hm : Antitone S)
    (hlo : ∀ x, 0 ≤ S x) (hhi : ∀ x, S x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), S x = 1) (hright : ∀ x, 1 ≤ x → S x = 0)
    (hS : ContDiff ℝ ∞ (fun x => (S x:ℂ)))
    (js : List ℕ) (Z r : ℝ) (hZ : 0 ≤ Z) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (L J N : ℕ) (dual : Bool)
      (A B : ℂ) (phi : ℝ → ℂ),
      1 ≤ N → (N:ℝ) ≤ T → ‖A‖ ≤ Z → ‖B‖ ≤ Z → r ≤ ‖A+B‖ → Continuous phi →
      ‖large S js L J N dual T A B phi‖ ≤ C*T^(-2:ℝ)*(∫ t in Set.Icc T (2*T), ‖phi t‖) := by
  obtain ⟨C,hC,h⟩ := PRZZLargeResolvedPruning.large_time S hm hlo hhi hleft hright hS js Z r 2 hr
  obtain ⟨D,hD,hd⟩ := PRZZLargeResolvedPruning.dual_large_time S hm hlo hhi hleft hright hS js Z r 2 hZ hr
  refine ⟨C+D,by positivity,?_⟩
  filter_upwards [h,hd] with T h hd
  intro L J N dual A B phi hN hNT hA hB hsep hphi
  have hT0 : 0 < T := lt_of_lt_of_le (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)) hNT
  have hn : 0 ≤ T^(-2:ℝ)*(∫ t in Set.Icc T (2*T), ‖phi t‖) :=
    mul_nonneg (Real.rpow_nonneg hT0.le _) (integral_nonneg (fun t => norm_nonneg _))
  cases dual with
  | false =>
    have hh := h L J N A B phi hN hNT hA hB hsep hphi
    norm_num only [show ((2:ℝ)+6)/2 = 4 by norm_num] at hh
    have hh' : ‖large S js L J N false T A B phi‖ ≤ C*T^(-2:ℝ)*(∫ t in Set.Icc T (2*T), ‖phi t‖) := by
      simpa only [large,PRZZResolvedTailMass.branch,Bool.false_eq_true,if_false,mul_one] using hh
    nlinarith [mul_nonneg hD.le hn]
  | true =>
    have hsep' : r ≤ ‖-B+-A‖ := by simpa only [show -B+-A = -(A+B) by ring,norm_neg] using hsep
    have hh := hd L J N (-B) (-A) phi hN hNT (by simpa only [norm_neg] using hB)
      (by simpa only [norm_neg] using hA) hsep' hphi
    norm_num only [show ((2:ℝ)+6)/2 = 4 by norm_num,neg_neg] at hh
    change ‖large S js L J N true T A B phi‖ ≤ D*T^(-2:ℝ)*(∫ t in Set.Icc T (2*T), ‖phi t‖) at hh
    nlinarith [mul_nonneg hC.le hn]

/-- Common budget for displayed actual terms on the first AFE branch.
The reflected large-M estimate is separately available in large_time.
This does not silently identify an arbitrary selected freezing sum with
the complete active envelope fullMass. -/
theorem common_budget (S : ℝ → ℝ) (hm : Antitone S)
    (hlo : ∀ x, 0 ≤ S x) (hhi : ∀ x, S x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), S x = 1) (hright : ∀ x, 1 ≤ x → S x = 0)
    (hS : ContDiff ℝ ∞ (fun x => (S x:ℂ)))
    (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G)
    (hsF : Function.support F ⊆ Set.Icc (1/2:ℝ) 3)
    (hsG : Function.support G ⊆ Set.Icc (1/2:ℝ) 3)
    (js : List ℕ) (a Z r eps eH eta delta : ℝ)
    (ha : 0 < a) (hZ : 0 ≤ Z) (hr : 0 < r) (heps : 0 ≤ eps) (heps1 : eps < 1)
    (he : eps < eH) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hmargin : 6*eps+2*eta < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (L J N K : ℕ) (A B : ℂ) (phi : ℝ → ℂ) (P : ℝ),
      1 ≤ N → (N:ℝ) ≤ T^(4/7:ℝ) → 4*(N:ℝ)*T^(4:ℝ) ≤ L →
      ‖A‖ ≤ Z → ‖B‖ ≤ Z → r ≤ ‖A+B‖ → Continuous phi → 0 ≤ P →
      (∀ t ∈ Set.Icc T (2*T), ‖phi t‖ ≤ P) →
      let W := PRZZWRowLimit.profile (fun x => (S x:ℂ))
      (∑ p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2),
        ∫ t in Set.Icc T (2*T), ‖phi t*PRZZLocalTailBudget.field F G W js L N false T
          ((2:ℝ)^p.1) ((2:ℝ)^p.2) 4 eps eH t A B‖)+
      (∑ p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2),
        PRZZFullFreezeBudget.fullMass L J W phi js N K T 1 ((2:ℝ)^p.1) ((2:ℝ)^p.2) eps eH F G
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) ((A+B)/(Real.log T:ℂ)))+
      ‖large S js L J N false T A B phi‖+
      ‖∫ t in Set.Icc T (2*T), phi t*PRZZWindowBoundary.part .boundary L J N W
        (fun _ => 1) (fun _ => 1) (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) T 4 t
          (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))‖ ≤ C*P*T^delta*PRZZOptimalPowers.target N T := by
  have hl (x : ℝ) (hx : x ≤ (1/2:ℝ)) : (S x:ℂ) = 1 := by simp [hleft x hx]
  have hr' (x : ℝ) (hx : 1 ≤ x) : (S x:ℂ) = 0 := by simp [hright x hx]
  have hw := PRZZWRowLimit.profile_regular (fun x => (S x:ℂ)) hS hl hr'
  obtain ⟨Ct,hCt,htail⟩ := PRZZLocalTailBudget.partition_time F G _ hF hG hcF hcG hsF hw.1 hw.2.2
    js a 4 Z r eps eH delta 1 ha (by norm_num) hZ hr heps he (by norm_num)
  obtain ⟨Cf,hCf,hfreeze⟩ := PRZZFullFreezeBudget.partition_bound _ F G hw.1 hw.2.1 hw.2.2
    hF hG hcF hcG hsF hsG js Z r eps eta delta hZ hr heps heta heta1 hmargin
  obtain ⟨Cl,hCl,hlarge⟩ := large_time S hm hlo hhi hleft hright hS js Z r hZ hr
  refine ⟨Ct+Cf+Cl,by positivity,?_⟩
  filter_upwards [htail,hlarge,PRZZRejectedExhaustion.height_eventually eps heps1,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 (2*Z/eta))),
    eventually_ge_atTop (1:ℝ)] with T ht hlrg hh hlog hT
  intro L J N K A B phi P hN hscale hL hA hB hsep hphi hP hp
  dsimp only
  have hNT : (N:ℝ) ≤ T := hscale.trans (by
    simpa using Real.rpow_le_rpow_of_exponent_le hT (by norm_num : (4/7:ℝ) ≤ 1))
  have hmass := PRZZActualPoissonError.phi_mass T P (by linarith) phi hp
  have h1 := ht L N false P A B phi hN hNT hP hA hB hsep hphi hmass
  have h2 := hfreeze L J N K T 1 eH A B phi P hA hB hsep hN hT
    ((le_max_left _ _).trans hlog) ((le_max_right _ _).trans hlog) hscale hh.2
    (by norm_num) hphi hP hp
  have h3 := hlrg L J N false A B phi hN hNT hA hB hsep hphi
  have hd : 0 < delta := by nlinarith
  have htarget : 1 ≤ PRZZOptimalPowers.target N T := by
    unfold PRZZOptimalPowers.target
    exact (Real.one_le_rpow (by exact_mod_cast hN : (1:ℝ) ≤ N) (by norm_num : (0:ℝ) ≤ 7/4)).trans
      (le_add_of_nonneg_right (by positivity))
  have h3' : ‖large S js L J N false T A B phi‖ ≤ Cl*P*T^delta*PRZZOptimalPowers.target N T := by
    calc
      _ ≤ Cl*T^(-2:ℝ)*(P*T) := h3.trans (mul_le_mul_of_nonneg_left hmass (by positivity))
      _ = Cl*P*T^(-1:ℝ) := by
        rw [show Cl*T^(-2:ℝ)*(P*T) = Cl*P*(T^(-2:ℝ)*T^((1:ℝ))) by simp only [Real.rpow_one]; ring]
        rw [← Real.rpow_add hh.1]; norm_num
      _ ≤ Cl*P*T^delta := by gcongr; linarith
      _ ≤ _ := le_mul_of_one_le_right (by positivity) htarget
  rw [PRZZWindowBoundary.boundary_integral_zero L J N _ _ _ _ T 4 _ _ phi hN hw.2.2 hL,norm_zero,add_zero]
  nlinarith only [h1,h2,h3']

#print axioms common_budget
#print axioms boundary_zero
#print axioms boundary_time_zero
#print axioms large_time
end XiPrime8845.PRZZSpatialErrorJoin
