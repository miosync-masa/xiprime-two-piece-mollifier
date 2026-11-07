import PRZZSelectedLocalFourier
import PRZZDyadicBudget

/-! The actual selected local Fourier tail on the polynomial spatial
window is dominated by nativeMass. Strict source masks are embedded in
the closed mass envelope without changing their original endpoint. The
large-M complement is not silently included in this assertion. -/
noncomputable section
open scoped BigOperators ContDiff
open Finset Filter MeasureTheory
namespace XiPrime8845.PRZZLocalTailBudget
open PRZZSelectedLocalFourier PRZZMellinSeparation
set_option maxHeartbeats 8000000
attribute [local instance] Classical.propDecidable

def field (F G W : ℝ → ℂ) (js : List ℕ) (L N : ℕ) (dual : Bool)
    (T Q V b eD eH t : ℝ) (A B : ℂ) : ℂ :=
  ∑ s ∈ PRZZWindowGrids.spatial L T b, ∑ d ∈ Icc 1 N,
    ∑ u ∈ Icc 1 N, ∑ v ∈ Icc 1 N,
      if PRZZDiagonalAssembly.admissible N d u v then
        ∑ delta ∈ PRZZNativeFamily.gaps L N (d*u) (d*v),
          if delta ≠ 0 ∧ ¬PRZZSourceMaskFamily.discarded T Q eD s
              (PRZZNativeFamily.pairLabel (d*u) (d*v) delta) then
            PRZZResolvedTailMass.branch dual A B T t *
              PRZZNativeComponents.row .tail L (sourceCutoff T eH s d u v delta) W
                (scaledCutoff F Q) (scaledCutoff G V) ((2:ℝ)^s) ((u,v),(-delta,1))
                (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))
                (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) d t
          else 0 else 0

theorem native_dominates (F G W : ℝ → ℂ) (js : List ℕ) (L N : ℕ) (dual : Bool)
    (T Q V b eD eH t : ℝ) (A B : ℂ) :
    ‖field F G W js L N dual T Q V b eD eH t A B‖ ≤
      PRZZWindowNativeTail.nativeMass F G W js L N dual T Q V b eD eH t A B := by
  rw [← PRZZWindowNativeTail.flat_eq]
  unfold field PRZZWindowNativeTail.flatMass
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro s hs
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro d hd
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro u hu
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro v hv
  by_cases had : PRZZDiagonalAssembly.admissible N d u v
  · have had' : u.Coprime v ∧ d*u ≤ N ∧ d*v ≤ N := had
    simp only [if_pos had,if_pos had']
    apply (norm_sum_le _ _).trans
    apply sum_le_sum; intro delta hdel
    by_cases hr : delta ≠ 0 ∧ ¬PRZZSourceMaskFamily.discarded T Q eD s
        (PRZZNativeFamily.pairLabel (d*u) (d*v) delta)
    · rw [if_pos hr,source_tail]
      have hg : Nat.gcd (d*u) (d*v) = d := by rw [Nat.gcd_mul_left,had.1.gcd_eq_one,mul_one]
      have hd0 : (0:ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
      have hf : |((-delta:ℤ):ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eD/d := by
        have hh := hr.2
        simp only [PRZZSourceMaskFamily.discarded,PRZZNativeFamily.pairLabel,hg,not_le] at hh
        simp only [Int.cast_neg,abs_neg]
        exact ((lt_div_iff₀ hd0).mpr (by simpa only [mul_comm] using hh)).le
      simp only [Int.cast_neg,abs_neg] at hf
      by_cases hsmall : |(delta:ℝ)| ≤ (2:ℝ)^s*u/4
      · have hsmall' : |((-delta:ℤ):ℝ)| ≤ (2:ℝ)^s*u/4 := by simpa only [Int.cast_neg,abs_neg] using hsmall
        have hcond : delta ≠ 0 ∧ |((-delta:ℤ):ℝ)| ≤ (2:ℝ)^s*u/4 ∧
            |((-delta:ℤ):ℝ)| ≤ PRZZSourceCutoffs.deltaCutoff T ((2:ℝ)^s) Q eD/d :=
          ⟨hr.1,hsmall',by simpa only [Int.cast_neg,abs_neg] using hf⟩
        rw [if_pos hcond,if_pos hsmall']
        simp only [PRZZResolvedTailMass.coeff,mul_assoc,le_refl]
      · simp only [Int.cast_neg,abs_neg,hsmall,and_false,false_and,if_false,mul_zero,norm_zero,le_refl]
    · rw [if_neg hr,norm_zero]
      split_ifs <;> positivity
  · have had' : ¬(u.Coprime v ∧ d*u ≤ N ∧ d*v ≤ N) := had
    simp only [if_neg had,if_neg had',norm_zero,le_refl]

/-- Constants precede every arithmetic scale, truncation, and branch. -/
theorem uniform (F G W : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G)
    (hsF : Function.support F ⊆ Set.Icc (1/2:ℝ) 3)
    (hW : ContDiff ℝ ∞ W) (hsW : Function.support W ⊆ Set.Icc (1/2:ℝ) 3)
    (js : List ℕ) (a b S r eD eH power : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hS : 0 ≤ S) (hr : 0 < r)
    (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (L N : ℕ) (dual : Bool) (Q V t : ℝ) (A B : ℂ),
      1 ≤ N → (N:ℝ) ≤ T → 0 < Q → t ∈ Set.Icc T (2*T) →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      ‖field F G W js L N dual T Q V b eD eH t A B‖ ≤ C*T^(-power) := by
  obtain ⟨C,hC,h⟩ := PRZZWindowTailTime.uniform F G W hF hG hcF hcG hsF hW hsW
    js a b S r eD eH power ha hb hS hr heD he
  refine ⟨C,hC,?_⟩
  filter_upwards [h,eventually_ge_atTop (1:ℝ)] with T h hT
  intro L N dual Q V t A B hN hNT hQ ht hA hB hsep
  apply (native_dominates F G W js L N dual T Q V b eD eH t A B).trans
  rw [PRZZWindowNativeTail.native_eq_all F G W js L N dual T Q V b eD eH t A B hT hNT hQ hsF]
  exact h L N dual Q V t A B hN hNT hQ ht hA hB hsep

theorem time (F G W : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G)
    (hsF : Function.support F ⊆ Set.Icc (1/2:ℝ) 3)
    (hW : ContDiff ℝ ∞ W) (hsW : Function.support W ⊆ Set.Icc (1/2:ℝ) 3)
    (js : List ℕ) (a b S r eD eH delta : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hS : 0 ≤ S) (hr : 0 < r)
    (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (L N : ℕ) (dual : Bool) (Q V P : ℝ) (A B : ℂ) (phi : ℝ → ℂ),
      1 ≤ N → (N:ℝ) ≤ T → 0 < Q → 0 ≤ P → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      Continuous phi → (∫ t in Set.Icc T (2*T), ‖phi t‖) ≤ P*T →
      (∫ t in Set.Icc T (2*T), ‖phi t*field F G W js L N dual T Q V b eD eH t A B‖) ≤
        C*P*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := uniform F G W hF hG hcF hcG hsF hW hsW js a b S r eD eH
    (1-delta) ha hb hS hr heD he
  refine ⟨C,hC,?_⟩
  filter_upwards [h,eventually_ge_atTop (1:ℝ)] with T h hT
  intro L N dual Q V P A B phi hN hNT hQ hP hA hB hsep hphi hmass
  have hT0 : 0 < T := by linarith
  have hi : IntegrableOn (fun t => C*T^(-(1-delta))*‖phi t‖) (Set.Icc T (2*T)) :=
    (continuous_const.mul hphi.norm).integrableOn_Icc
  have hh : (∫ t in Set.Icc T (2*T), ‖phi t*field F G W js L N dual T Q V b eD eH t A B‖) ≤
      C*T^(-(1-delta))*(∫ t in Set.Icc T (2*T), ‖phi t‖) := by
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg (Eventually.of_forall (fun t => norm_nonneg _)) hi
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (h L N dual Q V t A B hN hNT hQ ht hA hB hsep)
      (norm_nonneg _)).trans_eq (by ring)
  have htarg : 1 ≤ PRZZOptimalPowers.target N T := by
    unfold PRZZOptimalPowers.target
    exact (Real.one_le_rpow (by exact_mod_cast hN : (1:ℝ) ≤ N) (by norm_num : (0:ℝ) ≤ 7/4)).trans
      (le_add_of_nonneg_right (by positivity))
  calc
    _ ≤ C*T^(-(1-delta))*(P*T) := hh.trans (mul_le_mul_of_nonneg_left hmass (by positivity))
    _ = C*P*T^delta := by
      rw [show -(1-delta) = delta-1 by ring,Real.rpow_sub hT0,Real.rpow_one]
      field_simp
    _ ≤ _ := le_mul_of_one_le_right (by positivity) htarg

/-- The actual arithmetic profile grid has log_2 N+2, not log_2 N+1,
scales. Its square costs only the explicitly spent gamma slack. -/
theorem arithmetic_grid_absorbed (gamma : ℝ) (hg : 0 < gamma) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ T : ℝ,
      (N:ℝ) ≤ T → 1 ≤ Real.log T →
      ((range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2)).card:ℝ) ≤ C*T^gamma := by
  obtain ⟨C,hC,h⟩ := PRZZDyadicBudget.grids_absorbed 2 gamma hg
  refine ⟨4*C,by positivity,?_⟩
  intro N hN T hNT hlog
  have hh := h N hN T hNT hlog 2 le_rfl
  have hz : (0:ℝ) ≤ Nat.log 2 N := by positivity
  simp only [card_product,card_range,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
  nlinarith

/-- Sum every arithmetic cutoff window with one height-uniform constant.
The full local-tail absolute mass, rather than a supplied coefficient
budget, is charged to the common PRZZ target. -/
theorem partition_time (F G W : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G)
    (hsF : Function.support F ⊆ Set.Icc (1/2:ℝ) 3)
    (hW : ContDiff ℝ ∞ W) (hsW : Function.support W ⊆ Set.Icc (1/2:ℝ) 3)
    (js : List ℕ) (a b S r eD eH delta gamma : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hS : 0 ≤ S) (hr : 0 < r)
    (heD : 0 ≤ eD) (he : eD < eH) (hg : 0 < gamma) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (L N : ℕ) (dual : Bool) (P : ℝ) (A B : ℂ) (phi : ℝ → ℂ),
      1 ≤ N → (N:ℝ) ≤ T → 0 ≤ P → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      Continuous phi → (∫ t in Set.Icc T (2*T), ‖phi t‖) ≤ P*T →
      (∑ p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2),
        ∫ t in Set.Icc T (2*T), ‖phi t*field F G W js L N dual T ((2:ℝ)^p.1)
          ((2:ℝ)^p.2) b eD eH t A B‖) ≤ C*P*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := time F G W hF hG hcF hcG hsF hW hsW js a b S r eD eH
    (delta-gamma) ha hb hS hr heD he
  obtain ⟨D,hD,hgrid⟩ := arithmetic_grid_absorbed gamma hg
  refine ⟨D*C,by positivity,?_⟩
  filter_upwards [h,Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    eventually_ge_atTop (1:ℝ)] with T h hlog hT
  intro L N dual P A B phi hN hNT hP hA hB hsep hphi hmass
  have hT0 : 0 < T := by linarith
  calc
    _ ≤ ∑ _p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2),
        C*P*T^(delta-gamma)*PRZZOptimalPowers.target N T := by
      apply sum_le_sum; intro p hp
      exact h L N dual _ _ P A B phi hN hNT (by positivity) hP hA hB hsep hphi hmass
    _ = ((range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2)).card:ℝ)*
        (C*P*T^(delta-gamma)*PRZZOptimalPowers.target N T) := by simp only [sum_const,nsmul_eq_mul]
    _ ≤ (D*T^gamma)*(C*P*T^(delta-gamma)*PRZZOptimalPowers.target N T) := by
      apply mul_le_mul_of_nonneg_right (hgrid N hN T hNT hlog)
      unfold PRZZOptimalPowers.target; positivity
    _ = _ := by
      rw [show delta = gamma+(delta-gamma) by ring,Real.rpow_add hT0]
      ring

/-- Actual partition profiles and the actual scaled time cutoff, with
their regularity and time L1 mass supplied. No coefficient mass, tail
bound, or externally supplied time integral is a premise. -/
theorem actual_partition (P F Phi : ℝ → ℂ)
    (hP : ContDiff ℝ ∞ P) (hPl : ∀ x ≤ (1/2:ℝ), P x = 1)
    (hPr : ∀ x, 1 ≤ x → P x = 0)
    (hF : ContDiff ℝ ∞ F) (hFl : ∀ x ≤ (1/2:ℝ), F x = 1)
    (hFr : ∀ x, 1 ≤ x → F x = 0)
    (hPhi : Continuous Phi) (hcPhi : HasCompactSupport Phi)
    (js : List ℕ) (a b S r eD eH delta : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hS : 0 ≤ S) (hr : 0 < r)
    (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (L N : ℕ) (dual : Bool) (A B : ℂ),
      1 ≤ N → (N:ℝ) ≤ T → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      (∑ p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2),
        ∫ t in Set.Icc T (2*T), ‖scaledCutoff Phi T t*
          field (PRZZWRowLimit.profile P) (PRZZWRowLimit.profile P) (PRZZWRowLimit.profile F)
            js L N dual T ((2:ℝ)^p.1) ((2:ℝ)^p.2) b eD eH t A B‖) ≤
        C*T^delta*PRZZOptimalPowers.target N T := by
  have hp := PRZZWRowLimit.profile_regular P hP hPl hPr
  have hf := PRZZWRowLimit.profile_regular F hF hFl hFr
  obtain ⟨C,hC,h⟩ := partition_time _ _ _ hp.1.continuous hp.1.continuous hp.2.1 hp.2.1 hp.2.2
    hf.1 hf.2.2 js a b S r eD eH delta 1 ha hb hS hr heD he (by norm_num)
  obtain ⟨P0,hP0,hcut⟩ := PRZZWindowErrorJoin.cutoff_mass Phi hPhi hcPhi
  refine ⟨C*P0,by positivity,?_⟩
  filter_upwards [h,eventually_gt_atTop (0:ℝ)] with T h hT
  intro L N dual A B hN hNT hA hB hsep
  have hh := h L N dual P0 A B (scaledCutoff Phi T) hN hNT hP0.le hA hB hsep
    (hPhi.comp (continuous_const.mul continuous_id)) (hcut T hT).2
  simpa only [mul_assoc] using hh

#print axioms native_dominates
#print axioms uniform
#print axioms time
#print axioms arithmetic_grid_absorbed
#print axioms partition_time
#print axioms actual_partition
end XiPrime8845.PRZZLocalTailBudget
