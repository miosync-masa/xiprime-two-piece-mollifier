import PRZZBodyTailMass

/-! Time and full arithmetic-grid aggregation of the literal body-cut
absolute tail mass. All three previously evaluated corrections are used;
there is no new analytic coefficient-mass or tail-bound premise. -/
noncomputable section
open scoped BigOperators ContDiff Topology
open Complex Finset Set Filter MeasureTheory
namespace XiPrime8845.PRZZBodyTailTime
open PRZZBodyTailMass PRZZMellinSeparation
set_option maxHeartbeats 10000000

theorem time (F G W : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hsG : Function.support G ⊆ Icc (1/2:ℝ) 3)
    (hW : ContDiff ℝ ∞ W) (hsW : Function.support W ⊆ Icc (1/2:ℝ) 3)
    (js : List ℕ) (a b S r eD eH power : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hS : 0 ≤ S) (hr : 0 < r)
    (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (L N : ℕ) (dual : Bool) (Q V : ℝ) (A B : ℂ) (phi : ℝ → ℂ),
      1 ≤ N → (N:ℝ) ≤ T → 0 < Q → 0 < V →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ → Continuous phi →
      (∫ t in Icc T (2*T), ‖phi t‖*mass F G W js L N dual T Q V b eD eH t A B) ≤
        C*T^(-power)*(∫ t in Icc T (2*T), ‖phi t‖) := by
  obtain ⟨C,hC,h⟩ := uniform F G W hF hG hcF hcG hsF hsG hW hsW
    js a b S r eD eH power ha hb hS hr heD he
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with T h
  intro L N dual Q V A B phi hN hNT hQ hV hA hB hsep hphi
  have hi : IntegrableOn (fun t => C*T^(-power)*‖phi t‖) (Icc T (2*T)) :=
    (continuous_const.mul hphi.norm).integrableOn_Icc
  apply (integral_mono_of_nonneg
    (Eventually.of_forall (fun t => mul_nonneg (norm_nonneg _) (mass_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))) hi ?_).trans_eq
  · rw [integral_const_mul]
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (mul_le_mul_of_nonneg_left (h L N dual Q V t A B hN hNT hQ hV ht hA hB hsep)
      (norm_nonneg _)).trans_eq (by ring)

theorem grid_time (F G W : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hsG : Function.support G ⊆ Icc (1/2:ℝ) 3)
    (hW : ContDiff ℝ ∞ W) (hsW : Function.support W ⊆ Icc (1/2:ℝ) 3)
    (js : List ℕ) (a b S r eD eH power : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hS : 0 ≤ S) (hr : 0 < r)
    (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (L N : ℕ) (dual : Bool) (A B : ℂ) (phi : ℝ → ℂ),
      1 ≤ N → (N:ℝ) ≤ T → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ → Continuous phi →
      (∑ p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2),
        ∫ t in Icc T (2*T), ‖phi t‖*mass F G W js L N dual T ((2:ℝ)^p.1)
          ((2:ℝ)^p.2) b eD eH t A B) ≤
        C*T^(-power)*(∫ t in Icc T (2*T), ‖phi t‖) := by
  obtain ⟨C,hC,h⟩ := time F G W hF hG hcF hcG hsF hsG hW hsW
    js a b S r eD eH (power+1) ha hb hS hr heD he
  obtain ⟨D,hD,hgrid⟩ := PRZZLocalTailBudget.arithmetic_grid_absorbed 1 (by norm_num)
  refine ⟨D*C,by positivity,?_⟩
  filter_upwards [h,eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with T h hT hlog
  intro L N dual A B phi hN hNT hA hB hsep hphi
  have hT0 : 0 < T := by linarith
  calc
    _ ≤ ∑ _p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2),
        C*T^(-(power+1))*(∫ t in Icc T (2*T), ‖phi t‖) := by
      apply sum_le_sum; intro p hp
      exact h L N dual ((2:ℝ)^p.1) ((2:ℝ)^p.2) A B phi hN hNT
        (by positivity) (by positivity) hA hB hsep hphi
    _ = ((range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2)).card:ℝ)*
        (C*T^(-(power+1))*(∫ t in Icc T (2*T), ‖phi t‖)) := by
      simp only [sum_const,nsmul_eq_mul]
    _ ≤ (D*T)*(C*T^(-(power+1))*(∫ t in Icc T (2*T), ‖phi t‖)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa only [Real.rpow_one] using hgrid N hN T hNT hlog
    _ = _ := by
      rw [show (D*T)*(C*T^(-(power+1))*(∫ t in Icc T (2*T), ‖phi t‖)) =
        (D*C)*(T^(1:ℝ)*T^(-(power+1)))*(∫ t in Icc T (2*T), ‖phi t‖) by rw [Real.rpow_one]; ring]
      rw [← Real.rpow_add hT0,show (1:ℝ)+-(power+1) = -power by ring]

theorem actual_partition (P F Phi : ℝ → ℂ)
    (hP : ContDiff ℝ ∞ P) (hPl : ∀ x ≤ (1/2:ℝ), P x = 1)
    (hPr : ∀ x, 1 ≤ x → P x = 0)
    (hF : ContDiff ℝ ∞ F) (hFl : ∀ x ≤ (1/2:ℝ), F x = 1)
    (hFr : ∀ x, 1 ≤ x → F x = 0)
    (hPhi : Continuous Phi) (hcPhi : HasCompactSupport Phi)
    (js : List ℕ) (a b S r eD eH delta : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hS : 0 ≤ S) (hr : 0 < r)
    (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (L N : ℕ) (dual : Bool) (A B : ℂ),
      1 ≤ N → (N:ℝ) ≤ T → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      (∑ p ∈ range (Nat.log 2 N+2) ×ˢ range (Nat.log 2 N+2),
        ∫ t in Icc T (2*T), ‖scaledCutoff Phi T t‖*
          mass (PRZZWRowLimit.profile P) (PRZZWRowLimit.profile P) (PRZZWRowLimit.profile F)
            js L N dual T ((2:ℝ)^p.1) ((2:ℝ)^p.2) b eD eH t A B) ≤
        C*T^delta*PRZZOptimalPowers.target N T := by
  have hp := PRZZWRowLimit.profile_regular P hP hPl hPr
  have hf := PRZZWRowLimit.profile_regular F hF hFl hFr
  obtain ⟨C,hC,h⟩ := grid_time _ _ _ hp.1.continuous hp.1.continuous hp.2.1 hp.2.1 hp.2.2 hp.2.2
    hf.1 hf.2.2 js a b S r eD eH (1-delta) ha hb hS hr heD he
  obtain ⟨P0,hP0,hcut⟩ := PRZZWindowErrorJoin.cutoff_mass Phi hPhi hcPhi
  refine ⟨C*P0,by positivity,?_⟩
  filter_upwards [h,eventually_gt_atTop (0:ℝ)] with T h hT
  intro L N dual A B hN hNT hA hB hsep
  have hh := h L N dual A B (scaledCutoff Phi T) hN hNT hA hB hsep
    (hPhi.comp (continuous_const.mul continuous_id))
  have htarg : 1 ≤ PRZZOptimalPowers.target N T := by
    unfold PRZZOptimalPowers.target
    exact (Real.one_le_rpow (by exact_mod_cast hN : (1:ℝ) ≤ N) (by norm_num : (0:ℝ) ≤ 7/4)).trans
      (le_add_of_nonneg_right (by positivity))
  calc
    _ ≤ C*T^(-(1-delta))*(P0*T) := hh.trans (mul_le_mul_of_nonneg_left (hcut T hT).2 (by positivity))
    _ = C*P0*T^delta := by
      have he : T^(-(1-delta))*T = T^delta := by
        calc
          _ = T^(-(1-delta))*T^(1:ℝ) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_add hT]; congr 1; ring
      calc
        _ = C*P0*(T^(-(1-delta))*T) := by ring
        _ = _ := by rw [he]
    _ ≤ _ := le_mul_of_one_le_right (by positivity) htarg

#print axioms time
#print axioms grid_time
#print axioms actual_partition
end XiPrime8845.PRZZBodyTailTime
