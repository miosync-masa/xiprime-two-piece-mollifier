import PRZZWindowTailMass
import PRZZOptimalPowers

/-! Supply the actual scaled-cutoff support and remove the artificial
upper cutoff scale: if Q>2T, every original arithmetic coefficient is zero.
Then integrate the full outer absolute mass in time. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Finset Set Filter MeasureTheory
namespace XiPrime8845.PRZZWindowTailTime
open PRZZWindowTailMass PRZZWindowGrids PRZZMellinSeparation
set_option maxHeartbeats 5000000
attribute [local instance] Classical.propDecidable

theorem scaled_support (F : ℝ → ℂ) (Q : ℝ) (hQ : 0 < Q)
    (hs : Function.support F ⊆ Icc (1/2:ℝ) 3) :
    Function.support (scaledCutoff F Q) ⊆ Icc (Q/2) (3*Q) := by
  intro x hx
  have hh := hs hx
  change (1/2:ℝ) ≤ Q⁻¹*x ∧ Q⁻¹*x ≤ 3 at hh
  have h1 := mul_le_mul_of_nonneg_left hh.1 hQ.le
  have h2 := mul_le_mul_of_nonneg_left hh.2 hQ.le
  simp only [← mul_assoc,mul_inv_cancel₀ hQ.ne',one_mul] at h1 h2
  constructor <;> nlinarith

theorem wide_zero (F G W : ℝ → ℂ) (js : List ℕ) (L N : ℕ) (dual : Bool)
    (T Q V b eD eH t : ℝ) (A B : ℂ) (hNT : (N:ℝ) ≤ T) (hQ : 0 < Q)
    (hs : Function.support F ⊆ Icc (1/2:ℝ) 3) (hwide : 2*T < Q) :
    mass F G W js L N dual T Q V b eD eH t A B = 0 := by
  unfold mass
  apply sum_eq_zero; intro k hk
  apply sum_eq_zero; intro d hd
  apply sum_eq_zero; intro j hj
  apply sum_eq_zero; intro l hl
  apply sum_eq_zero; intro delta hg
  unfold term
  split_ifs
  · apply sum_eq_zero; intro p hp
    have hpair := mem_filter.mp (mem_filter.mp hp).1
    have hdu : (d:ℝ)*p.1 ≤ T := (by exact_mod_cast hpair.2.2.1 : (d:ℝ)*p.1 ≤ N).trans hNT
    have hz : scaledCutoff F Q ((d:ℝ)*p.1) = 0 := by
      by_contra hz
      have hh := (scaled_support F Q hQ hs hz).1
      linarith
    simp [PRZZResolvedTailMass.coeff,PRZZUnfrozenPoisson.arithmetic,hz]
  · rfl

theorem uniform (F G W : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hW : ContDiff ℝ ∞ W) (hsW : Function.support W ⊆ Icc (1/2:ℝ) 3)
    (js : List ℕ) (a b S r eD eH power : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hS : 0 ≤ S) (hr : 0 < r)
    (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (L N : ℕ) (dual : Bool) (Q V t : ℝ) (A B : ℂ),
      1 ≤ N → (N:ℝ) ≤ T → 0 < Q → t ∈ Icc T (2*T) →
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      mass F G W js L N dual T Q V b eD eH t A B ≤ C*T^(-power) := by
  obtain ⟨C,hC,h⟩ := absorbed F G W hF hG hcF hcG hW hsW js a b S r eD eH power
    ha hb hS hr heD he
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with T h
  intro L N dual Q V t A B hN hNT hQ ht hA hB hsep
  have hT0 : 0 < T := lt_of_lt_of_le
    (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)) hNT
  by_cases hQT : Q ≤ 2*T
  · exact h L N dual Q V t A B hN hNT hQ hQT ht hA hB hsep (scaled_support F Q hQ hsF)
  · rw [wide_zero F G W js L N dual T Q V b eD eH t A B hNT hQ hsF (lt_of_not_ge hQT)]
    positivity

theorem time (F G W : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hW : ContDiff ℝ ∞ W) (hsW : Function.support W ⊆ Icc (1/2:ℝ) 3)
    (js : List ℕ) (a b S r eD eH power : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hS : 0 ≤ S) (hr : 0 < r)
    (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (L N : ℕ) (dual : Bool) (Q V : ℝ) (A B : ℂ) (phi : ℝ → ℂ),
      1 ≤ N → (N:ℝ) ≤ T → 0 < Q → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      Continuous phi →
      (∫ t in Icc T (2*T), ‖phi t‖*mass F G W js L N dual T Q V b eD eH t A B) ≤
        C*T^(-power)*(∫ t in Icc T (2*T), ‖phi t‖) := by
  obtain ⟨C,hC,h⟩ := uniform F G W hF hG hcF hcG hsF hW hsW js a b S r eD eH power
    ha hb hS hr heD he
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with T h
  intro L N dual Q V A B phi hN hNT hQ hA hB hsep hphi
  have hi : IntegrableOn (fun t => C*T^(-power)*‖phi t‖) (Icc T (2*T)) :=
    (continuous_const.mul hphi.norm).integrableOn_Icc
  have hn (t : ℝ) : 0 ≤ ‖phi t‖*mass F G W js L N dual T Q V b eD eH t A B := by
    unfold mass term
    positivity
  apply (integral_mono_of_nonneg (Eventually.of_forall hn) hi ?_).trans_eq
  · rw [integral_const_mul]
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (mul_le_mul_of_nonneg_left
      (h L N dual Q V t A B hN hNT hQ ht hA hB hsep) (norm_nonneg _)).trans_eq (by ring)

/-- Insert the computed outer Fourier mass in the PRZZ common error
budget. Only the ordinary L1 mass of the chosen time cutoff is retained;
there is no tail-bound or arithmetic-mass premise. -/
theorem przz_time (F G W : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hW : ContDiff ℝ ∞ W) (hsW : Function.support W ⊆ Icc (1/2:ℝ) 3)
    (js : List ℕ) (a b S r eD eH delta : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hS : 0 ≤ S) (hr : 0 < r)
    (heD : 0 ≤ eD) (he : eD < eH) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (L N : ℕ) (dual : Bool) (Q V P : ℝ) (A B : ℂ) (phi : ℝ → ℂ),
      1 ≤ N → (N:ℝ) ≤ T → 0 < Q → 0 ≤ P → ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ →
      Continuous phi → (∫ t in Icc T (2*T), ‖phi t‖) ≤ P*T →
      (∫ t in Icc T (2*T), ‖phi t‖*mass F G W js L N dual T Q V b eD eH t A B) ≤
        C*P*T^delta*PRZZOptimalPowers.target N T := by
  obtain ⟨C,hC,h⟩ := time F G W hF hG hcF hcG hsF hW hsW js a b S r eD eH (1-delta)
    ha hb hS hr heD he
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with T h
  intro L N dual Q V P A B phi hN hNT hQ hP hA hB hsep hphi hmass
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one (hNR.trans hNT)
  have htarg : 1 ≤ PRZZOptimalPowers.target N T := by
    unfold PRZZOptimalPowers.target
    exact (Real.one_le_rpow hNR (by norm_num : (0:ℝ) ≤ 7/4)).trans
      (le_add_of_nonneg_right (by positivity))
  have hh := h L N dual Q V A B phi hN hNT hQ hA hB hsep hphi
  calc
    _ ≤ C*T^(-(1-delta))*(P*T) := hh.trans (mul_le_mul_of_nonneg_left hmass (by positivity))
    _ = C*P*T^delta := by
      have hp : T^(-(1-delta))*T = T^delta := by
        calc
          _ = T^(-(1-delta))*T^(1:ℝ) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_add hT0]; congr 1; ring
      calc
        _ = C*P*(T^(-(1-delta))*T) := by ring
        _ = _ := by rw [hp]
    _ ≤ _ := le_mul_of_one_le_right (by positivity) htarg

#print axioms przz_time
#print axioms scaled_support
#print axioms wide_zero
#print axioms uniform
#print axioms time
end XiPrime8845.PRZZWindowTailTime
