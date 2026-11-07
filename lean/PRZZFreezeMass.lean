import PRZZAmplitudeFreeze
import PRZZDyadicArithmeticMass
import PRZZValuedCutoffs

/-! Supply the denominator-sensitive dyadic arithmetic mass for the joint
power/W/phase error. Actual cutoff values and unit phases are retained.
The local lower product numerator R0 remains explicit. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex MeasureTheory Set
namespace XiPrime8845.PRZZFreezeMass
open PRZZAmplitudeFreeze
set_option maxHeartbeats 3000000

theorem cutoff_time_bound (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hsF : HasCompactSupport F) (hsG : HasCompactSupport G) (Z : ℝ) :
    ∃ E : ℝ, 0 < E ∧ ∀ (js : List ℕ) (N d j l : ℕ) (T Q V R0 kappa : ℝ)
      (s : Finset (ℕ × ℕ)) (phase : ℕ × ℕ → ℂ) (R u : ℕ × ℕ → ℝ)
      (z sigma : ℂ) (phi : ℝ → ℂ),
      1 ≤ N → 1 ≤ d → s ⊆ PRZZDyadic.cell N j ×ˢ PRZZDyadic.cell N l →
      (∀ p ∈ s, d*p.1 ≤ N ∧ d*p.2 ≤ N) →
      (∀ p ∈ s, ‖phase p‖ ≤ 1) → ‖z‖ ≤ Z → sigma ≠ 0 →
      0 < T → 0 < R0 → 0 ≤ kappa → Continuous phi →
      (∀ p ∈ s, R0 ≤ R p) → (∀ p ∈ s, |u p| ≤ 1/2) →
      (∀ p ∈ s, |u p| ≤ kappa) →
      ‖∫ t in Icc T (2*T), phi t*∑ p ∈ s,
        ((((PRZZGCoefficient.coefficient js (d*p.1):ℂ)*star (PRZZGCoefficient.coefficient js (d*p.2):ℂ))*
          (F (Q⁻¹*((d:ℝ)*p.1))*G (V⁻¹*((d:ℝ)*p.2))*phase p))/((p.1:ℂ)*(p.2:ℂ)))*
          error z sigma (R p/t) t (u p)‖ ≤
        E*(1+1/‖sigma‖^2)*(kappa+2*T*kappa^2)*(2*T)^2*
          ((Real.log N)^(2*PRZZGCoefficient.degree js)/R0^2)*
          (∫ t in Icc T (2*T), ‖phi t‖) := by
  obtain ⟨C,D,hC,hD,hh⟩ := time_bound (ι := ℕ × ℕ) Z
  obtain ⟨B,hB,hb⟩ := PRZZValuedCutoffs.cutoff_pair_uniform F G hF hG hsF hsG
  let E := (C+D)*(B+1)+1
  have hE : 0 < E := by dsimp [E]; positivity
  refine ⟨E,hE,?_⟩
  intro js N d j l T Q V R0 kappa s phase R u z sigma phi
    hN hd hs hlen hp hz hsigma hT hR0 hk hphi hR hu huk
  let c := fun p : ℕ × ℕ =>
    (((PRZZGCoefficient.coefficient js (d*p.1):ℂ)*star (PRZZGCoefficient.coefficient js (d*p.2):ℂ))*
      (F (Q⁻¹*((d:ℝ)*p.1))*G (V⁻¹*((d:ℝ)*p.2))*phase p))/((p.1:ℂ)*(p.2:ℂ))
  have hc : (∑ p ∈ s, ‖c p‖) ≤ (Real.log N)^(2*PRZZGCoefficient.degree js)*B := by
    apply PRZZDyadicArithmeticMass.dilated_weighted_pair_mass js N d j l hN hd s hs hlen _ B hB
    intro p hp'
    rw [norm_mul]
    have hh := hb Q V ((d:ℝ)*p.1) ((d:ℝ)*p.2)
    change ‖F (Q⁻¹*((d:ℝ)*p.1))*G (V⁻¹*((d:ℝ)*p.2))‖ ≤ B at hh
    exact (mul_le_mul hh (hp p hp') (norm_nonneg _) hB).trans_eq (mul_one B)
  have hmass : (∑ p ∈ s, ‖c p‖/(R p)^2) ≤
      (Real.log N)^(2*PRZZGCoefficient.degree js)*B/R0^2 := by
    calc
      _ ≤ ∑ p ∈ s, ‖c p‖/R0^2 := by
        apply Finset.sum_le_sum
        intro p hp
        have hrp := hR p hp
        gcongr
      _ = (∑ p ∈ s, ‖c p‖)/R0^2 := by rw [Finset.sum_div]
      _ ≤ _ := div_le_div_of_nonneg_right hc (sq_nonneg _)
  have hi := hh z sigma hz hsigma s c R u T kappa phi hT hk hphi
    (fun p hp => hR0.trans_le (hR p hp)) hu huk
  have hcoeff : (C+D/‖sigma‖^2)*B ≤ E*(1+1/‖sigma‖^2) := by
    have hd : C+D/‖sigma‖^2 ≤ (C+D)*(1+1/‖sigma‖^2) := by
      simp only [div_eq_mul_inv,one_mul]
      nlinarith [mul_nonneg hC (inv_nonneg.mpr (sq_nonneg ‖sigma‖))]
    calc
      _ ≤ ((C+D)*(1+1/‖sigma‖^2))*B := mul_le_mul_of_nonneg_right hd hB
      _ = ((C+D)*B)*(1+1/‖sigma‖^2) := by ring
      _ ≤ _ := by gcongr; dsimp [E]; nlinarith
  apply hi.trans
  have hnon : 0 ≤ ∫ t in Icc T (2*T), ‖phi t‖ := integral_nonneg (fun t => norm_nonneg _)
  calc
    _ ≤ (C+D/‖sigma‖^2)*(kappa+2*T*kappa^2)*(2*T)^2*
        ((Real.log N)^(2*PRZZGCoefficient.degree js)*B/R0^2)*
        (∫ t in Icc T (2*T), ‖phi t‖) := by gcongr
    _ = ((C+D/‖sigma‖^2)*B)*
        ((kappa+2*T*kappa^2)*(2*T)^2*((Real.log N)^(2*PRZZGCoefficient.degree js)/R0^2)*
          (∫ t in Icc T (2*T), ‖phi t‖)) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_right hcoeff (by positivity)).trans_eq (by ring)

/-- The actual scaled shift family in the arithmetic and time aggregate.
Only the displayed quadratic logarithmic singularity remains. -/
theorem scaled_cutoff_time_bound (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hsF : HasCompactSupport F) (hsG : HasCompactSupport G) (S r : ℝ) (hr : 0 < r) :
    ∃ E : ℝ, 0 < E ∧ ∀ (A B : ℂ) (js : List ℕ) (N d j l : ℕ)
      (T Q V R0 kappa : ℝ) (s : Finset (ℕ × ℕ))
      (phase : ℕ × ℕ → ℂ) (R u : ℕ × ℕ → ℝ) (phi : ℝ → ℂ),
      ‖B‖ ≤ S → r ≤ ‖A+B‖ → 1 ≤ Real.log T →
      1 ≤ N → 1 ≤ d → s ⊆ PRZZDyadic.cell N j ×ˢ PRZZDyadic.cell N l →
      (∀ p ∈ s, d*p.1 ≤ N ∧ d*p.2 ≤ N) → (∀ p ∈ s, ‖phase p‖ ≤ 1) →
      0 < T → 0 < R0 → 0 ≤ kappa → Continuous phi →
      (∀ p ∈ s, R0 ≤ R p) → (∀ p ∈ s, |u p| ≤ 1/2) → (∀ p ∈ s, |u p| ≤ kappa) →
      ‖∫ t in Icc T (2*T), phi t*∑ p ∈ s,
        ((((PRZZGCoefficient.coefficient js (d*p.1):ℂ)*star (PRZZGCoefficient.coefficient js (d*p.2):ℂ))*
          (F (Q⁻¹*((d:ℝ)*p.1))*G (V⁻¹*((d:ℝ)*p.2))*phase p))/((p.1:ℂ)*(p.2:ℂ)))*
          error ((1/2:ℂ)+B/(Real.log T:ℂ)) ((A+B)/(Real.log T:ℂ)) (R p/t) t (u p)‖ ≤
        E*(1+(Real.log T)^2/r^2)*(kappa+2*T*kappa^2)*(2*T)^2*
          ((Real.log N)^(2*PRZZGCoefficient.degree js)/R0^2)*
          (∫ t in Icc T (2*T), ‖phi t‖) := by
  obtain ⟨E,hE,hh⟩ := cutoff_time_bound F G hF hG hsF hsG (1/2+S)
  refine ⟨E,hE,?_⟩
  intro A B js N d j l T Q V R0 kappa s phase R u phi hB hsep hL
    hN hd hs hlen hp hT hR0 hk hphi hR hu huk
  have hL0 : 0 < Real.log T := by linarith
  have hLc : (Real.log T:ℂ) ≠ 0 := by exact_mod_cast hL0.ne'
  have hz : ‖(1/2:ℂ)+B/(Real.log T:ℂ)‖ ≤ 1/2+S := by
    apply (norm_add_le _ _).trans
    norm_num only [norm_div,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos hL0,norm_one,Complex.norm_ofNat]
    have hb : ‖B‖/Real.log T ≤ S := (div_le_self (norm_nonneg B) hL).trans hB
    linarith
  have hsigma : (A+B)/(Real.log T:ℂ) ≠ 0 :=
    div_ne_zero (norm_pos_iff.mp (hr.trans_le hsep)) hLc
  have hi := hh js N d j l T Q V R0 kappa s phase R u _ _ phi
    hN hd hs hlen hp hz hsigma hT hR0 hk hphi hR hu huk
  have hcap := PRZZDiscardedSuppliers.log_shift_cap (fun sigma => 1+1/‖sigma‖^2)
    1 r (by norm_num) hr (fun sigma => by simp) A B (Real.log T) hL0.ne' hsep
  simp only [one_mul] at hcap
  apply hi.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcap hE.le)
        (by positivity)) (by positivity)) (by positivity))
    (integral_nonneg (fun t => norm_nonneg _))

#print axioms scaled_cutoff_time_bound
#print axioms cutoff_time_bound
end XiPrime8845.PRZZFreezeMass
