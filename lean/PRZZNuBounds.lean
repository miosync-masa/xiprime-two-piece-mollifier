import PRZZNuCoefficient
import PRZZEulerSubpower
import PRZZSourceTypeII

/-! Uniform subpower bounds for the signed h*Delta coefficient and its
positive-frequency DI rectangle. The constants precede the finite source
set and integration variables. DI remains an explicit proposition input. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZNuBounds
open PRZZNuCoefficient PRZZKloostermanInputs PRZZSourceTypeII
set_option maxHeartbeats 2000000

theorem divisors_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → (n.divisors.card:ℝ) ≤ C*(n:ℝ)^ε := by
  obtain ⟨C,hC,h⟩ := PRZZEulerSubpower.eulerMass_subpower (ε/2) (ε/2)
    (by positivity) (by positivity)
  refine ⟨C,hC,?_⟩
  intro n hn
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hsum : (n.divisors.card:ℝ) ≤
      (n:ℝ)^(ε/2)*(∑ r ∈ n.divisors, (r:ℝ)^(-(ε/2))) := by
    rw [mul_sum]
    calc
      _ = ∑ r ∈ n.divisors, (1:ℝ) := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro r hr
        have hrR : (0:ℝ) < r := by exact_mod_cast Nat.pos_of_mem_divisors hr
        rw [Real.rpow_neg hrR.le,← div_eq_mul_inv]
        apply (one_le_div (Real.rpow_pos_of_pos hrR _)).mpr
        exact Real.rpow_le_rpow hrR.le
          (by exact_mod_cast Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hr)) (by positivity)
  have hmass : (∑ r ∈ n.divisors, (r:ℝ)^(-(ε/2))) ≤
      SupportTail.eulerMass n (1-ε/2) := by
    have hh := SupportTail.supported_mass_le n hn.ne' n.divisors (1-ε/2) (by linarith)
      (fun r hr p _ hpr => hpr.trans (Nat.dvd_of_mem_divisors hr))
    simpa only [show 1-ε/2-1 = -(ε/2) by ring] using hh
  calc
    _ ≤ (n:ℝ)^(ε/2)*SupportTail.eulerMass n (1-ε/2) :=
      hsum.trans (mul_le_mul_of_nonneg_left hmass (Real.rpow_nonneg hnR.le _))
    _ ≤ (n:ℝ)^(ε/2)*(C*(n:ℝ)^(ε/2)) :=
      mul_le_mul_of_nonneg_left (h n hn) (Real.rpow_nonneg hnR.le _)
    _ = C*(n:ℝ)^ε := by
      rw [← mul_assoc,mul_comm ((n:ℝ)^(ε/2)) C,mul_assoc,← Real.rpow_add hnR]
      congr 2
      ring

theorem nu_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset (ℤ × ℕ)), (∀ q ∈ s, 0 < q.2) →
      ∀ x y : ℝ, ∀ k : ℤ, k ≠ 0 → ‖nu s x y k‖ ≤ C*(k.natAbs:ℝ)^ε := by
  obtain ⟨C,hC,h⟩ := divisors_subpower ε hε
  exact ⟨C,hC,fun s hs x y k hk => (nu_norm_le_divisors s x y k hk hs).trans
    (h k.natAbs (Int.natAbs_pos.mpr hk))⟩

/-- The frequency envelope is supplied, not assumed. Remaining arithmetic
coefficient envelopes and the DI theorem itself are explicit inputs.
Only the positive-frequency branch is asserted here. -/
theorem positive_rectangle_bound (hDI : DeshouillersIwaniecLemma1)
    (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (s : Finset (ℤ × ℕ)), (∀ q ∈ s, 0 < q.2) →
      ∀ A E F V : ℝ, 1 ≤ A → 1 ≤ E → 1 ≤ F → 1 ≤ V →
      ∀ h d : ℕ, 1 ≤ h → ∀ R S Q : ℝ, 0 ≤ R → 0 ≤ S → 0 < Q →
      ∀ r beta alpha : ℕ → ℂ,
      (∀ v ∈ Icc 1 ⌊V⌋₊, ‖r v‖ ≤ R) →
      (∀ f ∈ Icc 1 ⌊F⌋₊, ‖beta f‖ ≤ S) →
      (∀ e ∈ Icc 1 ⌊E⌋₊, ‖alpha e‖ ≤ Q) → ∀ x y : ℝ,
      ‖sourceSum A E F V h d r beta (fun k => nu s x y k) alpha‖ ≤
        R*S*((C*A^η)*Q)*K*diBound ε V F A E h := by
  obtain ⟨C,hC,hnu⟩ := nu_subpower η hη
  obtain ⟨K,hK,hbound⟩ := sourceSum_bound hDI ε hε
  refine ⟨C,K,hC,hK,?_⟩
  intro s hs A E F V hA hE hF hV h d hh R S Q hR hS hQ r beta alpha hr hb ha x y
  apply hbound A E F V hA hE hF hV h d hh R S (C*A^η) Q hR hS
    (mul_pos hC (Real.rpow_pos_of_pos (by linarith) _)) hQ r beta _ alpha hr hb _ ha
  intro k hk
  have hk0 : 0 < k := (mem_Icc.mp hk).1
  have hkA : (k:ℝ) ≤ A := (Nat.cast_le.mpr (mem_Icc.mp hk).2).trans (Nat.floor_le (by linarith))
  have hn := hnu s hs x y (k:ℤ) (by exact_mod_cast hk0.ne')
  simp only [Int.natAbs_natCast] at hn
  exact hn.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by positivity) hkA hη.le) hC.le)

#print axioms divisors_subpower
#print axioms nu_subpower
#print axioms positive_rectangle_bound
end XiPrime8845.PRZZNuBounds
