import PRZZArithmeticMass
import PRZZDyadic

/-! Denominator-sensitive mass on the actual half-open dyadic cells.
Each reciprocal denominator pays for its own cell cardinality. Restrictions
such as coprimality or a product cutoff may be retained by taking a subset. -/
noncomputable section
open scoped BigOperators
open Finset
namespace XiPrime8845.PRZZDyadicArithmeticMass
open PRZZGCoefficient PRZZDyadic

theorem cell_card (N j : ℕ) : (cell N j).card ≤ 2^j := by
  have hsub : cell N j ⊆ Ico (2^j) (2^(j+1)) := by
    intro n hn
    have h := (mem_cell N j n).mp hn
    exact mem_Ico.mpr h.2
  have h := card_le_card hsub
  simp only [Nat.card_Ico, pow_succ] at h
  omega

theorem reciprocal_mass (js : List ℕ) (N j : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ cell N j, |coefficient js n|/(n:ℝ)) ≤ (Real.log N)^degree js := by
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hp : 0 < (2:ℝ)^j := by positivity
  calc
    _ ≤ ∑ _n ∈ cell N j, (Real.log N)^degree js/(2:ℝ)^j := by
      apply sum_le_sum
      intro n hn
      have h := (mem_cell N j n).mp hn
      have hnn := mem_Icc.mp h.1
      apply div_le_div₀ (pow_nonneg hlog _) (coefficient_bound js N hN n hnn.1 hnn.2)
        hp
      exact_mod_cast h.2.1
    _ = ((cell N j).card:ℝ)*((Real.log N)^degree js/(2:ℝ)^j) := by simp
    _ ≤ (2:ℝ)^j*((Real.log N)^degree js/(2:ℝ)^j) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast cell_card N j
    _ = _ := by field_simp

/-- No cardinality of the retained pair set remains in the bound. -/
theorem pair_mass (js : List ℕ) (N j l : ℕ) (hN : 1 ≤ N)
    (s : Finset (ℕ × ℕ)) (hs : s ⊆ (cell N j) ×ˢ (cell N l)) :
    (∑ p ∈ s, |coefficient js p.1|/(p.1:ℝ) *
      (|coefficient js p.2|/(p.2:ℝ))) ≤ (Real.log N)^(2*degree js) := by
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  calc
    _ ≤ ∑ p ∈ (cell N j) ×ˢ (cell N l),
      |coefficient js p.1|/(p.1:ℝ) * (|coefficient js p.2|/(p.2:ℝ)) :=
      sum_le_sum_of_subset_of_nonneg hs (by intro p _ _; positivity)
    _ = (∑ n ∈ cell N j, |coefficient js n|/(n:ℝ))*
      (∑ m ∈ cell N l, |coefficient js m|/(m:ℝ)) := by rw [sum_mul_sum, sum_product]
    _ ≤ (Real.log N)^degree js*(Real.log N)^degree js :=
      mul_le_mul (reciprocal_mass js N j hN) (reciprocal_mass js N l hN)
        (sum_nonneg (by intro n _; positivity)) (pow_nonneg hlog _)
    _ = _ := by rw [← pow_add]; congr 1; omega

/-- Analytic factors remain inside the restricted sum. No distinctness of
frequencies is asserted: this theorem concerns the arithmetic pair set. -/
theorem weighted_pair_mass (js : List ℕ) (N j l : ℕ) (hN : 1 ≤ N)
    (s : Finset (ℕ × ℕ)) (hs : s ⊆ (cell N j) ×ˢ (cell N l))
    (u : ℕ × ℕ → ℂ) (B : ℝ) (hB : 0 ≤ B) (hu : ∀ p ∈ s, ‖u p‖ ≤ B) :
    (∑ p ∈ s, ‖(((coefficient js p.1:ℂ)*star (coefficient js p.2:ℂ))*u p)/
      ((p.1:ℂ)*(p.2:ℂ))‖) ≤ (Real.log N)^(2*degree js)*B := by
  calc
    _ = ∑ p ∈ s, (|coefficient js p.1|/(p.1:ℝ)*
        (|coefficient js p.2|/(p.2:ℝ)))*‖u p‖ := by
      apply sum_congr rfl
      intro p hp
      simp only [norm_div,norm_mul,norm_star,Complex.norm_real,Real.norm_eq_abs,
        Complex.norm_natCast]
      ring
    _ ≤ ∑ p ∈ s, (|coefficient js p.1|/(p.1:ℝ)*
        (|coefficient js p.2|/(p.2:ℝ)))*B := by
      apply sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left (hu p hp) (by positivity)
    _ = (∑ p ∈ s, |coefficient js p.1|/(p.1:ℝ)*
        (|coefficient js p.2|/(p.2:ℝ)))*B := by rw [sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (pair_mass js N j l hN s hs) hB

/-- Two fixed cutoff profiles supply their own uniform analytic mass.
The constant precedes both dilation scales, d, N and the restricted pair set.
Unit-modulus phases may remain in the weight. This does not estimate the
additional Gamma/power factors of the original AFE coefficient. -/
theorem scaled_cutoff_pair_mass (F G : ℝ → ℂ)
    (hF : Continuous F) (hG : Continuous G)
    (hsF : HasCompactSupport F) (hsG : HasCompactSupport G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (js : List ℕ) (N j l : ℕ) (Q R d : ℝ)
      (s : Finset (ℕ × ℕ)) (phase : ℕ × ℕ → ℂ),
      1 ≤ N → s ⊆ (cell N j) ×ˢ (cell N l) →
      (∀ p ∈ s, ‖phase p‖ ≤ 1) →
      (∑ p ∈ s, ‖(((coefficient js p.1:ℂ)*star (coefficient js p.2:ℂ))*
        (F (Q⁻¹*(d*p.1))*G (R⁻¹*(d*p.2))*phase p))/
        ((p.1:ℂ)*(p.2:ℂ))‖) ≤ (Real.log N)^(2*degree js)*C := by
  obtain ⟨CF,hCF⟩ := hsF.exists_bound_of_continuous hF
  obtain ⟨CG,hCG⟩ := hsG.exists_bound_of_continuous hG
  have hCF0 : 0 ≤ CF := (norm_nonneg _).trans (hCF 0)
  have hCG0 : 0 ≤ CG := (norm_nonneg _).trans (hCG 0)
  refine ⟨CF*CG,mul_nonneg hCF0 hCG0,?_⟩
  intro js N j l Q R d s phase hN hs hphase
  apply weighted_pair_mass js N j l hN s hs _ (CF*CG) (mul_nonneg hCF0 hCG0)
  intro p hp
  simp only [norm_mul]
  calc
    _ ≤ (CF*CG)*1 := mul_le_mul
      (mul_le_mul (hCF _) (hCG _) (norm_nonneg _) hCF0)
      (hphase p hp) (norm_nonneg _) (mul_nonneg hCF0 hCG0)
    _ = _ := mul_one _

/-- Original coefficients at d*u and d*v. The original length restrictions
are retained; the two dyadic denominators pay for the cell cardinality. -/
theorem dilated_weighted_pair_mass (js : List ℕ) (N d j l : ℕ)
    (hN : 1 ≤ N) (hd : 1 ≤ d) (s : Finset (ℕ × ℕ))
    (hs : s ⊆ (cell N j) ×ˢ (cell N l))
    (hlen : ∀ p ∈ s, d*p.1 ≤ N ∧ d*p.2 ≤ N)
    (u : ℕ × ℕ → ℂ) (B : ℝ) (hB : 0 ≤ B) (hu : ∀ p ∈ s, ‖u p‖ ≤ B) :
    (∑ p ∈ s, ‖(((coefficient js (d*p.1):ℂ)*star (coefficient js (d*p.2):ℂ))*u p)/
      ((p.1:ℂ)*(p.2:ℂ))‖) ≤ (Real.log N)^(2*degree js)*B := by
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hcard : (s.card:ℝ) ≤ (2:ℝ)^j*(2:ℝ)^l := by
    exact_mod_cast (card_le_card hs).trans
      (by rw [card_product]; exact Nat.mul_le_mul (cell_card N j) (cell_card N l))
  calc
    _ ≤ ∑ _p ∈ s, ((Real.log N)^(2*degree js)*B)/((2:ℝ)^j*(2:ℝ)^l) := by
      apply sum_le_sum
      intro p hp
      have hc := mem_product.mp (hs hp)
      have h1 := (mem_cell N j p.1).mp hc.1
      have h2 := (mem_cell N l p.2).mp hc.2
      have hp1 := (mem_Icc.mp h1.1).1
      have hp2 := (mem_Icc.mp h2.1).1
      have ha := coefficient_bound js N hN (d*p.1) (Nat.mul_le_mul hd hp1) (hlen p hp).1
      have hb := coefficient_bound js N hN (d*p.2) (Nat.mul_le_mul hd hp2) (hlen p hp).2
      have hn : |coefficient js (d*p.1)| * |coefficient js (d*p.2)| * ‖u p‖ ≤
          (Real.log N)^(2*degree js)*B := by
        have hh := mul_le_mul (mul_le_mul ha hb (abs_nonneg _) (pow_nonneg hlog _))
          (hu p hp) (norm_nonneg _) (by positivity)
        simpa only [← pow_add,← two_mul] using hh
      simp only [norm_div,norm_mul,norm_star,Complex.norm_real,Real.norm_eq_abs,
        Complex.norm_natCast]
      apply div_le_div₀ (by positivity) hn (by positivity)
      exact mul_le_mul (by exact_mod_cast h1.2.1) (by exact_mod_cast h2.2.1)
        (by positivity) (by positivity)
    _ = (s.card:ℝ)*(((Real.log N)^(2*degree js)*B)/((2:ℝ)^j*(2:ℝ)^l)) := by simp
    _ ≤ ((2:ℝ)^j*(2:ℝ)^l)*(((Real.log N)^(2*degree js)*B)/((2:ℝ)^j*(2:ℝ)^l)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by field_simp

#print axioms dilated_weighted_pair_mass
#print axioms scaled_cutoff_pair_mass
#print axioms weighted_pair_mass
#print axioms cell_card
#print axioms reciprocal_mass
#print axioms pair_mass
end XiPrime8845.PRZZDyadicArithmeticMass
