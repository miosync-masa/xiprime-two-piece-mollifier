import ShiftedMobius

/-! Exact shifted coprime convolution with a finite natural cutoff.
No uniform-in-g asymptotic is asserted by the finite identity. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
namespace XiPrime8845.CoprimeShift
open ShiftWeights ElementaryGcd
attribute [local instance] Classical.propDecidable

def inner (N : ℕ) (L u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, (μ n : ℂ) / n * weight A u θ P (Real.log n/L)

def coprimeInner (N g : ℕ) (L u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) : ℂ :=
  ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n.Coprime g),
    (μ n : ℂ) / n * weight A u θ P (Real.log n/L)

def supportFactor (r : ℕ) (L : ℝ) (A : ℂ) : ℂ :=
  Complex.exp (-A * (Real.log r/L : ℝ)) / r

theorem weight_translate (A : ℂ) (u θ a b : ℝ) (P : Polynomial ℂ) :
    weight A u θ P (a+b) = Complex.exp (-A*a) * weight A (u-a) θ P b := by
  unfold weight
  rw [show -A * ((a+b : ℝ) : ℂ) = -A*a + -A*b by push_cast; ring,
    Complex.exp_add]
  have he : (u-(a+b))/θ = ((u-a)-b)/θ := by ring
  rw [he, mul_assoc]

theorem shifted_coprime_expansion (N g : ℕ) (L u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) :
    coprimeInner N g L u θ P A =
      ∑ r ∈ (Finset.Icc 1 N).filter (SmoothMobius.supported g),
        supportFactor r L A * inner (N/r) L (u-Real.log r/L) θ P A := by
  unfold coprimeInner
  simp_rw [div_mul_eq_mul_div, mul_div_assoc]
  rw [coprime_weighted_expansion]
  apply Finset.sum_congr rfl
  intro r hr
  unfold inner
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hr0 : (r : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).1))
  have hm0 : (m : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hm).1)
  rw [Nat.cast_mul, Real.log_mul hr0 hm0, add_div, weight_translate]
  unfold supportFactor
  push_cast
  ring

/-- Separate the Conrey factor mu(g), retaining its exact value. -/
theorem conrey_shifted_expansion (N g : ℕ) (L u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) :
    (∑ n ∈ Finset.Icc 1 N, (μ (g*n) : ℂ) / n * weight A u θ P (Real.log n/L)) =
      (μ g : ℂ) * ∑ r ∈ (Finset.Icc 1 N).filter (SmoothMobius.supported g),
        supportFactor r L A * inner (N/r) L (u-Real.log r/L) θ P A := by
  rw [← shifted_coprime_expansion, coprimeInner, Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [SmoothMobius.moebius_mul_indicator]
  split_ifs <;> simp_all <;> ring

theorem inner_eq_weightedSum (L u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) :
    inner ⌊Real.exp (L*u)⌋₊ L u θ P A =
      WeightedMobius.weightedSum L u (weight A u θ P) := by
  unfold inner WeightedMobius.weightedSum
  have he : Finset.Icc 1 ⌊Real.exp (L*u)⌋₊ = Finset.Ioc 0 ⌊Real.exp (L*u)⌋₊ := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [he]
  push_cast
  rfl

theorem translated_cutoff (L u : ℝ) (r : ℕ) (hL : L ≠ 0) (hr : r ≠ 0) :
    ⌊Real.exp (L*u)⌋₊ / r = ⌊Real.exp (L*(u-Real.log r/L))⌋₊ := by
  have hr0 : 0 < (r : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hr
  rw [← Nat.floor_div_natCast]
  congr 1
  rw [show L*(u-Real.log r/L) = L*u-Real.log r by field_simp,
    Real.exp_sub, Real.exp_log hr0]

/-- Exact interface to the already proved unrestricted shifted main term.
The translated cutoff may reach zero; no uniform limit at that endpoint is used. -/
theorem scaled_coprime_expansion (L u θ : ℝ) (g : ℕ) (P : Polynomial ℂ) (A : ℂ)
    (hL : L ≠ 0) :
    (L : ℂ)*coprimeInner ⌊Real.exp (L*u)⌋₊ g L u θ P A =
      ∑ r ∈ (Finset.Icc 1 ⌊Real.exp (L*u)⌋₊).filter (SmoothMobius.supported g),
        supportFactor r L A * ShiftedMobius.scaledSum L (u-Real.log r/L) θ P A := by
  rw [shifted_coprime_expansion, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hr0 : r ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).1)
  rw [translated_cutoff L u r hL hr0, inner_eq_weightedSum]
  unfold ShiftedMobius.scaledSum
  ring

#print axioms translated_cutoff
#print axioms scaled_coprime_expansion
#print axioms weight_translate
#print axioms shifted_coprime_expansion
#print axioms conrey_shifted_expansion
#print axioms inner_eq_weightedSum
end XiPrime8845.CoprimeShift
