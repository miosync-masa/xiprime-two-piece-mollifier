import FengAtG
import CoprimeEulerCompletion

/-! Exact off-g convolution and its finite coprime-main-term replacement error.
The finite proxy below is not asserted to have reached a limiting integral. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
namespace XiPrime8845.FengOutside
open FengAtG CoprimeShift ShiftWeights CoprimeEulerCompletion
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

theorem outside_weighted (N g : ℕ) (w : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 N, outside g n*w n) =
      ∑ r ∈ (Finset.Icc 1 N).filter (fun r => r.Coprime g), mark r*
        ∑ m ∈ (Finset.Icc 1 (N/r)).filter (fun m => m.Coprime g), (μ m:ℂ)*w (r*m) := by
  have h := ElementaryGcd.weighted_divisor_reindex N
    (fun r => if r.Coprime g then mark r else 0)
    (fun m => if m.Coprime g then (μ m:ℂ) else 0) w
  simpa only [outside,Finset.sum_filter,ite_mul,zero_mul] using h

def transform (N g : ℕ) (L : ℝ) (A : ℂ) (X : ℕ → ℂ) : ℂ :=
  (μ g:ℂ)/(L:ℂ)^2 * ∑ r ∈ (Finset.Icc 1 N).filter (fun r => r.Coprime g),
    mark r*supportFactor r L A*X r

/-- Exact N/r cutoff and u-log(r)/L translation; all prime powers retained. -/
theorem outsideBlock_transform (N g : ℕ) (L u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) :
    outsideBlock N g L u θ P A = transform N g L A
      (fun r => coprimeScaled (N/r) g L (u-Real.log r/L) θ P A) := by
  have he : outsideBlock N g L u θ P A =
      (L:ℂ)*((μ g:ℂ)/(L:ℂ)^2) *
        (∑ n ∈ Finset.Icc 1 N, outside g n*(weight A u θ P (Real.log n/L)/(n:ℂ))) := by
    simp only [outsideBlock,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros
    ring
  rw [he,outside_weighted]
  simp only [transform,coprimeScaled,coprimeInner,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro m hm
  have hr0 : (r:ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by
    have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).1; omega)
  have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by
    have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1; omega)
  rw [Nat.cast_mul,Real.log_mul hr0 hm0,add_div,weight_translate]
  unfold supportFactor
  push_cast
  ring

/-- Replace just the coprime scaled sum; the prime-power sum is still finite. -/
def mainProxy (N g : ℕ) (L u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) : ℂ :=
  transform N g L A (fun r => zeroEulerMain g (u-Real.log r/L) θ P A)

theorem transform_sub (N g : ℕ) (L : ℝ) (A : ℂ) (X Y : ℕ → ℂ) :
    transform N g L A X - transform N g L A Y = transform N g L A (fun r => X r-Y r) := by
  simp only [transform,mul_sub,Finset.sum_sub_distrib]

/-- A pointwise finite error budget with the actual arithmetic weights. -/
theorem transform_error_bound (N g : ℕ) (L : ℝ) (A : ℂ) (X Y : ℕ → ℂ) :
    ‖transform N g L A X-transform N g L A Y‖ ≤
      1/|L|^2 * ∑ r ∈ (Finset.Icc 1 N).filter (fun r => r.Coprime g),
        ‖mark r*supportFactor r L A‖*‖X r-Y r‖ := by
  have hμ : ‖(μ g:ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_intCast] using (show |(μ g:ℝ)| ≤ 1 by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=g))
  rw [transform_sub,transform,norm_mul,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs]
  have hh := norm_sum_le ((Finset.Icc 1 N).filter (fun r => r.Coprime g))
    (fun r => mark r*supportFactor r L A*(X r-Y r))
  simp only [norm_mul] at hh
  apply mul_le_mul (div_le_div_of_nonneg_right hμ (sq_nonneg _))
    (by simpa only [norm_mul,mul_assoc] using hh) (norm_nonneg _) (by positivity)

theorem outsideBlock_main_error (N g : ℕ) (L u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) :
    ‖outsideBlock N g L u θ P A-mainProxy N g L u θ P A‖ ≤
      1/|L|^2 * ∑ r ∈ (Finset.Icc 1 N).filter (fun r => r.Coprime g),
        ‖mark r*supportFactor r L A‖ *
          ‖coprimeScaled (N/r) g L (u-Real.log r/L) θ P A-
            zeroEulerMain g (u-Real.log r/L) θ P A‖ := by
  rw [outsideBlock_transform,mainProxy]
  exact transform_error_bound N g L A _ _

def errorBudget (N g : ℕ) (L u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) : ℝ :=
  1/|L|^2 * ∑ r ∈ (Finset.Icc 1 N).filter (fun r => r.Coprime g),
    ‖mark r*supportFactor r L A‖ *
      ‖coprimeScaled (N/r) g L (u-Real.log r/L) θ P A-
        zeroEulerMain g (u-Real.log r/L) θ P A‖

theorem errorBudget_nonneg (N g : ℕ) (L u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) :
    0 ≤ errorBudget N g L u θ P A := by unfold errorBudget; positivity

/-- Returning the exact error to g-average does not silently assert its decay. -/
theorem outside_error_average (M : ℕ) (N : ℕ → ℕ) (L θ : ℝ) (u : ℕ → ℝ)
    (P : Polynomial ℂ) (A : ℂ) :
    (∑ g ∈ Finset.Icc 1 M, (1/(g:ℝ))*
      ‖outsideBlock (N g) g L (u g) θ P A-mainProxy (N g) g L (u g) θ P A‖) ≤
    ∑ g ∈ Finset.Icc 1 M, (1/(g:ℝ))*errorBudget (N g) g L (u g) θ P A := by
  apply Finset.sum_le_sum
  intro g hg
  exact mul_le_mul_of_nonneg_left (outsideBlock_main_error (N g) g L (u g) θ P A) (by positivity)

#print axioms outside_weighted
#print axioms outsideBlock_transform
#print axioms transform_sub
#print axioms transform_error_bound
#print axioms outsideBlock_main_error
#print axioms errorBudget_nonneg
#print axioms outside_error_average
end XiPrime8845.FengOutside
