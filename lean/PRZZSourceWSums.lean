import PRZZSourceWDerivatives
import PRZZL1Truncation
import Mathlib.Analysis.PSeries

/-! Absolute arithmetic summability for the actual Gaussian sourceW.
The product argument and derivative-order weight are retained. This is not
the Gamma-ratio AFE kernel: transferring the conclusions to that kernel
still requires its own comparison estimate. -/
noncomputable section
open scoped BigOperators
open Filter Topology Finset
namespace XiPrime8845.PRZZSourceWSums
open PRZZDyadicEnvelope PRZZSourceWDerivatives

def sampled (sigma : ℂ) (k : ℕ) (p : ℕ × ℕ) : ℂ :=
  let x : ℝ := (p.1+1:ℕ)*(p.2+1:ℕ)
  (x^k:ℝ) * iteratedDeriv k (sourceW sigma) x

/-- One majorant for the entire two-dimensional arithmetic index set. -/
theorem sampled_bound (sigma : ℂ) (hs : sigma ≠ 0) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℕ × ℕ,
      ‖sampled sigma k p‖ ≤ C*((1/((p.1:ℝ)+1)^2)*(1/((p.2:ℝ)+1)^2)) := by
  obtain ⟨C,D,hC,hD,h⟩ := source_all_decay k 2 (by norm_num)
  refine ⟨C+D/‖sigma‖^2,by positivity,?_⟩
  intro p
  let x : ℝ := (p.1+1:ℕ)*(p.2+1:ℕ)
  have hx : 0 < x := by dsimp [x]; positivity
  have hh := mul_le_mul_of_nonneg_left (h sigma hs x hx) (pow_nonneg hx.le k)
  have he : x^k*((C+D/‖sigma‖^2)*x^(-(2:ℝ))/x^k) =
      (C+D/‖sigma‖^2)*((1/((p.1:ℝ)+1)^2)*(1/((p.2:ℝ)+1)^2)) := by
    rw [Real.rpow_neg hx.le,Real.rpow_two]
    dsimp [x]
    push_cast
    field_simp
  rw [he] at hh
  change ‖(x^k:ℝ) * iteratedDeriv k (sourceW sigma) x‖ ≤ _
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hx.le k)]
  exact hh

theorem sampled_summable (sigma : ℂ) (hs : sigma ≠ 0) (k : ℕ) :
    Summable (sampled sigma k) := by
  obtain ⟨C,hC,h⟩ := sampled_bound sigma hs k
  have hp : Summable (fun n : ℕ => 1/((n:ℝ)+1)^2) := by
    have hh := (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    simpa only [Nat.cast_add,Nat.cast_one] using hh
  exact ((hp.mul_of_nonneg hp (by intro n; positivity)
    (by intro n; positivity)).mul_left C).of_norm_bounded h

/-- Rectangular arithmetic cutoffs can be removed for this supplied kernel. -/
theorem sampled_cutoff_removed (sigma : ℂ) (hs : sigma ≠ 0) (k : ℕ) :
    Tendsto (fun M : ℕ => ∑ p ∈ (range M) ×ˢ (range M), sampled sigma k p)
      atTop (nhds (∑' p : ℕ × ℕ, sampled sigma k p)) :=
  (sampled_summable sigma hs k).hasSum.comp PRZZL1Truncation.rectangles_tendsto

/-- Absolute truncation error tends to zero, not merely a formal tsum. -/
theorem sampled_tail_tendsto (sigma : ℂ) (hs : sigma ≠ 0) (k : ℕ) :
    Tendsto (fun M : ℕ => ‖(∑' p : ℕ × ℕ, sampled sigma k p) -
      ∑ p ∈ (range M) ×ˢ (range M), sampled sigma k p‖) atTop (nhds 0) := by
  simpa using ((sampled_cutoff_removed sigma hs k).const_sub
    (∑' p : ℕ × ℕ, sampled sigma k p)).norm

/-- The stronger absolute tail mass also tends to zero. -/
theorem sampled_absolute_tail (sigma : ℂ) (hs : sigma ≠ 0) (k : ℕ) :
    Tendsto (fun M : ℕ => (∑' p : ℕ × ℕ, ‖sampled sigma k p‖) -
      ∑ p ∈ (range M) ×ˢ (range M), ‖sampled sigma k p‖) atTop (nhds 0) := by
  have hh := (sampled_summable sigma hs k).norm.hasSum.comp
    PRZZL1Truncation.rectangles_tendsto
  simpa using hh.const_sub (∑' p : ℕ × ℕ, ‖sampled sigma k p‖)

#print axioms sampled_absolute_tail
#print axioms sampled_tail_tendsto
#print axioms sampled_bound
#print axioms sampled_summable
#print axioms sampled_cutoff_removed
end XiPrime8845.PRZZSourceWSums
