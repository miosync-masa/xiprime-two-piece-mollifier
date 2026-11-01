import PRZZGroupedDI
import Mathlib.Analysis.Fourier.AddCircle

/-! Exact separation of the sharp product cutoff by integer comparison.
The threshold min(F,N/e) is kept in the e coefficient. Fourier phases have
unit norm. The L1 cost is explicit; a logarithmic estimate for that cost
is NOT asserted in this module. -/
noncomputable section
open scoped BigOperators
open Finset MeasureTheory
namespace XiPrime8845.PRZZSharpCutoff
set_option maxHeartbeats 2000000

abbrev Circle := AddCircle (1:ℝ)
abbrev haar : Measure Circle := AddCircle.haarAddCircle

private theorem cont_integrable {E : Type*} [NormedAddCommGroup E] {f : Circle → E}
    (hf : Continuous f) : Integrable f haar := by
  simpa only [integrableOn_univ] using
    (hf.continuousOn.integrableOn_compact (μ := haar) isCompact_univ)

def kernel (F : ℕ) (t : Circle) : ℂ := ∑ k ∈ range (F+1), fourier (-(k:ℤ)) t
def cost (F : ℕ) : ℝ := ∫ t, ‖kernel F t‖ ∂haar
def threshold (N F e : ℕ) : ℕ := min F (N/e)

theorem phase_norm (k : ℤ) (t : Circle) : ‖fourier k t‖ = 1 := by
  exact Circle.norm_coe _

theorem phase_integral (k : ℤ) :
    (∫ t : Circle, fourier k t ∂haar) = if k=0 then 1 else 0 := by
  split_ifs with hk
  · simp [hk]
  · exact integral_eq_zero_of_add_right_eq_neg
      (fourier_add_half_inv_index hk (by norm_num : (0:ℝ)<1))

theorem kernel_continuous (F : ℕ) : Continuous (kernel F) := by
  apply continuous_finsetSum
  intro k hk
  exact (fourier (-(k:ℤ))).continuous

theorem comparison (F q m : ℕ) (hq : q ≤ F) :
    (∫ t : Circle, kernel F t*fourier (q:ℤ) t*fourier (-(m:ℤ)) t ∂haar) =
      if m ≤ q then 1 else 0 := by
  simp only [kernel,sum_mul]
  rw [integral_finsetSum]
  swap
  · intro k hk
    apply cont_integrable
    exact ((fourier (-(k:ℤ))).continuous.mul (fourier (q:ℤ)).continuous).mul
      (fourier (-(m:ℤ))).continuous
  simp_rw [← fourier_add,phase_integral]
  by_cases hmq : m ≤ q
  · rw [if_pos hmq]
    rw [sum_eq_single (q-m)]
    · rw [if_pos (by omega)]
    · intro k hk hne
      exact if_neg (by omega)
    · intro hk
      exact False.elim (hk (mem_range.mpr (by omega)))
  · rw [if_neg hmq]
    apply sum_eq_zero
    intro k hk
    exact if_neg (by omega)

theorem product_comparison (N F e m : ℕ) (he : 0 < e) (hm : m ≤ F) :
    (∫ t : Circle, kernel F t*fourier (threshold N F e:ℤ) t*
      fourier (-(m:ℤ)) t ∂haar) = if e*m ≤ N then 1 else 0 := by
  rw [comparison F (threshold N F e) m (min_le_left _ _)]
  have hh : m ≤ threshold N F e ↔ e*m ≤ N := by
    simp only [threshold,le_min_iff,hm,true_and]
    rw [Nat.le_div_iff_mul_le he]
    rw [Nat.mul_comm]
  simp only [hh]

def separated (N E F : ℕ) (K : ℕ → ℕ → ℂ) (t : Circle) : ℂ :=
  ∑ e ∈ Icc 1 E, ∑ m ∈ Icc 1 F,
    K e m*fourier (threshold N F e:ℤ) t*fourier (-(m:ℤ)) t

theorem separated_continuous (N E F : ℕ) (K : ℕ → ℕ → ℂ) :
    Continuous (separated N E F K) := by
  apply continuous_finsetSum
  intro e he
  apply continuous_finsetSum
  intro m hm
  exact (continuous_const.mul (fourier _).continuous).mul (fourier _).continuous

/-- No smoothing error: equality includes products exactly equal to N. -/
theorem sharp_eq (N E F : ℕ) (K : ℕ → ℕ → ℂ) :
    (∑ e ∈ Icc 1 E, ∑ m ∈ Icc 1 F, if e*m ≤ N then K e m else 0) =
      ∫ t : Circle, kernel F t*separated N E F K t ∂haar := by
  simp only [separated,mul_sum]
  rw [integral_finsetSum]
  · apply sum_congr rfl
    intro e he
    rw [integral_finsetSum]
    · apply sum_congr rfl
      intro m hm
      have hh := product_comparison N F e m (mem_Icc.mp he).1 (mem_Icc.mp hm).2
      rw [show (fun t : Circle => kernel F t*(K e m*fourier (threshold N F e:ℤ) t*
          fourier (-(m:ℤ)) t)) = (fun t => K e m*(kernel F t*
          fourier (threshold N F e:ℤ) t*fourier (-(m:ℤ)) t)) by funext t; ring,
        integral_const_mul,hh]
      split_ifs <;> simp
    · intro m hm
      exact cont_integrable ((kernel_continuous F).mul ((continuous_const.mul
        (fourier _).continuous).mul (fourier _).continuous))
  · intro e he
    apply integrable_finsetSum
    intro m hm
    exact cont_integrable ((kernel_continuous F).mul ((continuous_const.mul
      (fourier _).continuous).mul (fourier _).continuous))

theorem cost_nonneg (F : ℕ) : 0 ≤ cost F := integral_nonneg (fun _ => norm_nonneg _)

/-- Exact geometric numerator, the starting point for the logarithmic L1 bound. -/
theorem kernel_geometric (F : ℕ) (t : Circle) :
    kernel F t*(fourier (-1) t-1) = fourier (-((F+1:ℕ):ℤ)) t-1 := by
  induction F with
  | zero => simp [kernel]
  | succ F ih =>
    have hk : kernel (F+1) t = kernel F t+fourier (-((F+1:ℕ):ℤ)) t := by
      exact sum_range_succ _ (F+1)
    have hp : fourier (-((F+1+1:ℕ):ℤ)) t =
        fourier (-((F+1:ℕ):ℤ)) t*fourier (-1) t := by
      rw [← fourier_add]
      congr 1
    rw [hk,hp]
    linear_combination ih

theorem kernel_decay (F : ℕ) (t : Circle) :
    ‖kernel F t‖*‖fourier (-1) t-1‖ ≤ 2 := by
  rw [← norm_mul,kernel_geometric]
  exact (norm_sub_le _ _).trans (by rw [phase_norm,norm_one]; norm_num)

theorem kernel_norm_le (F : ℕ) (t : Circle) : ‖kernel F t‖ ≤ F+1 := by
  exact (norm_sum_le _ _).trans (by
    simp only [phase_norm,sum_const,card_range,nsmul_eq_mul,mul_one,Nat.cast_add,Nat.cast_one]; rfl)

/-- A coarse finite bound only; this is not the logarithmic loss required
for the optimized PRZZ exponents. -/
theorem cost_le (F : ℕ) : cost F ≤ F+1 := by
  calc
    _ ≤ ∫ _ : Circle, ((F:ℝ)+1) ∂haar := by
      apply integral_mono (cont_integrable (kernel_continuous F).norm) (integrable_const _)
      intro t
      exact kernel_norm_le F t
    _ = _ := by simp

theorem sharp_bound (N E F : ℕ) (K : ℕ → ℕ → ℂ) (B : ℝ)
    (hB : ∀ t, ‖separated N E F K t‖ ≤ B) :
    ‖∑ e ∈ Icc 1 E, ∑ m ∈ Icc 1 F, if e*m ≤ N then K e m else 0‖ ≤ cost F*B := by
  rw [sharp_eq]
  apply (norm_integral_le_integral_norm _).trans
  rw [cost,← integral_mul_const]
  apply integral_mono
    (cont_integrable ((kernel_continuous F).mul (separated_continuous N E F K)).norm)
    (cont_integrable ((kernel_continuous F).norm.mul continuous_const))
  intro t
  change ‖kernel F t*separated N E F K t‖ ≤ ‖kernel F t‖*B
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hB t) (norm_nonneg _)

#print axioms phase_norm
#print axioms phase_integral
#print axioms comparison
#print axioms product_comparison
#print axioms sharp_eq
#print axioms cost_nonneg
#print axioms kernel_geometric
#print axioms kernel_decay
#print axioms kernel_norm_le
#print axioms cost_le
#print axioms sharp_bound
end XiPrime8845.PRZZSharpCutoff
