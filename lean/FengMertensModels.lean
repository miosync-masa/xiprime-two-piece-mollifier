import Zeta23.XiPrime.Coeff.PrimeSums
import BetaKernel

/-! Unconditional Mertens-Abel model sums. These are prime-weight models;
identification with the marked totient sum is a separate arithmetic estimate. -/
noncomputable section
open scoped BigOperators
open Finset Filter Topology
namespace XiPrime8845.FengMertensModels
set_option maxHeartbeats 1000000

def primes (X : ℝ) : Finset ℕ := (Ioc 0 ⌊Real.exp X⌋₊).filter Nat.Prime
def moment (b : ℕ) (X : ℝ) : ℝ := ∑ p ∈ primes X, (Real.log p)^b/(p:ℝ)
def smooth (b : ℕ) (X : ℝ) : ℝ :=
  ∑ p ∈ primes X, (Real.log p)^b/(p:ℝ)*(X-Real.log p)

theorem log_mem (X : ℝ) (p : ℕ) (hp : p ∈ primes X) :
    0 ≤ Real.log p ∧ Real.log p ≤ X :=
  ⟨Real.log_natCast_nonneg p,Zeta23.XiPrime.log_le_of_mem_Ioc_floor_exp (mem_filter.mp hp).1⟩

theorem moment_nonneg (b : ℕ) (X : ℝ) : 0 ≤ moment b X :=
  sum_nonneg fun p _ => div_nonneg (pow_nonneg (Real.log_natCast_nonneg p) _) (Nat.cast_nonneg p)

theorem moment_error (b : ℕ) (hb : 2 ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 0 ≤ X →
      |moment b X-X^b/b| ≤ C*(1+X)^(b-1) := by
  obtain ⟨C,hC⟩ := Zeta23.XiPrime.prime_logpow_sum b hb
  refine ⟨|C|,abs_nonneg _,fun X hX => (hC X hX).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (by linarith) _)

theorem normalized_error_zero (f : ℝ → ℝ) (d : ℕ) (hd : 0 < d) (c C : ℝ)
    (h : ∀ X : ℝ, 0 ≤ X → |f X-c*X^d| ≤ C*(1+X)^(d-1)) :
    Tendsto (fun X => f X/X^d-c) atTop (nhds 0) := by
  have hi := tendsto_inv_atTop_zero (𝕜 := ℝ)
  have hb : Tendsto (fun X : ℝ => C*(1+X⁻¹)^(d-1)*X⁻¹) atTop (nhds 0) := by
    simpa using (((tendsto_const_nhds (x := (1:ℝ))).add hi).pow (d-1)).const_mul C |>.mul hi
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun X => norm_nonneg _) _ hb
  filter_upwards [eventually_gt_atTop (0:ℝ)] with X hX
  rw [Real.norm_eq_abs]
  have he : f X/X^d-c = (f X-c*X^d)/X^d := by field_simp
  rw [he,abs_div,abs_of_pos (pow_pos hX _)]
  apply (div_le_div_of_nonneg_right (h X hX.le) (pow_nonneg hX.le _)).trans_eq
  have hd' : d = (d-1)+1 := by omega
  calc
    C*(1+X)^(d-1)/X^d = C*((1+X)/X)^(d-1)/X := by
      rw [hd',pow_succ,div_pow]
      simp only [Nat.add_sub_cancel]
      field_simp
    _ = C*(1+X⁻¹)^(d-1)*X⁻¹ := by rw [add_div,div_self hX.ne']; ring

theorem normalized_limit (f : ℝ → ℝ) (d : ℕ) (hd : 0 < d) (c C : ℝ)
    (h : ∀ X : ℝ, 0 ≤ X → |f X-c*X^d| ≤ C*(1+X)^(d-1)) :
    Tendsto (fun X => f X/X^d) atTop (nhds c) := by
  simpa using (normalized_error_zero f d hd c C h).add_const c

theorem moment_normalized (b : ℕ) (hb : 2 ≤ b) :
    Tendsto (fun X => moment b X/X^b) atTop (nhds (1/(b:ℝ))) := by
  obtain ⟨C,hC,h⟩ := moment_error b hb
  exact normalized_limit _ b (by omega) _ C (by intro X hX; simpa only [one_div,mul_comm,div_eq_mul_inv,mul_one] using h X hX)

theorem smooth_eq (b : ℕ) (X : ℝ) :
    smooth b X = X*moment b X-moment (b+1) X := by
  unfold smooth moment
  rw [mul_sum,← sum_sub_distrib]
  apply sum_congr rfl
  intros
  ring

theorem smooth_error (b : ℕ) (hb : 2 ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 0 ≤ X →
      |smooth b X-X^(b+1)/((b:ℝ)*(b+1))| ≤ C*(1+X)^b := by
  obtain ⟨C,hC,h⟩ := moment_error b hb
  obtain ⟨D,hD,k⟩ := moment_error (b+1) (by omega)
  refine ⟨C+D,add_nonneg hC hD,fun X hX => ?_⟩
  have hb0 : (b:ℝ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  have hb1 : (b:ℝ)+1 ≠ 0 := by positivity
  have he : smooth b X-X^(b+1)/((b:ℝ)*(b+1)) =
      X*(moment b X-X^b/b)-(moment (b+1) X-X^(b+1)/(b+1)) := by
    rw [smooth_eq]; field_simp; ring
  rw [he]
  apply (abs_sub _ _).trans
  rw [abs_mul,abs_of_nonneg hX]
  have hh := mul_le_mul_of_nonneg_left (h X hX) hX
  have hpow : X*(1+X)^(b-1) ≤ (1+X)^b := by
    conv_rhs => rw [show b = (b-1)+1 by omega,pow_succ]
    nlinarith [pow_nonneg (show 0≤1+X by linarith) (b-1)]
  have hscale := mul_le_mul_of_nonneg_left hpow hC
  have hk := k X hX
  simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] at hk
  nlinarith

theorem smooth_normalized (b : ℕ) (hb : 2 ≤ b) :
    Tendsto (fun X => smooth b X/X^(b+1)) atTop (nhds (1/((b:ℝ)*(b+1)))) := by
  obtain ⟨C,hC,h⟩ := smooth_error b hb
  apply normalized_limit _ (b+1) (by omega) _ C
  intro X hX
  simpa only [Nat.add_sub_cancel,one_div,div_eq_mul_inv,mul_comm,one_mul] using h X hX

/-- The actual single-prime Abel model, not merely its integral coefficient. -/
theorem diagonal_model_limit :
    Tendsto (fun X => smooth 4 X/X^5) atTop (nhds (1/20:ℝ)) := by
  convert smooth_normalized 4 (by norm_num) using 1
  norm_num

/-- Ordered nested prime model, including the coincident-prime diagonal for now. -/
def nested (X : ℝ) : ℝ :=
  ∑ p ∈ primes X, (Real.log p)^2/(p:ℝ)*smooth 2 (X-Real.log p)

def cubicModel (X : ℝ) : ℝ :=
  ∑ p ∈ primes X, (Real.log p)^2/(p:ℝ)*(X-Real.log p)^3/6

theorem cubicModel_eq (X : ℝ) :
    cubicModel X =
      (X^3*moment 2 X-3*X^2*moment 3 X+3*X*moment 4 X-moment 5 X)/6 := by
  unfold cubicModel moment
  simp only [mul_sum,← sum_sub_distrib,← sum_add_distrib,← sum_div]
  congr 1
  apply sum_congr rfl
  intros
  ring

theorem cubicModel_limit :
    Tendsto (fun X => cubicModel X/X^5) atTop (nhds (1/120:ℝ)) := by
  have h := (((moment_normalized 2 (by norm_num)).sub
    ((moment_normalized 3 (by norm_num)).const_mul 3)).add
    ((moment_normalized 4 (by norm_num)).const_mul 3)).sub
    (moment_normalized 5 (by norm_num))
  have hh := h.div_const 6
  norm_num at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with X hX
  rw [cubicModel_eq]
  field_simp

theorem moment_upper (b : ℕ) (hb : 2 ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 0 ≤ X → moment b X ≤ C*(1+X)^b := by
  obtain ⟨C,hC,h⟩ := moment_error b hb
  refine ⟨C+1,by positivity,fun X hX => ?_⟩
  have h1 := pow_le_pow_right₀ (show (1:ℝ)≤1+X by linarith) (show b-1≤b by omega)
  have h2 := pow_le_pow_left₀ hX (show X≤1+X by linarith) b
  have hb1 : (1:ℝ)≤b := by exact_mod_cast (show 1≤b by omega)
  have h3 := div_le_self (pow_nonneg hX b) hb1
  have h4 := (abs_le.mp (h X hX)).2
  nlinarith [mul_le_mul_of_nonneg_left h1 hC]

theorem nested_error :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 0 ≤ X →
      |nested X-cubicModel X| ≤ C*(1+X)^4 := by
  obtain ⟨C,hC,h⟩ := smooth_error 2 (by norm_num)
  obtain ⟨D,hD,k⟩ := moment_upper 2 (by norm_num)
  refine ⟨C*D,mul_nonneg hC hD,fun X hX => ?_⟩
  unfold nested cubicModel
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ p ∈ primes X, |(Real.log p)^2/(p:ℝ)*smooth 2 (X-Real.log p) -
        (Real.log p)^2/(p:ℝ)*(X-Real.log p)^3/6| := abs_sum_le_sum_abs _ _
    _ ≤ C*(1+X)^2*moment 2 X := by
      unfold moment
      rw [mul_sum]
      apply sum_le_sum
      intro p hp
      have hl := log_mem X p hp
      have hv : 0 ≤ X-Real.log p := by linarith
      have he := h (X-Real.log p) hv
      norm_num at he
      have ha : 0 ≤ (Real.log p)^2/(p:ℝ) := by positivity
      have hid : (Real.log p)^2/(p:ℝ)*smooth 2 (X-Real.log p) -
          (Real.log p)^2/(p:ℝ)*(X-Real.log p)^3/6 =
          ((Real.log p)^2/(p:ℝ))*(smooth 2 (X-Real.log p)-(X-Real.log p)^3/6) := by ring
      rw [hid,abs_mul,abs_of_nonneg ha]
      have hpw := pow_le_pow_left₀ (show 0≤1+(X-Real.log p) by linarith)
        (show 1+(X-Real.log p)≤1+X by linarith) 2
      have hh := mul_le_mul_of_nonneg_left (he.trans (mul_le_mul_of_nonneg_left hpw hC)) ha
      convert hh using 1
      ring
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (k X hX) (mul_nonneg hC (sq_nonneg (1+X)))
      nlinarith [hh]

theorem nested_model_limit :
    Tendsto (fun X => nested X/X^5) atTop (nhds (1/120:ℝ)) := by
  obtain ⟨C,hC,h⟩ := nested_error
  have he := normalized_error_zero (fun X => nested X-cubicModel X) 5 (by norm_num) 0 C
    (by intro X hX; simpa using h X hX)
  have hh := he.add cubicModel_limit
  simpa only [sub_zero,zero_add,sub_div,sub_add_cancel] using hh

theorem model_total_limit :
    Tendsto (fun X => (smooth 4 X+nested X)/X^5) atTop (nhds (7/120:ℝ)) := by
  have h := diagonal_model_limit.add nested_model_limit
  norm_num at h
  simpa only [add_div] using h

#print axioms moment_error
#print axioms normalized_error_zero
#print axioms moment_normalized
#print axioms smooth_error
#print axioms diagonal_model_limit
#print axioms cubicModel_limit
#print axioms nested_error
#print axioms nested_model_limit
#print axioms model_total_limit
end XiPrime8845.FengMertensModels

