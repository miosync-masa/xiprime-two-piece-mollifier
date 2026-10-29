import FengMarkedTail
import FengMertensModels

/-! The actual marked diagonal, including all non-squarefree prime powers,
has leading coefficient 1/20. The ordered cross term is not identified here. -/
noncomputable section
open scoped BigOperators
open Finset Filter Topology
namespace XiPrime8845.FengMarkedDiagonal
open TotientCoprime FengMarkedTail FengMertensModels
set_option maxHeartbeats 1000000

theorem shifted_total_error (X : ℝ) (p : ℕ) (hp : p ∈ primes X) :
    |total (⌊Real.exp X⌋₊/p)-(X-Real.log p)| ≤ TotientHarmonic.errorConstant := by
  have hp0 := (mem_Ioc.mp (mem_filter.mp hp).1).1
  rw [Zeta23.XiPrime.floor_exp_div X hp0,total_eq]
  have h := TotientHarmonic.summatory_log_bound (Real.exp (X-Real.log p))
    (Real.one_le_exp_iff.mpr (sub_nonneg.mpr (log_mem X p hp).2))
  simpa only [Real.log_exp] using h

theorem head_point_error (X : ℝ) (hX : 0 ≤ X) (p : ℕ) (hp : p ∈ primes X) :
    |restricted (⌊Real.exp X⌋₊/p) p/(p-1:ℝ)-(X-Real.log p)/(p:ℝ)| ≤
      2*TotientHarmonic.errorConstant/(p:ℝ) +
        (6*X+4*TotientHarmonic.errorConstant)/(p:ℝ)^2 := by
  let E := TotientHarmonic.errorConstant
  have hE : 0 ≤ E := TotientHarmonic.errorConstant_nonneg
  have hpp := (mem_filter.mp hp).2
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hpp.two_le
  have hp0 : (0:ℝ) < p := by linarith
  have hpm : (0:ℝ) < p-1 := by linarith
  have hv := log_mem X p hp
  have ht := shifted_total_error X p hp
  have htot : total (⌊Real.exp X⌋₊/p) ≤ X+E := by
    have hh := (abs_le.mp ht).2
    dsimp [E]
    linarith
  have hrem := prime_exclusion_bound (⌊Real.exp X⌋₊/p) p hpp
  have hrem' : total (⌊Real.exp X⌋₊/p)-restricted (⌊Real.exp X⌋₊/p) p ≤ (X+E)/(p-1:ℝ) :=
    hrem.2.trans (div_le_div_of_nonneg_right
      ((total_mono (Nat.div_le_self _ _)).trans htot) hpm.le)
  have hid : restricted (⌊Real.exp X⌋₊/p) p/(p-1:ℝ)-(X-Real.log p)/(p:ℝ) =
      -(total (⌊Real.exp X⌋₊/p)-restricted (⌊Real.exp X⌋₊/p) p)/(p-1:ℝ) +
      (total (⌊Real.exp X⌋₊/p)-(X-Real.log p))/(p-1:ℝ) +
      (X-Real.log p)/((p:ℝ)*(p-1)) := by
    field_simp; ring
  have htri := (abs_add_le
    (-(total (⌊Real.exp X⌋₊/p)-restricted (⌊Real.exp X⌋₊/p) p)/(p-1:ℝ) +
      (total (⌊Real.exp X⌋₊/p)-(X-Real.log p))/(p-1:ℝ))
    ((X-Real.log p)/((p:ℝ)*(p-1)))).trans
      (add_le_add (abs_add_le _ _) le_rfl)
  rw [hid]
  apply htri.trans
  rw [abs_div,abs_neg,abs_of_nonneg hrem.1,abs_of_pos hpm,
    abs_div,abs_of_pos hpm,abs_div,abs_of_nonneg (sub_nonneg.mpr hv.2),
    abs_of_pos (mul_pos hp0 hpm)]
  have hfirst := div_le_div_of_nonneg_right hrem' hpm.le
  have hsecond := div_le_div_of_nonneg_right ht hpm.le
  have hthird := div_le_div_of_nonneg_right (show X-Real.log p ≤ X by linarith)
    (mul_nonneg hp0.le hpm.le)
  apply (add_le_add (add_le_add hfirst hsecond) hthird).trans
  change (X+E)/(p-1:ℝ)/(p-1:ℝ)+E/(p-1:ℝ)+X/((p:ℝ)*(p-1)) ≤ _
  have hi : 1/(p-1:ℝ) ≤ 2/(p:ℝ) := by
    apply (div_le_div_iff₀ hpm hp0).mpr
    linarith
  have hs := mul_self_le_mul_self (by positivity : (0:ℝ) ≤ 1/(p-1:ℝ)) hi
  have ha := mul_le_mul_of_nonneg_left hs (show 0 ≤ X+E by positivity)
  have hb := mul_le_mul_of_nonneg_left hi hE
  have hc := mul_le_mul_of_nonneg_left hi (div_nonneg hX hp0.le)
  dsimp only [E] at ha hb ⊢
  simp only [div_eq_mul_inv,mul_inv_rev,← inv_pow] at ha hb hc ⊢
  nlinarith only [ha,hb,hc]

theorem head_error (X : ℝ) (hX : 0 ≤ X) :
    |primeHead ⌊Real.exp X⌋₊-smooth 4 X| ≤
      2*TotientHarmonic.errorConstant*moment 4 X+
        (6*X+4*TotientHarmonic.errorConstant)*X^2*Zeta23.XiPrime.Cdef := by
  have he : Icc 1 ⌊Real.exp X⌋₊ = Ioc 0 ⌊Real.exp X⌋₊ := by
    ext n; simp only [mem_Icc,mem_Ioc]; omega
  unfold primeHead smooth
  rw [he]
  change |(∑ p ∈ primes X, _) - ∑ p ∈ primes X, _| ≤ _
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ p ∈ primes X, |(Real.log p)^4*(restricted (⌊Real.exp X⌋₊/p) p/(p-1:ℝ)) -
        (Real.log p)^4/(p:ℝ)*(X-Real.log p)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ primes X, (Real.log p)^4*
        (2*TotientHarmonic.errorConstant/(p:ℝ)+(6*X+4*TotientHarmonic.errorConstant)/(p:ℝ)^2) := by
      apply sum_le_sum
      intro p hp
      have hid : (Real.log p)^4*(restricted (⌊Real.exp X⌋₊/p) p/(p-1:ℝ)) -
          (Real.log p)^4/(p:ℝ)*(X-Real.log p) =
          (Real.log p)^4*(restricted (⌊Real.exp X⌋₊/p) p/(p-1:ℝ)-(X-Real.log p)/(p:ℝ)) := by ring
      rw [hid,abs_mul,abs_of_nonneg (by positivity : 0≤(Real.log p)^4)]
      exact mul_le_mul_of_nonneg_left (head_point_error X hX p hp) (by positivity)
    _ = 2*TotientHarmonic.errorConstant*moment 4 X+
        (6*X+4*TotientHarmonic.errorConstant)*
          ∑ p ∈ primes X, (Real.log p)^4/(p:ℝ)^2 := by
      unfold moment
      simp only [mul_sum,← sum_add_distrib]
      apply sum_congr rfl; intros; ring
    _ ≤ _ := by
      have h := prime_fourth_square_bound X hX
      rw [he] at h
      have hh := mul_le_mul_of_nonneg_left h (show 0≤6*X+4*TotientHarmonic.errorConstant by
        have := TotientHarmonic.errorConstant_nonneg; positivity)
      change _ ≤ (6*X+4*TotientHarmonic.errorConstant)*(X^2*Zeta23.XiPrime.Cdef) at hh
      change (6*X+4*TotientHarmonic.errorConstant)*(∑ p ∈ primes X, (Real.log p)^4/(p:ℝ)^2) ≤ _ at hh
      nlinarith

theorem head_error_polynomial :
    ∃ C : ℝ, ∀ X : ℝ, 0 ≤ X →
      |primeHead ⌊Real.exp X⌋₊-smooth 4 X| ≤ C*(1+X)^4 := by
  obtain ⟨D,hD,k⟩ := moment_upper 4 (by norm_num)
  let E := TotientHarmonic.errorConstant
  have hE : 0 ≤ E := TotientHarmonic.errorConstant_nonneg
  refine ⟨2*E*D+(6+4*E)*Zeta23.XiPrime.Cdef,fun X hX => ?_⟩
  apply (head_error X hX).trans
  have h1 := mul_le_mul_of_nonneg_left (k X hX) (show 0≤2*E by positivity)
  have h2 : (6*X+4*E)*X^2 ≤ (6+4*E)*(1+X)^4 := by
    calc
      _ ≤ ((6+4*E)*(1+X))*(1+X)^2 := by
        gcongr <;> nlinarith
      _ ≤ (6+4*E)*(1+X)^4 := by
        have hh := pow_le_pow_right₀ (show (1:ℝ)≤1+X by linarith) (show 3≤4 by omega)
        have hm := mul_le_mul_of_nonneg_left hh (show 0≤6+4*E by positivity)
        nlinarith
  have h3 := mul_le_mul_of_nonneg_right h2 (show 0≤Zeta23.XiPrime.Cdef by norm_num [Zeta23.XiPrime.Cdef])
  dsimp only [E] at h1 h3 ⊢
  nlinarith [h1,h3]

theorem primeHead_limit :
    Tendsto (fun X => primeHead ⌊Real.exp X⌋₊/X^5) atTop (nhds (1/20:ℝ)) := by
  obtain ⟨C,h⟩ := head_error_polynomial
  have he := normalized_error_zero (fun X => primeHead ⌊Real.exp X⌋₊-smooth 4 X) 5
    (by norm_num) 0 C (by intro X hX; simpa using h X hX)
  simpa only [sub_zero,zero_add,sub_div,sub_add_cancel] using he.add diagonal_model_limit

theorem diagonal_limit :
    Tendsto (fun X => FengMarkedDecomposition.diagonal ⌊Real.exp X⌋₊/X^5)
      atTop (nhds (1/20:ℝ)) := by
  simpa only [diagonal_split,add_div,add_zero] using primeHead_limit.add higherPowers_normalized

#print axioms shifted_total_error
#print axioms head_point_error
#print axioms head_error
#print axioms head_error_polynomial
#print axioms primeHead_limit
#print axioms diagonal_limit
end XiPrime8845.FengMarkedDiagonal

