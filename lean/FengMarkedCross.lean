import FengMarkedDiagonal

/-! Arithmetic comparison of the ordered marked cross term with its
Mertens-Abel prime model. Coincident primes are accounted for separately. -/
noncomputable section
open scoped BigOperators
open Finset Filter Topology
namespace XiPrime8845.FengMarkedCross
open TotientCoprime FengMarkedTail FengMertensModels FengMarkedDiagonal
set_option maxHeartbeats 1500000

theorem reciprocal_prime_bounds (p : ℕ) (hp : p.Prime) :
    0 ≤ 1/(p-1:ℝ)-1/(p:ℝ) ∧
    1/(p-1:ℝ) ≤ 2/(p:ℝ) ∧
    1/(p-1:ℝ)-1/(p:ℝ) ≤ 2/(p:ℝ)^2 := by
  have hp2 : (2:ℝ)≤p := by exact_mod_cast hp.two_le
  have hp0 : (0:ℝ)<p := by linarith
  have hpm : (0:ℝ)<p-1 := by linarith
  have hi : 1/(p-1:ℝ) ≤ 2/(p:ℝ) := by
    apply (div_le_div_iff₀ hpm hp0).mpr; linarith
  have he : 1/(p-1:ℝ)-1/(p:ℝ) = (1/(p-1:ℝ))/(p:ℝ) := by field_simp; ring
  refine ⟨?_,hi,?_⟩
  · rw [he]; positivity
  · rw [he]
    simpa only [div_div,pow_two] using div_le_div_of_nonneg_right hi hp0.le

def pairReciprocal (p q : ℕ) : ℝ :=
  1/(p:ℝ)^2/(q:ℝ)+1/(p:ℝ)/(q:ℝ)^2

theorem pair_reciprocal_bounds (p q : ℕ) (hp : p.Prime) (hq : q.Prime) :
    1/((p-1:ℝ)*(q-1:ℝ)) ≤ 4/((p:ℝ)*q) ∧
    0 ≤ 1/((p-1:ℝ)*(q-1:ℝ))-1/((p:ℝ)*q) ∧
    1/((p-1:ℝ)*(q-1:ℝ))-1/((p:ℝ)*q) ≤ 4*pairReciprocal p q ∧
    ((p-1:ℝ)⁻¹+(q-1:ℝ)⁻¹)/((p-1:ℝ)*(q-1:ℝ)) ≤ 8*pairReciprocal p q := by
  have hp0 : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hq0 : (0:ℝ)<q := by exact_mod_cast hq.pos
  have hp1 : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  have hq1 : (1:ℝ)<q := by exact_mod_cast hq.one_lt
  have hpb := reciprocal_prime_bounds p hp
  have hqb := reciprocal_prime_bounds q hq
  have hprod := mul_le_mul hpb.2.1 hqb.2.1 (by positivity : (0:ℝ)≤1/(q-1:ℝ)) (by positivity : (0:ℝ)≤2/(p:ℝ))
  have hprod' : 1/((p-1:ℝ)*(q-1:ℝ)) ≤ 4/((p:ℝ)*q) := by
    simpa only [div_mul_div_comm,one_mul,show (2:ℝ)*2=4 by norm_num] using hprod
  have he : 1/((p-1:ℝ)*(q-1:ℝ))-1/((p:ℝ)*q) =
      (1/(p-1:ℝ)-1/(p:ℝ))*(1/(q-1:ℝ))+
        (1/(p:ℝ))*(1/(q-1:ℝ)-1/(q:ℝ)) := by
    simp only [div_eq_mul_inv,mul_inv_rev]; ring
  refine ⟨hprod',?_,?_,?_⟩
  · rw [he]; exact add_nonneg (mul_nonneg hpb.1 (by positivity)) (mul_nonneg (by positivity) hqb.1)
  · rw [he]
    have h1 := mul_le_mul hpb.2.2 hqb.2.1 (by positivity : (0:ℝ)≤1/(q-1:ℝ)) (by positivity : (0:ℝ)≤2/(p:ℝ)^2)
    have h2 := mul_le_mul_of_nonneg_left hqb.2.2 (show (0:ℝ)≤1/(p:ℝ) by positivity)
    unfold pairReciprocal
    have hz : 0 ≤ 1/(p:ℝ)/(q:ℝ)^2 := by positivity
    simp only [div_eq_mul_inv,← inv_pow] at h1 h2 hz ⊢
    nlinarith only [h1,h2,hz]
  · have hs : (p-1:ℝ)⁻¹+(q-1:ℝ)⁻¹ ≤ 2/(p:ℝ)+2/(q:ℝ) := by
      simpa only [one_div] using add_le_add hpb.2.1 hqb.2.1
    have hm := mul_le_mul hs hprod' (by positivity : (0:ℝ)≤1/((p-1:ℝ)*(q-1:ℝ)))
      (by positivity : (0:ℝ)≤2/(p:ℝ)+2/(q:ℝ))
    unfold pairReciprocal
    simp only [div_eq_mul_inv,mul_inv_rev,← inv_pow] at hm ⊢
    nlinarith only [hm]

def cutoffLog (X : ℝ) (p q : ℕ) : ℝ := max (X-Real.log p-Real.log q) 0

theorem total_pair_error (X : ℝ) (p q : ℕ) (hp : p.Prime) (hq : q.Prime) :
    |total (⌊Real.exp X⌋₊/(p*q))-cutoffLog X p q| ≤ TotientHarmonic.errorConstant := by
  have hp0 : (p:ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hq0 : (q:ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
  rw [Zeta23.XiPrime.floor_exp_div X (Nat.mul_pos hp.pos hq.pos),Nat.cast_mul,Real.log_mul hp0 hq0]
  unfold cutoffLog
  rw [← sub_sub]
  by_cases hv : 0 ≤ X-Real.log p-Real.log q
  · rw [max_eq_left hv,total_eq]
    simpa only [Real.log_exp] using TotientHarmonic.summatory_log_bound
      (Real.exp (X-Real.log p-Real.log q)) (Real.one_le_exp_iff.mpr hv)
  · rw [max_eq_right (le_of_not_ge hv),Nat.floor_eq_zero.mpr
      (Real.exp_lt_one_iff.mpr (lt_of_not_ge hv))]
    simpa [total] using TotientHarmonic.errorConstant_nonneg

theorem cross_point_error (X : ℝ) (hX : 0 ≤ X) (p q : ℕ)
    (hp : p ∈ primes X) (hq : q ∈ primes X) :
    |restricted (⌊Real.exp X⌋₊/(p*q)) (p*q)/((p-1:ℝ)*(q-1:ℝ))-
      cutoffLog X p q/((p:ℝ)*q)| ≤
      4*TotientHarmonic.errorConstant/((p:ℝ)*q)+
        (12*X+8*TotientHarmonic.errorConstant)*pairReciprocal p q := by
  let E := TotientHarmonic.errorConstant
  let v := cutoffLog X p q
  let N := ⌊Real.exp X⌋₊/(p*q)
  have hE : 0 ≤ E := TotientHarmonic.errorConstant_nonneg
  have hpp := (mem_filter.mp hp).2
  have hqq := (mem_filter.mp hq).2
  have hp1 : (1:ℝ)<p := by exact_mod_cast hpp.one_lt
  have hq1 : (1:ℝ)<q := by exact_mod_cast hqq.one_lt
  have hv0 : 0 ≤ v := le_max_right _ _
  have hvX : v ≤ X := max_le (by linarith [(log_mem X p hp).1,(log_mem X q hq).1]) hX
  have ht := total_pair_error X p q hpp hqq
  have htn : total N ≤ X+E := by
    have := (abs_le.mp ht).2
    dsimp only [N,E,v] at *
    linarith
  have hr0 : 0 ≤ total N-restricted N (p*q) := sub_nonneg.mpr (restricted_le_total _ _)
  have hr : total N-restricted N (p*q) ≤ (X+E)*((p-1:ℝ)⁻¹+(q-1:ℝ)⁻¹) := by
    apply (product_exclusion N p q).trans
    have h1 := (prime_exclusion_bound N p hpp).2.trans
      (div_le_div_of_nonneg_right ((total_mono (Nat.div_le_self _ _)).trans htn) (by linarith))
    have h2 := (prime_exclusion_bound N q hqq).2.trans
      (div_le_div_of_nonneg_right ((total_mono (Nat.div_le_self _ _)).trans htn) (by linarith))
    simpa only [div_eq_mul_inv,mul_add] using add_le_add h1 h2
  have hrv : |restricted N (p*q)-v| ≤ E+(X+E)*((p-1:ℝ)⁻¹+(q-1:ℝ)⁻¹) := by
    have h := abs_sub_le (restricted N (p*q)) (total N) v
    rw [abs_sub_comm (restricted N (p*q)) (total N),abs_of_nonneg hr0] at h
    change |total N-v| ≤ E at ht
    linarith
  have hb := pair_reciprocal_bounds p q hpp hqq
  have hden : 0 < (p-1:ℝ)*(q-1:ℝ) := mul_pos (by linarith) (by linarith)
  have he : restricted N (p*q)/((p-1:ℝ)*(q-1:ℝ))-v/((p:ℝ)*q) =
      (restricted N (p*q)-v)/((p-1:ℝ)*(q-1:ℝ))+
      v*(1/((p-1:ℝ)*(q-1:ℝ))-1/((p:ℝ)*q)) := by ring
  change |restricted N (p*q)/((p-1:ℝ)*(q-1:ℝ))-v/((p:ℝ)*q)| ≤ _
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_div,abs_of_pos hden,abs_mul,abs_of_nonneg hv0,abs_of_nonneg hb.2.1]
  have h1 := div_le_div_of_nonneg_right hrv hden.le
  have h2 := mul_le_mul hvX hb.2.2.1 hb.2.1 hX
  have h3 := mul_le_mul_of_nonneg_left hb.1 hE
  have h4 := mul_le_mul_of_nonneg_left hb.2.2.2 (show 0≤X+E by positivity)
  dsimp only [E] at h1 h2 h3 h4
  simp only [div_eq_mul_inv,mul_inv_rev] at h1 h2 h3 h4 ⊢
  nlinarith only [h1,h2,h3,h4]

#print axioms reciprocal_prime_bounds
#print axioms pair_reciprocal_bounds
#print axioms total_pair_error
#print axioms cross_point_error
end XiPrime8845.FengMarkedCross

