import FengSharedApproximation
import FengSharedBounds

/-! The positive p-power tail is small; the a=0 marked-prime head is retained.
All bounds are uniform in growing g and include the cutoff endpoint. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Finset Filter Topology
namespace XiPrime8845.FengSharedTail
open FengSharedApproximation FengSharedBounds FengResidual FengAtG CoprimeShift
open SupportTail CoprimeEndpoint ShiftWeights
set_option maxHeartbeats 1000000

theorem residual_prime_support (g p q : ℕ) (_hg : g ≠ 0)
    (hp : p ∈ g.primeFactors) (hq : q.Prime) :
    q ∣ (g/p^(g.factorization p))*p ↔ q ∣ g := by
  constructor
  · intro h
    rcases hq.dvd_mul.mp h with h | h
    · exact h.trans (Nat.ordCompl_dvd g p)
    · exact h.trans (Nat.dvd_of_mem_primeFactors hp)
  · intro h
    have he := Nat.ordProj_mul_ordCompl_eq_self g p
    rw [← he] at h
    rcases hq.dvd_mul.mp h with h | h
    · exact dvd_mul_of_dvd_right (hq.dvd_of_dvd_pow h) _
    · exact dvd_mul_of_dvd_left h p

theorem residual_coprime (g p n : ℕ) (hg : g ≠ 0) (hp : p ∈ g.primeFactors) :
    n.Coprime ((g/p^(g.factorization p))*p) ↔ n.Coprime g := by
  rw [← not_iff_not]
  simp only [Nat.Prime.not_coprime_iff_dvd]
  constructor <;> rintro ⟨q,hq,hqn,hqg⟩
  · exact ⟨q,hq,hqn,(residual_prime_support g p q hg hp hq).mp hqg⟩
  · exact ⟨q,hq,hqn,(residual_prime_support g p q hg hp hq).mpr hqg⟩

theorem residual_euler_eq (g p : ℕ) (hg : g ≠ 0) (hp : p ∈ g.primeFactors) :
    eulerMass ((g/p^(g.factorization p))*p) 0 = eulerMass g 0 := by
  apply le_antisymm (residual_modulus_euler g p hg hp)
  apply euler_mono_support g _ hg
    (mul_ne_zero (Nat.ordCompl_pos p hg).ne' (Nat.prime_of_mem_primeFactors hp).ne_zero)
  intro q hq h
  exact (residual_prime_support g p q hg hp hq).mpr h

theorem residual_coprimeScaled (N g p : ℕ) (hg : g ≠ 0) (hp : p ∈ g.primeFactors)
    (L u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) :
    coprimeScaled N ((g/p^(g.factorization p))*p) L u θ P A =
      coprimeScaled N g L u θ P A := by
  simp only [coprimeScaled, coprimeInner, residual_coprime g p _ hg hp]

def mark (g : ℕ) (L : ℝ) : ℂ :=
  ∑ p ∈ g.primeFactors, (Real.log p:ℂ)^2/(L:ℂ)^2 * (μ (g/p^(g.factorization p)):ℂ)

theorem transform_split (N g : ℕ) (L : ℝ) (A : ℂ) (X : ℕ → ℕ → ℂ) :
    transform N g L A X =
      (∑ p ∈ g.primeFactors, (Real.log p:ℂ)^2/(L:ℂ)^2 *
        (μ (g/p^(g.factorization p)):ℂ)*X p 0) +
      ∑ p ∈ g.primeFactors, (Real.log p:ℂ)^2/(L:ℂ)^2 *
        (μ (g/p^(g.factorization p)):ℂ)*
        ∑ a ∈ range (Nat.log p N), supportFactor (p^(a+1)) L A*X p (a+1) := by
  simp only [transform, sum_range_succ', pow_zero, supportFactor, Real.log_one,
    Complex.ofReal_zero, zero_div, mul_zero, Complex.exp_zero,
    Nat.cast_one, div_one, one_mul, mul_add, sum_add_distrib]
  ring

theorem reciprocal_positive_powers (p M : ℕ) (hp : p.Prime) :
    (∑ a ∈ range M, 1/((p^(a+1):ℕ):ℝ)) ≤ 2/(p:ℝ) := by
  have he : (∑ a ∈ range M, 1/((p^(a+1):ℕ):ℝ)) =
      (∑ a ∈ range M, 1/((p^a:ℕ):ℝ))/(p:ℝ) := by
    rw [sum_div]; apply sum_congr rfl; intros
    simp only [pow_succ, Nat.cast_mul]; ring
  rw [he]
  exact div_le_div_of_nonneg_right (reciprocal_power_sum p M hp) (Nat.cast_nonneg p)

theorem prime_log_square_div_sum (g : ℕ) (hg : g ≠ 0) :
    (∑ p ∈ g.primeFactors, (Real.log p)^2/(p:ℝ)) ≤ Real.log g := by
  apply le_trans _ (ShiftedEulerUniform.prime_log_sum_le g hg)
  apply sum_le_sum
  intro p hp
  have hp0 : (0:ℝ)<p := by exact_mod_cast Nat.pos_of_mem_primeFactors hp
  have hl0 := Real.log_nonneg (show (1:ℝ)≤p by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le)
  have hl := Real.log_le_sub_one_of_pos hp0
  apply (div_le_iff₀ hp0).mpr
  nlinarith

theorem positive_support_sum (p : ℕ) (hp : p.Prime) (L u C U : ℝ) (A : ℂ)
    (hL : 0 < L) (hu : u ∈ Set.Icc 0 U) (hA : ‖A‖ ≤ C) :
    (∑ a ∈ range (Nat.log p ⌊Real.exp (L*u)⌋₊), ‖supportFactor (p^(a+1)) L A‖) ≤
      2*Real.exp (C*U)/(p:ℝ) := by
  calc
    _ ≤ ∑ a ∈ range (Nat.log p ⌊Real.exp (L*u)⌋₊), Real.exp (C*U)/((p^(a+1):ℕ):ℝ) := by
      apply sum_le_sum
      intro a ha
      have hr := power_cutoff_mem p (a+1) hp L u hL hu.1 (mem_range.mpr (by have := mem_range.mp ha; omega))
      have hr1 : (1:ℝ)≤(p^(a+1):ℕ) := by exact_mod_cast (mem_Icc.mp hr).1
      have hlog := (Real.log_le_iff_le_exp (by positivity : (0:ℝ)<(p^(a+1):ℕ))).mpr
        ((Nat.le_floor_iff (Real.exp_pos _).le).mp (mem_Icc.mp hr).2)
      have ht := normalized_log_mem ((p^(a+1):ℕ):ℝ) L u hr1 hL hlog
      have hb := exp_weight_bound A (Real.log (p^(a+1):ℕ)/L) C U hA
        (by rw [abs_of_nonneg ht.1]; exact ht.2.trans hu.2)
      rw [supportFactor,norm_div,Complex.norm_natCast]
      exact div_le_div_of_nonneg_right hb (Nat.cast_nonneg _)
    _ = Real.exp (C*U)*(∑ a ∈ range (Nat.log p ⌊Real.exp (L*u)⌋₊),1/((p^(a+1):ℕ):ℝ)) := by
      rw [mul_sum]; apply sum_congr rfl; intros; ring
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (reciprocal_positive_powers p (Nat.log p ⌊Real.exp (L*u)⌋₊) hp) (Real.exp_pos (C*U)).le
      exact h.trans_eq (by ring)

theorem mark_bound (g : ℕ) (hg : g ≠ 0) (L V : ℝ) (hL : 0 < L)
    (ht : |Real.log g/L| ≤ V) : ‖mark g L‖ ≤ V^2 := by
  have hm (p : ℕ) : ‖(μ (g/p^(g.factorization p)):ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_intCast] using (show |(μ (g/p^(g.factorization p)):ℝ)| ≤ 1 by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=g/p^(g.factorization p)))
  have hb : ‖mark g L‖ ≤ (∑ p ∈ g.primeFactors, (Real.log p)^2)/L^2 := by
    apply (norm_sum_le _ _).trans
    rw [sum_div]
    apply sum_le_sum
    intro p hp
    rw [norm_mul,norm_div,norm_pow,norm_pow,Complex.norm_real,Complex.norm_real,
      Real.norm_eq_abs,Real.norm_eq_abs,sq_abs,abs_of_pos hL]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hm p) (by positivity : 0≤(Real.log p)^2/L^2)
  apply hb.trans
  have hh := div_le_div_of_nonneg_right (prime_log_square_sum g hg) (sq_nonneg L)
  have hv := pow_le_pow_left₀ (abs_nonneg (Real.log g/L)) ht 2
  rw [sq_abs,div_pow] at hv
  exact hh.trans hv

theorem transform_tail_bound (g : ℕ) (hg : g ≠ 0) (L u C U V D : ℝ) (A : ℂ)
    (X : ℕ → ℕ → ℂ) (hL : 0 < L) (hu : u ∈ Set.Icc 0 U)
    (ht : |Real.log g/L| ≤ V) (hD : 0 ≤ D) (hA : ‖A‖ ≤ C)
    (hX : ∀ p ∈ g.primeFactors, ∀ a ∈ range (Nat.log p ⌊Real.exp (L*u)⌋₊),
      ‖X p (a+1)‖ ≤ D*eulerMass g 0) :
    ‖transform ⌊Real.exp (L*u)⌋₊ g L A X -
      ∑ p ∈ g.primeFactors, (Real.log p:ℂ)^2/(L:ℂ)^2 *
        (μ (g/p^(g.factorization p)):ℂ)*X p 0‖ ≤
      (2*Real.exp (C*U)*D*V/L)*eulerMass g 0 := by
  rw [transform_split,add_sub_cancel_left]
  have hE := euler_nonneg g hg
  have hb : ‖∑ p ∈ g.primeFactors, (Real.log p:ℂ)^2/(L:ℂ)^2 *
      (μ (g/p^(g.factorization p)):ℂ)*
      ∑ a ∈ range (Nat.log p ⌊Real.exp (L*u)⌋₊), supportFactor (p^(a+1)) L A*X p (a+1)‖ ≤
      ((2*Real.exp (C*U)*D*eulerMass g 0)/L^2)*
        ∑ p ∈ g.primeFactors, (Real.log p)^2/(p:ℝ) := by
    apply (norm_sum_le _ _).trans
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    have hm : ‖(μ (g/p^(g.factorization p)):ℂ)‖ ≤ 1 := by
      simpa only [Complex.norm_intCast] using (show |(μ (g/p^(g.factorization p)):ℝ)| ≤ 1 by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=g/p^(g.factorization p)))
    have hi : ‖∑ a ∈ range (Nat.log p ⌊Real.exp (L*u)⌋₊), supportFactor (p^(a+1)) L A*X p (a+1)‖ ≤
        (2*Real.exp (C*U)/(p:ℝ))*(D*eulerMass g 0) := by
      apply (norm_sum_le _ _).trans
      calc
        _ ≤ ∑ a ∈ range (Nat.log p ⌊Real.exp (L*u)⌋₊), ‖supportFactor (p^(a+1)) L A‖*(D*eulerMass g 0) := by
          apply sum_le_sum; intro a ha; rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hX p hp a ha) (norm_nonneg _)
        _ = (∑ a ∈ range (Nat.log p ⌊Real.exp (L*u)⌋₊), ‖supportFactor (p^(a+1)) L A‖)*(D*eulerMass g 0) := (sum_mul ..).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (positive_support_sum p (Nat.prime_of_mem_primeFactors hp) L u C U A hL hu hA) (mul_nonneg hD hE)
    rw [norm_mul,norm_mul,norm_div,norm_pow,norm_pow,Complex.norm_real,Complex.norm_real,
      Real.norm_eq_abs,Real.norm_eq_abs,sq_abs,abs_of_pos hL]
    have hm' := mul_le_mul_of_nonneg_left hm (by positivity : 0≤(Real.log p)^2/L^2)
    simp only [mul_one] at hm'
    have hh := mul_le_mul hm' hi (norm_nonneg _) (by positivity : 0≤(Real.log p)^2/L^2)
    convert hh using 1; ring
  apply hb.trans
  have hh := mul_le_mul_of_nonneg_left (prime_log_square_div_sum g hg)
    (show 0≤(2*Real.exp (C*U)*D*eulerMass g 0)/L^2 by positivity)
  have hlog : Real.log g ≤ V*L := (div_le_iff₀ hL).mp ((le_abs_self _).trans ht)
  have hz := mul_le_mul_of_nonneg_left hlog
    (show 0≤(2*Real.exp (C*U)*D*eulerMass g 0)/L^2 by positivity)
  apply hh.trans
  convert hz using 1; field_simp

theorem actual_head (N g : ℕ) (hg : g ≠ 0) (L u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) :
    (∑ p ∈ g.primeFactors, (Real.log p:ℂ)^2/(L:ℂ)^2 *
      (μ (g/p^(g.factorization p)):ℂ)*actualArray N g L u θ P A p 0) =
      mark g L * coprimeScaled N g L u θ P A := by
  rw [mark,sum_mul]
  apply sum_congr rfl
  intro p hp
  simp only [actualArray,pow_zero,Nat.div_one,Real.log_one,zero_div,sub_zero,
    residual_coprimeScaled N g p hg hp]

theorem main_head (g : ℕ) (hg : g ≠ 0) (L u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) :
    (∑ p ∈ g.primeFactors, (Real.log p:ℂ)^2/(L:ℂ)^2 *
      (μ (g/p^(g.factorization p)):ℂ)*mainArray g L u θ P A p 0) =
      mark g L * CoprimeEulerCompletion.zeroEulerMain g u θ P A := by
  rw [mark,sum_mul]
  apply sum_congr rfl
  intro p hp
  simp only [mainArray,pow_zero,Real.log_one,zero_div,sub_zero,
    CoprimeEulerCompletion.zeroEulerMain,residual_euler_eq g p hg hp]

theorem shared_head_error (P : Polynomial ℂ) (hP : P.eval 0 = 0)
    (θ C U V : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hU : 0 ≤ U) (hV : 0 ≤ V) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ L : ℝ, 0 < L → ∀ g : ℕ, g ≠ 0 →
      |Real.log g/L| ≤ V → ∀ u ∈ Set.Icc 0 U, ∀ A : ℂ, ‖A‖ ≤ C →
        ‖FengAtG.sharedBlock ⌊Real.exp (L*u)⌋₊ g L u θ P A -
          mark g L * CoprimeApproximation.actual L g u θ P A‖ ≤
            (D/L)*eulerMass g 0 := by
  obtain ⟨K,hK,hbound⟩ := ShiftedEndpoint.absoluteError_bounded
  let B := ShiftedEndpoint.coprimeCap P θ C U K
  have hB : 0 ≤ B := mul_nonneg (Real.exp_pos _).le
    (ShiftedEndpoint.scaledCap_nonneg P θ C U K hθ hC hU hK)
  refine ⟨2*Real.exp (C*U)*B*V,by positivity,?_⟩
  intro L hL g hg ht u hu A hA
  change ‖sharedBlock ⌊Real.exp (L*u)⌋₊ g L u θ P A -
    mark g L * coprimeScaled ⌊Real.exp (L*u)⌋₊ g L u θ P A‖ ≤ _
  rw [sharedBlock_transform _ g hg, ← actual_head _ g hg]
  apply transform_tail_bound g hg L u C U V B A _ hL hu ht hB hA
  intro p hp a ha
  have hp' := Nat.prime_of_mem_primeFactors hp
  have hr := power_cutoff_mem p (a+1) hp' L u hL hu.1 (mem_range.mpr (by have := mem_range.mp ha; omega))
  have hr1 : (1:ℝ) ≤ (p^(a+1):ℕ) := by exact_mod_cast (mem_Icc.mp hr).1
  have hlog := (Real.log_le_iff_le_exp (by positivity : (0:ℝ)<(p^(a+1):ℕ))).mpr
    ((Nat.le_floor_iff (Real.exp_pos _).le).mp (mem_Icc.mp hr).2)
  have hv := normalized_log_mem ((p^(a+1):ℕ):ℝ) L u hr1 hL hlog
  have hv' : u-Real.log (p^(a+1))/L ∈ Set.Icc 0 U := by
    simp only [Nat.cast_pow] at hv
    exact ⟨by linarith [hv.2],by linarith [hv.1,hu.2]⟩
  unfold actualArray
  rw [residual_coprimeScaled _ g p hg hp,
    translated_cutoff L u (p^(a+1)) hL.ne' (pow_ne_zero _ hp'.ne_zero)]
  simp only [Nat.cast_pow]
  exact (ShiftedEndpoint.scaled_coprime_common_bound P hP A g L _ θ C U K hL hθ hA hv' hK hbound).trans
    (mul_le_mul_of_nonneg_left (EulerHead.mass_le _ g hg) hB)

/-- Uniform relative to the necessary Euler envelope, even at u=0.
This is a proved small remainder, not a hypothesis on the finite error budget. -/
theorem shared_head_uniform (P : Polynomial ℂ) (hP : P.eval 0 = 0)
    (θ C U V : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ L : ℝ in atTop, ∀ g : ℕ, g ≠ 0 → |Real.log g/L| ≤ V →
      ∀ u ∈ Set.Icc 0 U, ∀ A : ℂ, ‖A‖ ≤ C →
        ‖FengAtG.sharedBlock ⌊Real.exp (L*u)⌋₊ g L u θ P A -
          mark g L * CoprimeApproximation.actual L g u θ P A‖ ≤ eps*eulerMass g 0 := by
  obtain ⟨D,hD,h⟩ := shared_head_error P hP θ C U V hθ hC hU hV
  have hl : Tendsto (fun L : ℝ => D/L) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using tendsto_inv_atTop_zero.const_mul D
  filter_upwards [eventually_gt_atTop (0:ℝ),hl.eventually (gt_mem_nhds heps)] with L hL hs
  intro g hg ht u hu A hA
  exact (h L hL g hg ht u hu A hA).trans
    (mul_le_mul_of_nonneg_right hs.le (euler_nonneg g hg))

#print axioms shared_head_error
#print axioms shared_head_uniform
#print axioms transform_tail_bound
#print axioms actual_head
#print axioms main_head
#print axioms residual_prime_support
#print axioms residual_coprime
#print axioms residual_euler_eq
#print axioms residual_coprimeScaled
#print axioms transform_split
#print axioms reciprocal_positive_powers
#print axioms prime_log_square_div_sum
#print axioms positive_support_sum
#print axioms mark_bound
end XiPrime8845.FengSharedTail
