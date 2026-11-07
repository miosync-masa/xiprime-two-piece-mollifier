import PRZZProductMass
import Mathlib.Analysis.PSeries

/-! Join the two actual contour bounds before summing product scales.
The exponent p is selectable, allowing a summable arithmetic majorant. -/
noncomputable section
open scoped BigOperators
open MeasureTheory Set Complex Filter Topology
namespace XiPrime8845.PRZZProductSummation
open PRZZLocalReplacement
set_option maxHeartbeats 2000000

theorem monomial (T x u : ℝ) (hT : 0 < T) (hx : 0 < x) :
    T^(-1:ℝ)*(x/T)^u = x^u*T^(-1-u) := by
  rw [Real.div_rpow hx.le hT.le,div_eq_mul_inv,← Real.rpow_neg hT.le]
  calc
    _ = x^u*(T^(-1:ℝ)*T^(-u)) := by ring
    _ = _ := by rw [← Real.rpow_add hT]; simp only [sub_eq_add_neg]

theorem global_bound : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℂ,
    ‖a‖ ≤ 1/4 → ‖b‖ ≤ 1/4 → a+b ≠ 0 → ∀ T t x p : ℝ,
    256*Real.pi ≤ T → 128 ≤ T → T ≤ t → t ≤ 2*T → 0 < x →
    -(1/8:ℝ) ≤ p → p ≤ 2 →
    ‖error a b x t‖ ≤ C*(1+32/‖a+b‖^2)*x^(-p)*T^(p-1) := by
  obtain ⟨Cs,hCs,hs⟩ := PRZZLeftUniform.small_product_bound
  obtain ⟨Cl,hCl,hl⟩ := PRZZLocalReplacement.local_bound
  refine ⟨Cs+Cl,by positivity,?_⟩
  intro a b ha hb hab T t x p hT hT' ht ht2 hx hp hp'
  have hT0 : 0 < T := by linarith
  have he : x^(-p)*T^(p-1) = T^(-1:ℝ)*(x/T)^(-p) := by
    rw [monomial T x (-p) hT0 hx]; congr 1; ring
  rw [mul_assoc ((Cs+Cl)*(1+32/‖a+b‖^2)),he]
  by_cases hxt : x ≤ T
  · have hh := hs a b ha hb hab T t x hT hT' ht ht2 hx
    have he' : x^(1/8:ℝ)*T^(-9/8:ℝ) = T^(-1:ℝ)*(x/T)^(1/8:ℝ) := by
      rw [monomial T x (1/8) hT0 hx]; norm_num
    have hh' : ‖error a b x t‖ ≤ Cs*(1+32/‖a+b‖^2)*(T^(-1:ℝ)*(x/T)^(1/8:ℝ)) := by
      rw [← he']; exact hh.trans_eq (by ring)
    apply hh'.trans
    have hr : (x/T)^(1/8:ℝ) ≤ (x/T)^(-p) :=
      Real.rpow_le_rpow_of_exponent_ge (by positivity)
        ((div_le_one hT0).mpr hxt) (by linarith)
    exact mul_le_mul
      (mul_le_mul_of_nonneg_right (show Cs ≤ Cs+Cl by linarith) (by positivity))
      (mul_le_mul_of_nonneg_left hr (by positivity)) (by positivity) (by positivity)
  · have hh := hl a b ha hb hab T t x x hT hT' ht ht2 hx le_rfl
    have he' : T/x^2 = T^(-1:ℝ)*(x/T)^(-2:ℝ) := by
      rw [monomial T x (-2) hT0 hx]
      norm_num [Real.rpow_neg hx.le,Real.rpow_two]
      ring
    have hh' : ‖error a b x t‖ ≤ Cl*(1+16/‖a+b‖^2)*(T^(-1:ℝ)*(x/T)^(-2:ℝ)) := by
      rw [← he']; exact hh.trans_eq (by ring)
    apply hh'.trans
    have hr : (x/T)^(-2:ℝ) ≤ (x/T)^(-p) :=
      Real.rpow_le_rpow_of_exponent_le
        ((le_div_iff₀ hT0).mpr (by linarith)) (by linarith)
    have hc : Cl*(1+16/‖a+b‖^2) ≤ (Cs+Cl)*(1+32/‖a+b‖^2) := by
      gcongr <;> linarith
    exact mul_le_mul hc (mul_le_mul_of_nonneg_left hr (by positivity))
      (by positivity) (by positivity)

theorem coefficient_time (a b : ℂ) (t : ℝ) (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) :
    ‖PRZZL1Finite.directTerm a b (fun _ _ => 1) t m k‖ =
      ‖PRZZL1Finite.directTerm a b (fun _ _ => 1) 0 m k‖ := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  simp only [PRZZL1Finite.directTerm,norm_div,norm_one,norm_mul,← Complex.ofReal_natCast]
  simp only [Complex.norm_cpow_eq_rpow_re_of_pos hm0,Complex.norm_cpow_eq_rpow_re_of_pos hk0]
  simp

theorem arithmetic_bound : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℂ,
    ‖a‖ ≤ 1/4 → ‖b‖ ≤ 1/4 → a+b ≠ 0 → ∀ T t s eps : ℝ,
    256*Real.pi ≤ T → 128 ≤ T → T ≤ t → t ≤ 2*T →
    0 ≤ s → s ≤ 1/2 → 0 < eps → eps ≤ 1/2 →
    s ≤ 1/2+a.re → s ≤ 1/2+b.re → ∀ m k : ℕ, 1 ≤ m → 1 ≤ k →
    ‖PRZZL1Finite.directTerm a b (fun n t => error a b n t) t m k‖ ≤
      C*(1+32/‖a+b‖^2)*T^(eps-s)*(m:ℝ)^(-1-eps)*(k:ℝ)^(-1-eps) := by
  obtain ⟨C,hC,h⟩ := global_bound
  refine ⟨C,hC,?_⟩
  intro a b ha hb hab T t s eps hT hT' ht ht2 hs hs' he he' hsa hsb m k hm hk
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hx : 0 < (m:ℝ)*k := mul_pos hm0 hk0
  have hh := h a b ha hb hab T t ((m:ℝ)*k) (1+eps-s) hT hT' ht ht2 hx (by linarith) (by linarith)
  have hd := PRZZProductMass.direct_coefficient a b s m k hm hk hsa hsb
  rw [← coefficient_time a b t m k hm hk] at hd
  have hf : ‖PRZZL1Finite.directTerm a b (fun n t => error a b n t) t m k‖ =
      ‖error a b ((m:ℝ)*k) t‖*‖PRZZL1Finite.directTerm a b (fun _ _ => 1) t m k‖ := by
    simp only [PRZZL1Finite.directTerm,norm_div,norm_one,Nat.cast_mul]
    ring
  rw [hf]
  apply (mul_le_mul hh hd (norm_nonneg _) (by positivity)).trans_eq
  have hp : ((m:ℝ)*k)^(-(1+eps-s))*(1/((m:ℝ)*k)^s) =
      (m:ℝ)^(-1-eps)*(k:ℝ)^(-1-eps) := by
    rw [one_div,← Real.rpow_neg hx.le,← Real.rpow_add hx]
    rw [show -(1+eps-s)+(-s) = -1-eps by ring,Real.mul_rpow hm0.le hk0.le]
  rw [show 1+eps-s-1 = eps-s by ring]
  calc
    _ = C*(1+32/‖a+b‖^2)*T^(eps-s)*
        (((m:ℝ)*k)^(-(1+eps-s))*(1/((m:ℝ)*k)^s)) := by ring
    _ = _ := by rw [hp]; ring

/-- Summing the two product regimes costs an arbitrary epsilon, not L^2.
The constant depends on epsilon; all arithmetic truncations are absent. -/
theorem summed_bound (s eps : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1/2)
    (he : 0 < eps) (he' : eps ≤ 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℂ,
    ‖a‖ ≤ 1/4 → ‖b‖ ≤ 1/4 → a+b ≠ 0 →
    s ≤ 1/2+a.re → s ≤ 1/2+b.re → ∀ T t : ℝ,
    256*Real.pi ≤ T → 128 ≤ T → T ≤ t → t ≤ 2*T →
    Summable (fun p : ℕ × ℕ => PRZZL1Finite.directTerm a b
      (fun n t => error a b n t) t (p.1+1) (p.2+1)) ∧
    ‖∑' p : ℕ × ℕ, PRZZL1Finite.directTerm a b
      (fun n t => error a b n t) t (p.1+1) (p.2+1)‖ ≤
      C*(1+32/‖a+b‖^2)*T^(eps-s) := by
  obtain ⟨C,hC,h⟩ := arithmetic_bound
  let w := fun p : ℕ × ℕ => ((p.1:ℝ)+1)^(-1-eps)*((p.2:ℝ)+1)^(-1-eps)
  have hn : Summable (fun n : ℕ => ((n:ℝ)+1)^(-1-eps)) := by
    have hh := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith : -1-eps < -1))
    simpa only [Nat.cast_add,Nat.cast_one] using hh
  have hw : Summable w := hn.mul_of_nonneg hn (by intro n; positivity) (by intro n; positivity)
  have hw0 : 0 ≤ ∑' p, w p := tsum_nonneg (fun p => by dsimp [w]; positivity)
  refine ⟨C*((∑' p, w p)+1),by positivity,?_⟩
  intro a b ha hb hab hsa hsb T t hT hT' ht ht2
  let B := C*(1+32/‖a+b‖^2)*T^(eps-s)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hbnd (p : ℕ × ℕ) : ‖PRZZL1Finite.directTerm a b
      (fun n t => error a b n t) t (p.1+1) (p.2+1)‖ ≤ B*w p := by
    simpa only [B,w,Nat.cast_add,Nat.cast_one,mul_assoc] using
      h a b ha hb hab T t s eps hT hT' ht ht2 hs hs' he he' hsa hsb (p.1+1) (p.2+1) (by omega) (by omega)
  have hnorm := (hw.mul_left B).of_nonneg_of_le (fun p => norm_nonneg _) hbnd
  refine ⟨hnorm.of_norm,?_⟩
  apply (norm_tsum_le_tsum_norm hnorm).trans
  have hh := hnorm.tsum_le_tsum hbnd (hw.mul_left B)
  rw [tsum_mul_left] at hh
  apply hh.trans
  dsimp [B]
  nlinarith only [hB]

/-- The rectangular cutoff is removed for the actual V-W arithmetic
series. No summability premise is supplied by the caller. -/
theorem cutoff_removed (a b : ℂ) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4)
    (hab : a+b ≠ 0) (T t : ℝ) (hT : 256*Real.pi ≤ T) (hT' : 128 ≤ T)
    (ht : T ≤ t) (ht2 : t ≤ 2*T) :
    Tendsto (fun L : ℕ => PRZZL1Finite.directSum L a b
      (fun n t => error a b n t) t) atTop
      (𝓝 (∑' p : ℕ × ℕ, PRZZL1Finite.directTerm a b
        (fun n t => error a b n t) t (p.1+1) (p.2+1))) := by
  obtain ⟨C,hC,h⟩ := summed_bound (1/4) (1/8) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := (abs_le.mp ((Complex.abs_re_le_norm a).trans ha)).1
  have hbr := (abs_le.mp ((Complex.abs_re_le_norm b).trans hb)).1
  exact PRZZL1Truncation.directSum_tendsto a b _ t
    (h a b ha hb hab (by linarith) (by linarith) T t hT hT' ht ht2).1

/-- The untruncated arithmetic correction under the weighted time
integral. This norm bound does not assert a limit/integral interchange. -/
theorem integrated_bound (s eps : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1/2)
    (he : 0 < eps) (he' : eps ≤ 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℂ,
    ‖a‖ ≤ 1/4 → ‖b‖ ≤ 1/4 → a+b ≠ 0 →
    s ≤ 1/2+a.re → s ≤ 1/2+b.re → ∀ T : ℝ,
    256*Real.pi ≤ T → 128 ≤ T → ∀ phi : ℝ → ℂ, Continuous phi →
    ‖∫ t in Icc T (2*T), phi t * ∑' p : ℕ × ℕ,
      PRZZL1Finite.directTerm a b (fun n t => error a b n t) t (p.1+1) (p.2+1)‖ ≤
      (C*(1+32/‖a+b‖^2)*T^(eps-s))*(∫ t in Icc T (2*T), ‖phi t‖) := by
  obtain ⟨C,hC,h⟩ := summed_bound s eps hs hs' he he'
  refine ⟨C,hC,?_⟩
  intro a b ha hb hab hsa hsb T hT hT' phi hphi
  rw [← integral_const_mul]
  have hi : Continuous (fun t => (C*(1+32/‖a+b‖^2)*T^(eps-s))*‖phi t‖) := by fun_prop
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun t => norm_nonneg _)) hi.integrableOn_Icc
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left
    (h a b ha hb hab hsa hsb T t hT hT' ht.1 ht.2).2 (norm_nonneg _)).trans_eq (by ring)

#print axioms integrated_bound
#print axioms cutoff_removed
#print axioms coefficient_time
#print axioms arithmetic_bound
#print axioms summed_bound
#print axioms monomial
#print axioms global_bound
end XiPrime8845.PRZZProductSummation
