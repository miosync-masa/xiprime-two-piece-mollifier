import PRZZKernelUniform
import PRZZSourceWSums

/-! Arithmetic substitution and cutoff removal for the actual Gamma kernel.
This supplies joint absolute summability, not the zeta-product AFE identity
or the subsequent Poisson identification with A*. -/
noncomputable section
open scoped BigOperators
open Complex Filter Topology Finset
namespace XiPrime8845.PRZZActualDirectSum
open PRZZL1Finite PRZZDyadicEnvelope
set_option maxHeartbeats 3000000

def actualWeight (a b : ℂ) (n : ℕ) (t : ℝ) : ℂ := PRZZAFEGamma.kernel a b n t
def mainWeight (a b : ℂ) (n : ℕ) (t : ℝ) : ℂ := sourceW (a+b) ((n:ℝ)/(t/(2*Real.pi)))

theorem main_envelope (a b : ℂ) (hs : a+b ≠ 0) (t : ℝ) (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x →
      ‖sourceW (a+b) (x/(t/(2*Real.pi)))‖ ≤ C*x^(-2:ℝ) := by
  obtain ⟨C,D,hC,hD,h⟩ := PRZZSourceWDerivatives.source_all_decay 0 2 (by norm_num)
  let q := t/(2*Real.pi)
  have hq : 0 < q := by dsimp [q]; positivity
  refine ⟨(C+D/‖a+b‖^2)*q^2,by positivity,?_⟩
  intro x hx
  have hh := h (a+b) hs (x/q) (div_pos hx hq)
  simp only [iteratedDeriv_zero,pow_zero,div_one] at hh
  apply hh.trans_eq
  rw [Real.rpow_neg (div_nonneg hx.le hq.le),Real.rpow_two,
    Real.rpow_neg hx.le,Real.rpow_two]
  field_simp

theorem actual_envelope (a b : ℂ) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4)
    (hs : a+b ≠ 0) (T t : ℝ) (hT : 256*Real.pi ≤ T) (hT' : 128 ≤ T)
    (ht : T ≤ t) (ht2 : t ≤ 2*T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → ‖PRZZAFEGamma.kernel a b x t‖ ≤ C*x^(-2:ℝ) := by
  obtain ⟨C,hC,h⟩ := PRZZKernelUniform.difference_uniform
  obtain ⟨D,hD,hd⟩ := main_envelope a b hs t (by linarith)
  let B := C*(1+16/‖a+b‖^2)*
    ((t/(2*Real.pi))^2/T+(1+(t/(2*Real.pi))^2)*Real.exp (-T^2/64))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B+D,by positivity,?_⟩
  intro x hx
  have hh := h a b ha hb hs T t x hT hT' ht ht2 hx
  have htri := norm_le_norm_sub_add (PRZZAFEGamma.kernel a b x t)
    (sourceW (a+b) (x/(t/(2*Real.pi))))
  exact htri.trans ((add_le_add hh (hd x hx)).trans_eq (by dsimp [B]; ring))

theorem denominator_one (a b : ℂ) (ha : -(1/2:ℝ) ≤ a.re) (hb : -(1/2:ℝ) ≤ b.re)
    (t : ℝ) (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) :
    1 ≤ ‖(m:ℂ)^(1/2+a+t*I)*(k:ℂ)^(1/2+b-t*I)‖ := by
  have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  rw [← Complex.ofReal_natCast m,← Complex.ofReal_natCast k,
    norm_mul,norm_cpow_eq_rpow_re_of_pos (by linarith : (0:ℝ) < m),
    norm_cpow_eq_rpow_re_of_pos (by linarith : (0:ℝ) < k)]
  have h1 : 1 ≤ (m:ℝ)^((1/2+a+t*I).re) :=
    Real.one_le_rpow hm' (by simp; linarith)
  have h2 : 1 ≤ (k:ℝ)^((1/2+b-t*I).re) :=
    Real.one_le_rpow hk' (by simp; linarith)
  nlinarith

theorem direct_summable_of_envelope (a b : ℂ) (V : ℕ → ℝ → ℂ) (t C : ℝ)
    (ha : -(1/2:ℝ) ≤ a.re) (hb : -(1/2:ℝ) ≤ b.re)
    (hV : ∀ n : ℕ, 1 ≤ n → ‖V n t‖ ≤ C*(n:ℝ)^(-2:ℝ)) :
    Summable (fun p : ℕ × ℕ => directTerm a b V t (p.1+1) (p.2+1)) := by
  have hp : Summable (fun n : ℕ => 1/((n:ℝ)+1)^2) := by
    have hh := (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    simpa only [Nat.cast_add,Nat.cast_one] using hh
  apply ((hp.mul_of_nonneg hp (by intro n; positivity)
    (by intro n; positivity)).mul_left C).of_norm_bounded
  intro p
  have hd := denominator_one a b ha hb t (p.1+1) (p.2+1) (by omega) (by omega)
  have hh := hV ((p.1+1)*(p.2+1)) (by nlinarith)
  rw [directTerm,norm_div]
  apply (div_le_self (norm_nonneg _) hd).trans
  apply hh.trans_eq
  rw [Real.rpow_neg (by positivity),Real.rpow_two]
  push_cast
  field_simp

theorem actual_summable (a b : ℂ) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4)
    (hs : a+b ≠ 0) (T t : ℝ) (hT : 256*Real.pi ≤ T) (hT' : 128 ≤ T)
    (ht : T ≤ t) (ht2 : t ≤ 2*T) :
    Summable (fun p : ℕ × ℕ => directTerm a b (actualWeight a b) t (p.1+1) (p.2+1)) := by
  obtain ⟨C,hC,h⟩ := actual_envelope a b ha hb hs T t hT hT' ht ht2
  have har := abs_le.mp ((Complex.abs_re_le_norm a).trans ha)
  have hbr := abs_le.mp ((Complex.abs_re_le_norm b).trans hb)
  exact direct_summable_of_envelope a b _ t C (by linarith [har.1]) (by linarith [hbr.1])
    (fun n hn => h n (by exact_mod_cast (show 0 < n by omega)))

theorem actual_cutoff_removed (a b : ℂ) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4)
    (hs : a+b ≠ 0) (T t : ℝ) (hT : 256*Real.pi ≤ T) (hT' : 128 ≤ T)
    (ht : T ≤ t) (ht2 : t ≤ 2*T) :
    Tendsto (fun M => directSum M a b (actualWeight a b) t) atTop
      (nhds (∑' p : ℕ × ℕ, directTerm a b (actualWeight a b) t (p.1+1) (p.2+1))) :=
  PRZZL1Truncation.directSum_tendsto a b _ t (actual_summable a b ha hb hs T t hT hT' ht ht2)

#print axioms main_envelope
#print axioms actual_envelope
#print axioms denominator_one
#print axioms direct_summable_of_envelope
#print axioms actual_summable
#print axioms actual_cutoff_removed

theorem directTerm_sub (a b : ℂ) (V W : ℕ → ℝ → ℂ) (t : ℝ) (m k : ℕ) :
    directTerm a b V t m k-directTerm a b W t m k =
      directTerm a b (fun n t => V n t-W n t) t m k := by
  unfold directTerm
  rw [sub_div]

/-- Finite arithmetic replacement, before taking any limit or inserting
the mollifier. The original zeta denominators are retained exactly. -/
theorem finite_replacement (a b : ℂ) (V W : ℕ → ℝ → ℂ) (t C : ℝ) (M : ℕ)
    (ha : -(1/2:ℝ) ≤ a.re) (hb : -(1/2:ℝ) ≤ b.re)
    (hVW : ∀ n : ℕ, 1 ≤ n → ‖V n t-W n t‖ ≤ C*(n:ℝ)^(-2:ℝ)) :
    ‖directSum M a b V t-directSum M a b W t‖ ≤
      C*(∑ m ∈ Icc 1 M, (m:ℝ)^(-2:ℝ))*(∑ k ∈ Icc 1 M, (k:ℝ)^(-2:ℝ)) := by
  unfold directSum
  rw [← sum_sub_distrib]
  simp_rw [← sum_sub_distrib,directTerm_sub]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ m ∈ Icc 1 M, ∑ k ∈ Icc 1 M, C*(m:ℝ)^(-2:ℝ)*(k:ℝ)^(-2:ℝ) := by
      apply sum_le_sum
      intro m hm
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro k hk
      have hm' := (mem_Icc.mp hm).1
      have hk' := (mem_Icc.mp hk).1
      have hd := denominator_one a b ha hb t m k hm' hk'
      rw [directTerm,norm_div]
      apply (div_le_self (norm_nonneg _) hd).trans
      apply (hVW (m*k) (by nlinarith)).trans_eq
      rw [Nat.cast_mul,Real.mul_rpow (by positivity) (by positivity)]
      ring
    _ = _ := by
      simp only [sum_mul,mul_sum,mul_assoc]
      apply sum_congr rfl; intro m hm
      apply sum_congr rfl; intro k hk
      ring

/-- The actual V-W estimate supplies the arithmetic replacement premise.
Its x^-2 scale is kept; this is not the optimized integrated AFE remainder. -/
theorem actual_finite_replacement : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℂ,
    ‖a‖ ≤ 1/4 → ‖b‖ ≤ 1/4 → a+b ≠ 0 → ∀ T t : ℝ,
    256*Real.pi ≤ T → 128 ≤ T → T ≤ t → t ≤ 2*T → ∀ M : ℕ,
    ‖directSum M a b (actualWeight a b) t-directSum M a b (mainWeight a b) t‖ ≤
      (C*(1+16/‖a+b‖^2)*((t/(2*Real.pi))^2/T+
        (1+(t/(2*Real.pi))^2)*Real.exp (-T^2/64)))*
        (∑ m ∈ Icc 1 M, (m:ℝ)^(-2:ℝ))*(∑ k ∈ Icc 1 M, (k:ℝ)^(-2:ℝ)) := by
  obtain ⟨C,hC,h⟩ := PRZZKernelUniform.difference_uniform
  refine ⟨C,hC,?_⟩
  intro a b ha hb hs T t hT hT' ht ht2 M
  have har := abs_le.mp ((Complex.abs_re_le_norm a).trans ha)
  have hbr := abs_le.mp ((Complex.abs_re_le_norm b).trans hb)
  apply finite_replacement a b _ _ t _ M (by linarith [har.1]) (by linarith [hbr.1])
  intro n hn
  exact (h a b ha hb hs T t n hT hT' ht ht2 (by exact_mod_cast (show 0 < n by omega))).trans_eq (by ring)

#print axioms directTerm_sub
#print axioms finite_replacement
#print axioms actual_finite_replacement

theorem main_summable (a b : ℂ) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4)
    (hs : a+b ≠ 0) (t : ℝ) (ht : 0 < t) :
    Summable (fun p : ℕ × ℕ => directTerm a b (mainWeight a b) t (p.1+1) (p.2+1)) := by
  obtain ⟨C,hC,h⟩ := main_envelope a b hs t ht
  have har := abs_le.mp ((Complex.abs_re_le_norm a).trans ha)
  have hbr := abs_le.mp ((Complex.abs_re_le_norm b).trans hb)
  exact direct_summable_of_envelope a b _ t C (by linarith [har.1]) (by linarith [hbr.1])
    (fun n hn => h n (by exact_mod_cast (show 0 < n by omega)))

/-- Both sides of the infinite kernel replacement are genuine absolutely
convergent series, so subtraction commutes with the arithmetic sum. -/
theorem infinite_replacement (a b : ℂ) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4)
    (hs : a+b ≠ 0) (T t : ℝ) (hT : 256*Real.pi ≤ T) (hT' : 128 ≤ T)
    (ht : T ≤ t) (ht2 : t ≤ 2*T) :
    (∑' p : ℕ × ℕ, directTerm a b (actualWeight a b) t (p.1+1) (p.2+1))-
      (∑' p : ℕ × ℕ, directTerm a b (mainWeight a b) t (p.1+1) (p.2+1)) =
      ∑' p : ℕ × ℕ, directTerm a b
        (fun n t => actualWeight a b n t-mainWeight a b n t) t (p.1+1) (p.2+1) := by
  rw [← (actual_summable a b ha hb hs T t hT hT' ht ht2).tsum_sub
    (main_summable a b ha hb hs t (by linarith))]
  apply tsum_congr
  intro p
  exact directTerm_sub a b _ _ t _ _

theorem actual_absolute_tail (a b : ℂ) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4)
    (hs : a+b ≠ 0) (T t : ℝ) (hT : 256*Real.pi ≤ T) (hT' : 128 ≤ T)
    (ht : T ≤ t) (ht2 : t ≤ 2*T) :
    Tendsto (fun M : ℕ =>
      (∑' p : ℕ × ℕ, ‖directTerm a b (actualWeight a b) t (p.1+1) (p.2+1)‖)-
      ∑ p ∈ (range M) ×ˢ (range M), ‖directTerm a b (actualWeight a b) t (p.1+1) (p.2+1)‖)
      atTop (nhds 0) := by
  have hh := (actual_summable a b ha hb hs T t hT hT' ht ht2).norm.hasSum.comp
    PRZZL1Truncation.rectangles_tendsto
  simpa using hh.const_sub (∑' p : ℕ × ℕ, ‖directTerm a b (actualWeight a b) t (p.1+1) (p.2+1)‖)

/-- The actual reflected shifts in the dual AFE block obey the same
summability theorem. This does not assert the functional equation itself. -/
theorem dual_summable (a b : ℂ) (ha : ‖a‖ ≤ 1/4) (hb : ‖b‖ ≤ 1/4)
    (hs : a+b ≠ 0) (T t : ℝ) (hT : 256*Real.pi ≤ T) (hT' : 128 ≤ T)
    (ht : T ≤ t) (ht2 : t ≤ 2*T) :
    Summable (fun p : ℕ × ℕ => directTerm (-b) (-a) (actualWeight (-b) (-a)) t (p.1+1) (p.2+1)) := by
  apply actual_summable (-b) (-a) (by simpa using hb) (by simpa using ha) _ T t hT hT' ht ht2
  rw [show -b + -a = -(a+b) by ring]
  exact neg_ne_zero.mpr hs

#print axioms main_summable
#print axioms infinite_replacement
#print axioms actual_absolute_tail
#print axioms dual_summable
end XiPrime8845.PRZZActualDirectSum
