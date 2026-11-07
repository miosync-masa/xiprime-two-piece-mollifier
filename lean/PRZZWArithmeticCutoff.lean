import PRZZProductTime
import PRZZSourceDecay

/-! A summable, time-uniform envelope for the literal W arithmetic series.
This removes its sharp rectangular cutoff with the actual finite mollifier.
It does not identify a phase-replaced Poisson weight with this series. -/
noncomputable section
open scoped BigOperators
open MeasureTheory Set Filter Topology Complex
namespace XiPrime8845.PRZZWArithmeticCutoff
open PRZZL1Finite
set_option maxHeartbeats 3000000

def kernel (sigma : ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  PRZZDyadicEnvelope.sourceW sigma ((n:ℝ)/(t/(2*Real.pi)))

def decayConstant (sigma : ℂ) : ℝ :=
  Real.exp (2^2:ℝ)/(2*Real.sqrt Real.pi*2)+
    (2+2*|(2:ℝ)|)*Real.exp (2^2:ℝ)/(Real.sqrt Real.pi*‖sigma‖^2)

theorem kernel_bound (sigma : ℂ) (hs : sigma ≠ 0) (T t x : ℝ)
    (hT : 0 < T) (ht : t ∈ Icc T (2*T)) (hx : 0 < x) :
    ‖PRZZDyadicEnvelope.sourceW sigma (x/(t/(2*Real.pi)))‖ ≤
      decayConstant sigma*(T/Real.pi)^2/x^2 := by
  have ht0 : 0 < t := hT.trans_le ht.1
  have hq : 0 < t/(2*Real.pi) := by positivity
  have hh := PRZZSourceDecay.sourceW_decay sigma hs 2 (x/(t/(2*Real.pi)))
    (by norm_num) (by positivity)
  change _ ≤ decayConstant sigma*(x/(t/(2*Real.pi)))^(-(2:ℝ)) at hh
  have he : (x/(t/(2*Real.pi)))^(-(2:ℝ)) = (t/(2*Real.pi))^2/x^2 := by
    rw [Real.rpow_neg (by positivity),Real.rpow_two]
    field_simp
  rw [he] at hh
  apply hh.trans
  have hqt : t/(2*Real.pi) ≤ T/Real.pi := by
    apply (div_le_div_iff₀ (by positivity) Real.pi_pos).mpr
    nlinarith [mul_le_mul_of_nonneg_right ht.2 Real.pi_pos.le]
  have hc : 0 ≤ decayConstant sigma := by unfold decayConstant; positivity
  calc
    _ ≤ decayConstant sigma*((T/Real.pi)^2/x^2) := by gcongr
    _ = _ := by ring

theorem arithmetic_bound (a b : ℂ) (hab : a+b ≠ 0)
    (ha : 0 ≤ 1/2+a.re) (hb : 0 ≤ 1/2+b.re)
    (T t : ℝ) (hT : 0 < T) (ht : t ∈ Icc T (2*T))
    (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) :
    ‖directTerm a b (kernel (a+b)) t m k‖ ≤
      (decayConstant (a+b)*(T/Real.pi)^2)*((m:ℝ)^(-2:ℝ)*(k:ℝ)^(-2:ℝ)) := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hd := PRZZProductMass.direct_coefficient a b 0 m k hm hk ha hb
  rw [← PRZZProductSummation.coefficient_time a b t m k hm hk] at hd
  simp only [Real.rpow_zero,div_one] at hd
  have hker := kernel_bound (a+b) hab T t ((m:ℝ)*k) hT ht (mul_pos hm0 hk0)
  have he : ‖directTerm a b (kernel (a+b)) t m k‖ =
      ‖PRZZDyadicEnvelope.sourceW (a+b) (((m:ℝ)*k)/(t/(2*Real.pi)))‖ *
        ‖directTerm a b (fun _ _ => 1) t m k‖ := by
    simp only [directTerm,kernel,norm_div,norm_one,Nat.cast_mul]
    ring
  rw [he]
  apply (mul_le_mul hker hd (norm_nonneg _) (by unfold decayConstant; positivity)).trans_eq
  rw [mul_one,Real.rpow_neg hm0.le,Real.rpow_neg hk0.le,Real.rpow_two,Real.rpow_two]
  field_simp

theorem term_measurable (a b : ℂ) (hab : a+b ≠ 0) (T : ℝ) (hT : 0 < T)
    (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) :
    AEStronglyMeasurable (fun t => directTerm a b (kernel (a+b)) t m k)
      (volume.restrict (Icc T (2*T))) := by
  have hx : 0 < ((m*k:ℕ):ℝ) := by positivity
  have hw : ContinuousOn (fun t : ℝ => kernel (a+b) (m*k) t) (Icc T (2*T)) := by
    unfold kernel
    apply (PRZZSourceWOuter.sourceW_continuous (a+b) hab).comp
    · fun_prop (disch := intro t ht; have : 0 < t := hT.trans_le ht.1; positivity)
    · intro t ht
      have : 0 < t := hT.trans_le ht.1
      exact div_pos hx (by positivity)
  have hd : Continuous (fun t : ℝ => (m:ℂ)^(1/2+a+t*I)*(k:ℂ)^(1/2+b-t*I)) := by
    have hm0 : (m:ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    have hk0 : (k:ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    simp_rw [Complex.cpow_def_of_ne_zero hm0,Complex.cpow_def_of_ne_zero hk0]
    fun_prop
  have hdi := hd.inv₀ (fun t => mul_ne_zero
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast (by omega : m ≠ 0))))
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast (by omega : k ≠ 0)))))
  unfold directTerm
  simp only [div_eq_mul_inv]
  exact (hw.aestronglyMeasurable measurableSet_Icc).mul hdi.aestronglyMeasurable

theorem weighted_cutoff_removed (a b : ℂ) (hab : a+b ≠ 0)
    (ha : 0 ≤ 1/2+a.re) (hb : 0 ≤ 1/2+b.re) (T : ℝ) (hT : 0 < T)
    (phi : ℝ → ℂ) (hphi : Continuous phi) :
    Tendsto (fun L : ℕ => ∫ t in Icc T (2*T), phi t *
      directSum L a b (kernel (a+b)) t) atTop
      (𝓝 (∫ t in Icc T (2*T), phi t * ∑' p : ℕ × ℕ,
        directTerm a b (kernel (a+b)) t (p.1+1) (p.2+1))) := by
  obtain ⟨D,hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hphi.continuousOn
  let B := max D 0*(decayConstant (a+b)*(T/Real.pi)^2)
  let w := fun p : ℕ × ℕ => B*(((p.1:ℝ)+1)^(-2:ℝ)*((p.2:ℝ)+1)^(-2:ℝ))
  have hn : Summable (fun n : ℕ => ((n:ℝ)+1)^(-2:ℝ)) := by
    have hh := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr
      (by norm_num : (-2:ℝ) < -1))
    simpa only [Nat.cast_add,Nat.cast_one] using hh
  have hw : Summable w := (hn.mul_of_nonneg hn (by intro n; positivity)
    (by intro n; positivity)).mul_left B
  have hbound (p : ℕ × ℕ) (t : ℝ) (ht : t ∈ Icc T (2*T)) :
      ‖phi t * directTerm a b (kernel (a+b)) t (p.1+1) (p.2+1)‖ ≤ w p := by
    rw [norm_mul]
    have hh := arithmetic_bound a b hab ha hb T t hT ht (p.1+1) (p.2+1) (by omega) (by omega)
    have hp := mul_le_mul ((hD t ht).trans (le_max_left D 0)) hh
      (norm_nonneg _) (le_max_right D 0)
    simpa only [w,B,Nat.cast_add,Nat.cast_one,mul_assoc] using hp
  have hh := PRZZProductTime.rectangles_integral T
    (fun p t => phi t * directTerm a b (kernel (a+b)) t (p.1+1) (p.2+1)) w hw
    (by intro p; dsimp [w,B,decayConstant]; positivity)
    (fun p => hphi.aestronglyMeasurable.mul
      (term_measurable a b hab T hT _ _ (by omega) (by omega))) hbound
  simpa only [directSum,PRZZL1Truncation.positive_sum,Finset.sum_product,
    Finset.mul_sum,tsum_mul_left] using hh

theorem mollified_cutoff_removed (a b : ℂ) (hab : a+b ≠ 0)
    (ha : 0 ≤ 1/2+a.re) (hb : 0 ≤ 1/2+b.re) (T : ℝ) (hT : 0 < T)
    (phi : ℝ → ℂ) (hphi : Continuous phi) (c e : ℕ → ℂ) (N : ℕ) :
    Tendsto (fun L : ℕ => ∫ t in Icc T (2*T),
      PRZZMollifiedTime.mollifierWeight phi c e N t * directSum L a b (kernel (a+b)) t) atTop
      (𝓝 (∫ t in Icc T (2*T), PRZZMollifiedTime.mollifierWeight phi c e N t *
        ∑' p : ℕ × ℕ, directTerm a b (kernel (a+b)) t (p.1+1) (p.2+1))) :=
  weighted_cutoff_removed a b hab ha hb T hT _
    (PRZZMollifiedTime.mollifierWeight_continuous phi hphi c e N)

/-- Concrete arithmetic coefficient mass, uniform in time and independent
of every rectangular cutoff. The T^2 cost is a domination cost only. -/
theorem source_term_bound (a b : ℂ) (hab : a+b ≠ 0)
    (ha : 0 ≤ 1/2+a.re) (hb : 0 ≤ 1/2+b.re)
    (js : List ℕ) (N : ℕ) (hN : 1 ≤ N) (phi : ℝ → ℂ)
    (T t : ℝ) (hT : 0 < T) (ht : t ∈ Icc T (2*T))
    (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) :
    ‖PRZZMollifiedTime.mollifierWeight phi
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
      (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) N t *
        directTerm a b (kernel (a+b)) t m k‖ ≤
      (4*(N:ℝ)*(Real.log N)^(2*PRZZGCoefficient.degree js))*‖phi t‖ *
        ((decayConstant (a+b)*(T/Real.pi)^2)*
          ((m:ℝ)^(-2:ℝ)*(k:ℝ)^(-2:ℝ))) := by
  rw [norm_mul]
  have hlog : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  exact mul_le_mul (PRZZReplacementMass.source_weight_bound js N hN phi t)
    (arithmetic_bound a b hab ha hb T t hT ht m k hm hk)
    (norm_nonneg _) (by positivity)

#print axioms source_term_bound
#print axioms kernel_bound
#print axioms arithmetic_bound
#print axioms term_measurable
#print axioms weighted_cutoff_removed
#print axioms mollified_cutoff_removed
end XiPrime8845.PRZZWArithmeticCutoff
