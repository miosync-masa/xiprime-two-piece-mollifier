import PRZZIntegratedAFE

/-! Absolute arithmetic and weighted-time cost of the actual V-W replacement.
This retains the coarse line-Re=2 cost; it is not the optimized PRZZ error,
nor a Poisson formula for the untruncated AFE weight. -/
noncomputable section
open scoped BigOperators
open MeasureTheory Set
namespace XiPrime8845.PRZZReplacementIntegral
open PRZZActualDirectSum PRZZL1Finite
set_option maxHeartbeats 3000000

def arithmeticMass : ℝ := ∑' p : ℕ × ℕ,
  (1/((p.1:ℝ)+1)^2)*(1/((p.2:ℝ)+1)^2)

theorem mass_summable : Summable (fun p : ℕ × ℕ =>
    (1/((p.1:ℝ)+1)^2)*(1/((p.2:ℝ)+1)^2)) := by
  have hp : Summable (fun n : ℕ => 1/((n:ℝ)+1)^2) := by
    simpa only [Nat.cast_add,Nat.cast_one] using (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  exact hp.mul_of_nonneg hp (fun n => by positivity) (fun n => by positivity)

theorem series_bound (a b : ℂ) (V : ℕ → ℝ → ℂ) (t C : ℝ)
    (ha : -(1/2:ℝ) ≤ a.re) (hb : -(1/2:ℝ) ≤ b.re)
    (hV : ∀ n : ℕ, 1 ≤ n → ‖V n t‖ ≤ C*(n:ℝ)^(-2:ℝ)) :
    ‖∑' p : ℕ × ℕ, directTerm a b V t (p.1+1) (p.2+1)‖ ≤ C*arithmeticMass := by
  have hbnd : ∀ p : ℕ × ℕ, ‖directTerm a b V t (p.1+1) (p.2+1)‖ ≤
      C*((1/((p.1:ℝ)+1)^2)*(1/((p.2:ℝ)+1)^2)) := by
    intro p
    rw [directTerm,norm_div]
    apply (div_le_self (norm_nonneg _) (denominator_one a b ha hb t _ _
      (by omega) (by omega))).trans
    apply (hV ((p.1+1)*(p.2+1)) (by nlinarith)).trans_eq
    rw [Real.rpow_neg (by positivity),Real.rpow_two]
    push_cast
    field_simp
  have hm := mass_summable.mul_left C
  have hn := hm.of_nonneg_of_le (fun p => norm_nonneg _) hbnd
  exact (norm_tsum_le_tsum_norm hn).trans
    ((hn.tsum_le_tsum hbnd hm).trans_eq (by rw [tsum_mul_left]; rfl))

def cost (T t : ℝ) : ℝ :=
  (t/(2*Real.pi))^2/T+(1+(t/(2*Real.pi))^2)*Real.exp (-T^2/64)

def difference (a b : ℂ) (t : ℝ) : ℂ :=
  (∑' p : ℕ × ℕ, directTerm a b (actualWeight a b) t (p.1+1) (p.2+1))-
  (∑' p : ℕ × ℕ, directTerm a b (mainWeight a b) t (p.1+1) (p.2+1))

theorem actual_series_bound : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℂ,
    ‖a‖ ≤ 1/4 → ‖b‖ ≤ 1/4 → a+b ≠ 0 → ∀ T t : ℝ,
    256*Real.pi ≤ T → 128 ≤ T → T ≤ t → t ≤ 2*T →
    ‖difference a b t‖ ≤ C*(1+16/‖a+b‖^2)*cost T t*arithmeticMass := by
  obtain ⟨C,hC,h⟩ := PRZZKernelUniform.difference_uniform
  refine ⟨C,hC,?_⟩
  intro a b ha hb hs T t hT hT' ht ht2
  unfold difference
  rw [infinite_replacement a b ha hb hs T t hT hT' ht ht2]
  have har := (Complex.abs_re_le_norm a).trans ha
  have hbr := (Complex.abs_re_le_norm b).trans hb
  apply series_bound a b _ t _ (by linarith [abs_le.mp har]) (by linarith [abs_le.mp hbr])
  intro n hn
  exact (h a b ha hb hs T t n hT hT' ht ht2
    (by exact_mod_cast (show 0 < n by omega))).trans_eq (by dsimp [cost,actualWeight,mainWeight]; ring)

/-- Continuous weights include the actual finite mollifier weight. The
L1 cost is explicit and no time-exchange or kernel-error premise is supplied. -/
theorem weighted_bound : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℂ,
    ‖a‖ ≤ 1/4 → ‖b‖ ≤ 1/4 → a+b ≠ 0 → ∀ T : ℝ,
    256*Real.pi ≤ T → 128 ≤ T → ∀ w : ℝ → ℂ, Continuous w →
    ‖∫ t in Icc T (2*T), w t*difference a b t‖ ≤
      C*(1+16/‖a+b‖^2)*arithmeticMass *
        ∫ t in Icc T (2*T), ‖w t‖*cost T t := by
  obtain ⟨C,hC,h⟩ := actual_series_bound
  refine ⟨C,hC,?_⟩
  intro a b ha hb hs T hT hT' w hw
  let B := C*(1+16/‖a+b‖^2)*arithmeticMass
  have hc : Continuous (fun t => B*(‖w t‖*cost T t)) := by
    unfold cost; fun_prop
  have hi : IntegrableOn (fun t => B*(‖w t‖*cost T t)) (Icc T (2*T)) :=
    hc.integrableOn_Icc
  apply (norm_integral_le_integral_norm _).trans
  calc
    _ ≤ ∫ t in Icc T (2*T), B*(‖w t‖*cost T t) := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => norm_nonneg _)) hi
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (h a b ha hb hs T t hT hT' ht.1 ht.2)
        (norm_nonneg _)).trans_eq (by dsimp [B]; ring)
    _ = _ := by rw [integral_const_mul]

#print axioms series_bound
#print axioms actual_series_bound
#print axioms weighted_bound
end XiPrime8845.PRZZReplacementIntegral
