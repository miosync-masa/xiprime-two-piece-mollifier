import PRZZQuotientMass

/-! Absolute arithmetic mass with a constant fixed before height and shifts.
The explicit finite mollifier coefficient masses are retained. -/
noncomputable section
open scoped BigOperators
open Finset Complex
namespace XiPrime8845.PRZZHeightMass
open PRZZQuotientMass PRZZActualDirectSum PRZZL1Finite PRZZAFEIndices
set_option maxHeartbeats 3000000

theorem direct_mass_height : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℂ,
    ‖a‖ ≤ 1/4 → ‖b‖ ≤ 1/4 → a+b ≠ 0 → ∀ T t : ℝ,
    256*Real.pi ≤ T → 128 ≤ T → T ≤ t → t ≤ 2*T →
    (∑' p : ℕ × ℕ, ‖directTerm a b (actualWeight a b) t (p.1+1) (p.2+1)‖) ≤
      C*T^2*(1+1/‖a+b‖^2) := by
  obtain ⟨C,hC,h⟩ := kernel_height
  let w := fun p : ℕ × ℕ => (1/((p.1:ℝ)+1)^2)*(1/((p.2:ℝ)+1)^2)
  have hp : Summable (fun n : ℕ => 1/((n:ℝ)+1)^2) := by
    have hh := (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    simpa only [Nat.cast_add,Nat.cast_one] using hh
  have hw : Summable w := hp.mul_of_nonneg hp (by intro n; positivity) (by intro n; positivity)
  have hw0 : 0 ≤ ∑' p, w p := tsum_nonneg (fun p => by dsimp [w]; positivity)
  refine ⟨C*((∑' p, w p)+1),by positivity,?_⟩
  intro a b ha hb hs T t hT hT' ht ht2
  let B := C*T^2*(1+1/‖a+b‖^2)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have har := abs_le.mp ((Complex.abs_re_le_norm a).trans ha)
  have hbr := abs_le.mp ((Complex.abs_re_le_norm b).trans hb)
  have hbnd (p : ℕ × ℕ) :
      ‖directTerm a b (actualWeight a b) t (p.1+1) (p.2+1)‖ ≤ B*w p := by
    have hd := denominator_one a b (by linarith [har.1]) (by linarith [hbr.1])
      t (p.1+1) (p.2+1) (by omega) (by omega)
    rw [directTerm,norm_div]
    apply (div_le_self (norm_nonneg _) hd).trans
    apply (h a b ha hb hs T t _ hT hT' ht ht2 (by positivity)).trans_eq
    rw [Real.rpow_neg (by positivity),Real.rpow_two]
    dsimp [B,w,actualWeight]
    push_cast
    field_simp
  have hh := (actual_summable a b ha hb hs T t hT hT' ht ht2).norm.tsum_le_tsum
    hbnd (hw.mul_left B)
  rw [tsum_mul_left] at hh
  apply hh.trans
  dsimp [B]
  nlinarith only [hB]

theorem mollifier_mass_le (N : ℕ) (c : ℕ → ℂ) (t : ℝ) :
    (∑ n ∈ Icc 1 N, ‖c n/(n:ℂ)^(1/2+t*I)‖) ≤ ∑ n ∈ Icc 1 N, ‖c n‖ := by
  apply sum_le_sum
  intro n hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
  rw [norm_div]
  apply div_le_self (norm_nonneg _)
  rw [← Complex.ofReal_natCast n,norm_cpow_eq_rpow_re_of_pos (by linarith : (0:ℝ)<n)]
  apply Real.one_le_rpow hn1
  norm_num

/-- Uniform in the arithmetic cutoff L and in time on [T,2T]. Arbitrary
finite mollifier coefficients are measured explicitly, not assumed bounded. -/
theorem grouped_mass_height : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℂ,
    ‖a‖ ≤ 1/4 → ‖b‖ ≤ 1/4 → a+b ≠ 0 → ∀ T t : ℝ,
    256*Real.pi ≤ T → 128 ≤ T → T ≤ t → t ≤ 2*T →
    ∀ L N : ℕ, ∀ c e : ℕ → ℂ,
    (∑ z ∈ labels L N, ∑ i ∈ fibre L N z,
      ‖term c e a b (actualWeight a b) t i.1.1 i.1.2 i.2.1 i.2.2‖) ≤
      C*T^2*(1+1/‖a+b‖^2)*(∑ n ∈ Icc 1 N, ‖c n‖)*(∑ n ∈ Icc 1 N, ‖e n‖) := by
  obtain ⟨C,hC,h⟩ := direct_mass_height
  refine ⟨C,hC,?_⟩
  intro a b ha hb hs T t hT hT' ht ht2 L N c e
  apply (PRZZAFEProgression.grouped_analytic_mass L N c e a b ha hb hs T t hT hT' ht ht2).trans
  apply mul_le_mul
  · exact mul_le_mul (h a b ha hb hs T t hT hT' ht ht2) (mollifier_mass_le N c t)
      (sum_nonneg (fun n hn => norm_nonneg _)) (by positivity)
  · exact mollifier_mass_le N e t
  · exact sum_nonneg (fun n hn => norm_nonneg _)
  · positivity

#print axioms direct_mass_height
#print axioms mollifier_mass_le
#print axioms grouped_mass_height
/-- Logarithmically scaled shifts with fixed separation. All dependence
on height and the separation is displayed, uniformly in L,N and time. -/
theorem scaled_grouped_mass (S r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in Filter.atTop, ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ → ∀ t : ℝ,
      T ≤ t → t ≤ 2*T → ∀ L N : ℕ, ∀ c e : ℕ → ℂ,
      (∑ z ∈ labels L N, ∑ i ∈ fibre L N z,
        ‖term c e (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))
          (actualWeight (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)))
          t i.1.1 i.1.2 i.2.1 i.2.2‖) ≤
        C*T^2*(1+(Real.log T)^2/r^2)*
          (∑ n ∈ Icc 1 N, ‖c n‖)*(∑ n ∈ Icc 1 N, ‖e n‖) := by
  obtain ⟨C,hC,h⟩ := grouped_mass_height
  refine ⟨C,hC,?_⟩
  filter_upwards [PRZZGammaCentral.log_scaled_shifts_eventually S,
    Filter.eventually_ge_atTop (256*Real.pi),Filter.eventually_ge_atTop (128:ℝ)] with T hsmall hT hT'
  have hL : 0 < Real.log T := Real.log_pos (by linarith)
  have hLc : (Real.log T:ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  intro A B hA hB hsep t ht ht2 L N c e
  have hab : A+B ≠ 0 := norm_pos_iff.mp (hr.trans_le hsep)
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]; exact div_ne_zero hab hLc
  have hh := h _ _ (hsmall A B hA hB).1 (hsmall A B hA hB).2 hs T t hT hT' ht ht2 L N c e
  rw [← add_div] at hh
  have he : 1/‖(A+B)/(Real.log T:ℂ)‖^2 = (Real.log T)^2/‖A+B‖^2 := by
    rw [norm_div,div_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    field_simp
  rw [he] at hh
  apply hh.trans
  gcongr

#print axioms scaled_grouped_mass
theorem coefficient_mass (js : List ℕ) (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Icc 1 N, ‖(PRZZGCoefficient.coefficient js n:ℂ)‖) ≤
      (N:ℝ)*(Real.log N)^PRZZGCoefficient.degree js := by
  calc
    _ ≤ ∑ _n ∈ Icc 1 N, (Real.log N)^PRZZGCoefficient.degree js := by
      apply sum_le_sum
      intro n hn
      simpa only [Complex.norm_real,Real.norm_eq_abs] using
        PRZZGCoefficient.coefficient_bound js N hN n (mem_Icc.mp hn).1 (mem_Icc.mp hn).2
    _ = _ := by simp

/-- Concrete source coefficients, including both finite coefficient masses.
This is an absolute T^2 N^2 polylog bound, not the optimized PRZZ cancellation bound. -/
theorem source_mass_height : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℂ,
    ‖a‖ ≤ 1/4 → ‖b‖ ≤ 1/4 → a+b ≠ 0 → ∀ T t : ℝ,
    256*Real.pi ≤ T → 128 ≤ T → T ≤ t → t ≤ 2*T →
    ∀ L N : ℕ, 1 ≤ N → ∀ js : List ℕ,
    (∑ z ∈ labels L N, ∑ i ∈ fibre L N z,
      ‖term (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
        (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) a b (actualWeight a b)
        t i.1.1 i.1.2 i.2.1 i.2.2‖) ≤
      C*T^2*(1+1/‖a+b‖^2)*(N:ℝ)^2*(Real.log N)^(2*PRZZGCoefficient.degree js) := by
  obtain ⟨C,hC,h⟩ := grouped_mass_height
  refine ⟨C,hC,?_⟩
  intro a b ha hb hs T t hT hT' ht ht2 L N hN js
  have hh := h a b ha hb hs T t hT hT' ht ht2 L N
    (fun n => (PRZZGCoefficient.coefficient js n:ℂ)) (fun n => (PRZZGCoefficient.coefficient js n:ℂ))
  have hm := coefficient_mass js N hN
  have hl : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  apply hh.trans
  calc
    _ ≤ C*T^2*(1+1/‖a+b‖^2)*((N:ℝ)*(Real.log N)^PRZZGCoefficient.degree js)*
        ((N:ℝ)*(Real.log N)^PRZZGCoefficient.degree js) := by gcongr
    _ = _ := by rw [pow_mul]; ring

#print axioms coefficient_mass
#print axioms source_mass_height
end XiPrime8845.PRZZHeightMass
