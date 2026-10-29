import FengOutside

/-! An elementary uniform budget for the log-weighted prime-power measure.
No PNT rate or limiting prime-power integral is assumed. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.zeta
namespace XiPrime8845.FengPrimeMass
open ArithmeticFunction Finset
set_option maxHeartbeats 1000000

theorem reciprocal_le_floor (N r : ℕ) (hr : 0 < r) (hrN : r ≤ N) :
    1/(r:ℝ) ≤ 2*(N/r:ℕ)/(N:ℝ) := by
  have hN : 0 < N := hr.trans_le hrN
  have hq : 1 ≤ N/r := (Nat.le_div_iff_mul_le hr).mpr (by simpa using hrN)
  have hm := Nat.mod_lt N hr
  have hd := Nat.div_add_mod N r
  have hqr := Nat.mul_le_mul_right r hq
  have hh : N ≤ 2*(N/r)*r := by nlinarith
  have hrR : (0:ℝ)<r := by exact_mod_cast hr
  have hNR : (0:ℝ)<N := by exact_mod_cast hN
  apply (div_le_div_iff₀ hrR hNR).mpr
  simpa only [one_mul,Nat.cast_mul,Nat.cast_ofNat] using (show (N:ℝ) ≤ (2*(N/r)*r:ℕ) by exact_mod_cast hh)

theorem mangoldt_floor_sum (N : ℕ) :
    (∑ r ∈ Icc 1 N, vonMangoldt r*(N/r:ℕ)) = ∑ n ∈ Icc 1 N, Real.log n := by
  have h := sum_Ioc_mul_zeta_eq_sum (R:=ℝ) vonMangoldt N
  rw [vonMangoldt_mul_zeta] at h
  have he : Icc 1 N = Ioc 0 N := by ext n; simp; omega
  simpa only [he,ArithmeticFunction.log_apply] using h.symm

theorem mangoldt_reciprocal_sum (N : ℕ) :
    (∑ r ∈ Icc 1 N, vonMangoldt r/(r:ℝ)) ≤ 2*Real.log N := by
  by_cases hN : N=0
  · subst N; simp
  have hNR : (0:ℝ)<N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hh : (∑ r ∈ Icc 1 N, vonMangoldt r*(N/r:ℕ)) ≤ (N:ℝ)*Real.log N := by
    rw [mangoldt_floor_sum]
    calc
      _ ≤ ∑ n ∈ Icc 1 N, Real.log N := by
        apply sum_le_sum
        intro n hn
        exact Real.log_le_log (by exact_mod_cast (mem_Icc.mp hn).1) (by exact_mod_cast (mem_Icc.mp hn).2)
      _ = _ := by simp
  calc
    _ ≤ ∑ r ∈ Icc 1 N, vonMangoldt r*(2*(N/r:ℕ)/(N:ℝ)) := by
      apply sum_le_sum
      intro r hr
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left
        (reciprocal_le_floor N r (mem_Icc.mp hr).1 (mem_Icc.mp hr).2) (vonMangoldt_nonneg (n:=r))
    _ = (2/(N:ℝ))*(∑ r ∈ Icc 1 N, vonMangoldt r*(N/r:ℕ)) := by
      rw [Finset.mul_sum]; apply sum_congr rfl; intros; ring
    _ ≤ (2/(N:ℝ))*((N:ℝ)*Real.log N) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by field_simp

def mass (N : ℕ) : ℝ := ∑ r ∈ Icc 1 N, vonMangoldt r*Real.log r/(r:ℝ)

theorem mass_nonneg (N : ℕ) : 0 ≤ mass N := by
  unfold mass
  apply sum_nonneg
  intro r hr
  exact div_nonneg (mul_nonneg vonMangoldt_nonneg (Real.log_nonneg (by exact_mod_cast (mem_Icc.mp hr).1))) (Nat.cast_nonneg _)

theorem mass_le (N : ℕ) : mass N ≤ 2*(Real.log N)^2 := by
  by_cases hN : N=0
  · subst N; simp [mass]
  have hl : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN)
  calc
    _ ≤ Real.log N * ∑ r ∈ Icc 1 N, vonMangoldt r/(r:ℝ) := by
      rw [Finset.mul_sum]
      apply sum_le_sum
      intro r hr
      have hlog := Real.log_le_log (by exact_mod_cast (mem_Icc.mp hr).1 : (0:ℝ)<r)
        (by exact_mod_cast (mem_Icc.mp hr).2 : (r:ℝ)≤N)
      have hh := mul_le_mul_of_nonneg_right hlog (div_nonneg (vonMangoldt_nonneg (n:=r)) (Nat.cast_nonneg r))
      convert hh using 1 <;> ring
    _ ≤ Real.log N*(2*Real.log N) := mul_le_mul_of_nonneg_left (mangoldt_reciprocal_sum N) hl
    _ = _ := by ring

/-- After L^-2 normalization the full prime-power mass is uniformly bounded. -/
theorem scaled_mass_bound (L U : ℝ) (hL : 0 < L) (hU : 0 ≤ U) :
    mass ⌊Real.exp (L*U)⌋₊/L^2 ≤ 2*U^2 := by
  have hx : 1 ≤ Real.exp (L*U) := Real.one_le_exp_iff.mpr (mul_nonneg hL.le hU)
  have hN : 1 ≤ ⌊Real.exp (L*U)⌋₊ := (Nat.le_floor_iff (Real.exp_pos _).le).mpr (by exact_mod_cast hx)
  have hN0 : (0:ℝ)<⌊Real.exp (L*U)⌋₊ := by exact_mod_cast hN
  have hlog : Real.log ⌊Real.exp (L*U)⌋₊ ≤ L*U := by
    calc
      _ ≤ Real.log (Real.exp (L*U)) := Real.log_le_log hN0 (Nat.floor_le (Real.exp_pos _).le)
      _ = _ := Real.log_exp _
  have hlog0 : 0 ≤ Real.log ⌊Real.exp (L*U)⌋₊ := Real.log_nonneg (by exact_mod_cast hN)
  have hs := pow_le_pow_left₀ hlog0 hlog 2
  apply (div_le_iff₀ (sq_pos_of_pos hL)).mpr
  nlinarith [mass_le ⌊Real.exp (L*U)⌋₊]

#print axioms reciprocal_le_floor
#print axioms mangoldt_floor_sum
#print axioms mangoldt_reciprocal_sum
#print axioms mass_nonneg
#print axioms mass_le
#print axioms scaled_mass_bound
end XiPrime8845.FengPrimeMass
