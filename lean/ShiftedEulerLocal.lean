import ShiftedTotient

/-! Quantitative local cancellation for the shifted outer Euler product. -/
noncomputable section
namespace XiPrime8845.ShiftedEulerLocal
open ShiftedTotient
set_option maxHeartbeats 1000000

def localRatio (z : ℝ) (x y : ℂ) : ℂ :=
  (1-z)*(1-z*x*y)/((1-z*x)*(1-z*y))

theorem denominator_bound (z d : ℝ) (x : ℂ) (hz : 0 ≤ z) (hz' : z ≤ 1/2)
    (hx : ‖x-1‖ ≤ d) (hd : z*d ≤ 1/4) :
    (1/4 : ℝ) ≤ ‖1-(z:ℂ)*x‖ := by
  have he : (1:ℂ)-z = (1-z*x)+(z:ℂ)*(x-1) := by ring
  have h := norm_add_le ((1:ℂ)-z*x) ((z:ℂ)*(x-1))
  rw [← he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hz] at h
  have hn : ‖(1:ℂ)-z‖ = 1-z := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
  rw [hn] at h
  have hh := mul_le_mul_of_nonneg_left hx hz
  linarith

theorem local_defect_bound (z d e : ℝ) (x y : ℂ)
    (hz : 0 ≤ z) (hz' : z ≤ 1/2) (hx : ‖x-1‖ ≤ d) (hy : ‖y-1‖ ≤ e)
    (hd : z*d ≤ 1/4) (he : z*e ≤ 1/4) :
    ‖localRatio z x y-1‖ ≤ 16*z*d*e := by
  have hdx := denominator_bound z d x hz hz' hx hd
  have hdy := denominator_bound z e y hz hz' hy he
  have hnx : (1:ℂ)-z*x ≠ 0 := norm_pos_iff.mp (by linarith)
  have hny : (1:ℂ)-z*y ≠ 0 := norm_pos_iff.mp (by linarith)
  rw [localRatio, local_ratio_defect z x y hnx hny]
  simp only [norm_div, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hz, norm_sub_rev (1:ℂ) x, norm_sub_rev (1:ℂ) y]
  have hd0 : 0 ≤ d := (norm_nonneg _).trans hx
  have he0 : 0 ≤ e := (norm_nonneg _).trans hy
  have hnum := mul_le_mul (mul_le_mul_of_nonneg_left hx hz) hy (norm_nonneg _) (mul_nonneg hz hd0)
  have hden : (1/16 : ℝ) ≤ ‖(1:ℂ)-z*x‖*‖(1:ℂ)-z*y‖ := by nlinarith
  calc
    _ ≤ (z*d*e)/(1/16) := div_le_div₀ (mul_nonneg (mul_nonneg hz hd0) he0) hnum (by norm_num) hden
    _ = _ := by ring

def twist (A : ℂ) (L : ℝ) (p : ℕ) : ℂ :=
  Complex.exp (-(A/(L:ℂ))*(Real.log p:ℂ))

theorem twist_bound (A : ℂ) (L C U : ℝ) (p : ℕ) (hp : p.Prime)
    (hL : 0 < L) (hA : ‖A‖ ≤ C) (hpL : Real.log p ≤ L*U) (hCU : C*U ≤ 1) :
    ‖twist A L p-1‖ ≤ 2*C*Real.log p/L := by
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hC : 0 ≤ C := (norm_nonneg A).trans hA
  have hn : ‖-(A/(L:ℂ))*(Real.log p:ℂ)‖ ≤ C*Real.log p/L := by
    rw [norm_mul, norm_neg, norm_div, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hL, abs_of_nonneg hlog]
    exact (by simpa only [div_mul_eq_mul_div] using
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hA hlog) hL.le)
  have hs : C*Real.log p/L ≤ 1 := by
    apply (div_le_iff₀ hL).mpr
    nlinarith [mul_le_mul_of_nonneg_left hpL hC]
  apply (Complex.norm_exp_sub_one_le (hn.trans hs)).trans
  calc
    _ ≤ 2*(C*Real.log p/L) := mul_le_mul_of_nonneg_left hn (by norm_num)
    _ = _ := by ring

theorem prime_small (L C : ℝ) (p : ℕ) (hp : p.Prime)
    (hL : 0 < L) (hC : 0 ≤ C) (hlarge : 8*C ≤ L) :
    (1/(p:ℝ))*(2*C*Real.log p/L) ≤ 1/4 := by
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hlog : Real.log p/(p:ℝ) ≤ 1 :=
    (div_le_one hp0).mpr (Real.log_le_sub_one_of_pos hp0 |>.trans (by linarith))
  calc
    _ = (2*C/L)*(Real.log p/p) := by ring
    _ ≤ (2*C/L)*1 := mul_le_mul_of_nonneg_left hlog (by positivity)
    _ ≤ 1/4 := by rw [mul_one]; apply (div_le_iff₀ hL).mpr; linarith

def primeRatio (A B : ℂ) (L : ℝ) (p : ℕ) : ℂ :=
  localRatio (1/(p:ℝ)) (twist A L p) (twist B L p)

theorem prime_defect_bound (A B : ℂ) (L C U : ℝ) (p : ℕ) (hp : p.Prime)
    (hL : 0 < L) (hA : ‖A‖ ≤ C) (hB : ‖B‖ ≤ C)
    (hpL : Real.log p ≤ L*U) (hCU : C*U ≤ 1) (hlarge : 8*C ≤ L) :
    ‖primeRatio A B L p-1‖ ≤ (64*C^2/L^2)*Real.log p := by
  have hC : 0 ≤ C := (norm_nonneg A).trans hA
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hlog0 : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hz : 1/(p:ℝ) ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) hp2
  have hlog : Real.log p/(p:ℝ) ≤ 1 :=
    (div_le_one hp0).mpr (Real.log_le_sub_one_of_pos hp0 |>.trans (by linarith))
  have h := local_defect_bound (1/p) (2*C*Real.log p/L) (2*C*Real.log p/L)
    (twist A L p) (twist B L p) (by positivity) hz
    (twist_bound A L C U p hp hL hA hpL hCU)
    (twist_bound B L C U p hp hL hB hpL hCU)
    (prime_small L C p hp hL hC hlarge) (prime_small L C p hp hL hC hlarge)
  apply h.trans
  calc
    _ = (64*C^2/L^2)*(Real.log p/p)*Real.log p := by ring
    _ ≤ (64*C^2/L^2)*1*Real.log p :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog (by positivity)) hlog0
    _ = _ := by ring

theorem twist_cpow (A : ℂ) (L : ℝ) (p : ℕ) (hp : p ≠ 0) :
    twist A L p = (p:ℂ)^(-(A/(L:ℂ))) := by
  have h := GcdDecomposition.positive_cpow (p:ℝ)
    (by exact_mod_cast Nat.pos_of_ne_zero hp) (-(A/(L:ℂ)))
  simp only [Complex.ofReal_natCast] at h
  rw [h]
  unfold twist
  congr 1
  ring

theorem primeRatio_cpow (A B : ℂ) (L : ℝ) (p : ℕ) (hp : p ≠ 0) :
    primeRatio A B L p = (1-(p:ℂ)⁻¹)*localFactor (A/L) (B/L) p := by
  have hp0 : (p:ℂ) ≠ 0 := by exact_mod_cast hp
  have he (a : ℂ) : (p:ℂ)^(-(1+a)) = (p:ℂ)⁻¹*(p:ℂ)^(-a) := by
    rw [show -(1+a) = (-1:ℂ)+(-a) by ring, Complex.cpow_add _ _ hp0,
      Complex.cpow_neg_one]
  have he₂ (a b : ℂ) : (p:ℂ)^(-(1+a+b)) = (p:ℂ)⁻¹*(p:ℂ)^(-a)*(p:ℂ)^(-b) := by
    rw [show -(1+a+b) = (-(1+a))+(-b) by ring, Complex.cpow_add _ _ hp0, he]
  simp only [primeRatio, localRatio, localFactor, twist_cpow A L p hp,
    twist_cpow B L p hp, he, he₂,
    Complex.ofReal_natCast, Complex.ofReal_inv, one_div]
  ring

theorem primeRatio_factor (A B : ℂ) (L : ℝ) (p : ℕ) (hp : p.Prime) :
    localFactor (A/L) (B/L) p = localFactor 0 0 p * primeRatio A B L p := by
  have hzero : (1:ℂ)-(p:ℂ)⁻¹ ≠ 0 := by
    have hp1 : (p:ℂ) ≠ 1 := by exact_mod_cast hp.ne_one
    intro h
    have hh : (p:ℂ)⁻¹ = 1 := by linear_combination -h
    exact hp1 (inv_eq_one.mp hh)
  have he : localFactor 0 0 p = ((1:ℂ)-(p:ℂ)⁻¹)⁻¹ := by
    simp only [localFactor, add_zero, Complex.cpow_neg_one]
    field_simp
  rw [primeRatio_cpow A B L p hp.ne_zero, he, ← mul_assoc,
    inv_mul_cancel₀ hzero, one_mul]

#print axioms primeRatio_factor
#print axioms denominator_bound
#print axioms local_defect_bound
#print axioms twist_bound
#print axioms prime_defect_bound
end XiPrime8845.ShiftedEulerLocal
