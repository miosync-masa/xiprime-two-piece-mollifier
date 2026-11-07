import PRZZLeftFar

/-! The actual V-W comparison after moving to Re(s)=-1/8. Constants are
chosen before shifts, time and the product scale. -/
noncomputable section
open Complex Set MeasureTheory
namespace XiPrime8845.PRZZLeftUniform
open PRZZDifferenceRegular PRZZLeftCentral PRZZDyadicEnvelope
set_option maxHeartbeats 3000000

theorem integrand_uniform : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℂ,
    ‖a‖ ≤ 1/4 → ‖b‖ ≤ 1/4 → a+b ≠ 0 → ∀ T t x v : ℝ,
    256*Real.pi ≤ T → 128 ≤ T → T ≤ t → t ≤ 2*T → 0 < x →
      ‖regular a b x t (t/(2*Real.pi)) (line v)‖ ≤
        C*x^(1/8:ℝ)*(1+32/‖a+b‖^2)*
          ((t/(2*Real.pi))^(-1/8:ℝ)/T+
            (1+(t/(2*Real.pi))^(-1/8:ℝ))*Real.exp (-T^2/64))*
              PRZZCentralIntegral.majorant v := by
  obtain ⟨Cf,hCf,hf⟩ := PRZZLeftFar.far_bound
  let Cc := 1392*Real.exp 6
  refine ⟨Cc+Cf,by dsimp [Cc]; positivity,?_⟩
  intro a b ha hb hs T t x v hT hT' ht ht2 hx
  have ht0 : 0 < t := by linarith
  have hq : 0 < t/(2*Real.pi) := by positivity
  let U := x^(1/8:ℝ)*(1+32/‖a+b‖^2)*PRZZCentralIntegral.majorant v
  let P := (t/(2*Real.pi))^(-1/8:ℝ)/T
  let Q := (1+(t/(2*Real.pi))^(-1/8:ℝ))*Real.exp (-T^2/64)
  have hU : 0 ≤ U := by dsimp [U,PRZZCentralIntegral.majorant]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hCc : 0 ≤ Cc := by dsimp [Cc]; positivity
  by_cases hv : |v| ≤ T/4
  · have hh := central_bound T t x v a b hT' ht hx ha hb hs hv
    have hid : Cc*P*U = (1392*Real.exp 6)*x^(1/8:ℝ)*(1+32/‖a+b‖^2)*
        (t/(2*Real.pi))^(-1/8:ℝ)/T*PRZZCentralIntegral.majorant v := by dsimp [Cc,P,U]; ring
    rw [← hid] at hh
    have hh' : Cc*P*U ≤ (Cc+Cf)*(P+Q)*U := by gcongr <;> linarith
    exact (hh.trans hh').trans_eq (by dsimp [P,Q,U]; ring)
  · have hh := hf a b ha hb hs T t x (t/(2*Real.pi)) v hT
      (by simpa [abs_of_pos ht0] using ht2) hx hq (le_of_not_ge hv)
    have hid : Cf*Q*U = Cf*x^(1/8:ℝ)*(1+32/‖a+b‖^2)*
        (1+(t/(2*Real.pi))^(-1/8:ℝ))*Real.exp (-T^2/64)*PRZZCentralIntegral.majorant v := by
      dsimp [Q,U]; ring
    rw [← hid] at hh
    have hh' : Cf*Q*U ≤ (Cc+Cf)*(P+Q)*U := by gcongr <;> linarith
    exact (hh.trans hh').trans_eq (by dsimp [P,Q,U]; ring)

theorem difference_uniform : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℂ,
    ‖a‖ ≤ 1/4 → ‖b‖ ≤ 1/4 → a+b ≠ 0 → ∀ T t x : ℝ,
    256*Real.pi ≤ T → 128 ≤ T → T ≤ t → t ≤ 2*T → 0 < x →
      ‖PRZZAFEGamma.kernel a b x t-sourceW (a+b) (x/(t/(2*Real.pi)))‖ ≤
        C*x^(1/8:ℝ)*(1+32/‖a+b‖^2)*
          ((t/(2*Real.pi))^(-1/8:ℝ)/T+
            (1+(t/(2*Real.pi))^(-1/8:ℝ))*Real.exp (-T^2/64)) := by
  obtain ⟨C,hC,h⟩ := integrand_uniform
  let J := ∫ v, PRZZCentralIntegral.majorant v
  have hJ : 0 ≤ J := integral_nonneg (fun v => by dsimp [PRZZCentralIntegral.majorant]; positivity)
  refine ⟨C*(J+1)/(2*Real.pi),by positivity,?_⟩
  intro a b ha hb hs T t x hT hT' ht ht2 hx
  have ht0 : 0 < t := by linarith
  let B := C*x^(1/8:ℝ)*(1+32/‖a+b‖^2)*
    ((t/(2*Real.pi))^(-1/8:ℝ)/T+(1+(t/(2*Real.pi))^(-1/8:ℝ))*Real.exp (-T^2/64))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hm := PRZZCentralIntegral.majorant_integrable.const_mul B
  have hi : (∫ v, ‖regular a b x t (t/(2*Real.pi)) (line v)‖) ≤ B*J := by
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun v => norm_nonneg _)) hm
    exact Filter.Eventually.of_forall (fun v => h a b ha hb hs T t x v hT hT' ht ht2 hx)
  rw [PRZZDifferenceContour.difference_shifted a b x t (-1/8) ha hb hs hx ht0 (by norm_num),norm_mul]
  have hn : ‖(1/(2*Real.pi):ℂ)‖ = (1/(2*Real.pi):ℝ) := by
    simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  rw [hn]
  have hh := (norm_integral_le_integral_norm (fun v : ℝ =>
    regular a b x t (t/(2*Real.pi)) (line v))).trans hi
  simp only [line,Complex.ofReal_div,Complex.ofReal_neg,Complex.ofReal_ofNat] at hh ⊢
  apply (mul_le_mul_of_nonneg_left hh (show 0 ≤ 1/(2*Real.pi) by positivity)).trans
  have hh' := mul_le_mul_of_nonneg_left (show J ≤ J+1 by linarith) hB
  exact (mul_le_mul_of_nonneg_left hh' (show 0 ≤ 1/(2*Real.pi) by positivity)).trans_eq
    (by dsimp [B]; ring)

/-- The Gaussian remainder fits the same negative height power. -/
theorem scale_cost (T t : ℝ) (hT : 256*Real.pi ≤ T) (hT' : 128 ≤ T)
    (ht : T ≤ t) :
    (t/(2*Real.pi))^(-1/8:ℝ)/T+
      (1+(t/(2*Real.pi))^(-1/8:ℝ))*Real.exp (-T^2/64) ≤
        ((2*Real.pi)^(1/8:ℝ)+128)*T^(-9/8:ℝ) := by
  have hT0 : 0 < T := by linarith
  have ht0 : 0 < t := by linarith
  have hq1 : 1 ≤ t/(2*Real.pi) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*Real.pi)).mpr
    nlinarith [Real.pi_pos]
  have hq := Real.rpow_le_one_of_one_le_of_nonpos hq1 (by norm_num : (-1/8:ℝ) ≤ 0)
  have hmain : (t/(2*Real.pi))^(-1/8:ℝ)/T ≤ (2*Real.pi)^(1/8:ℝ)*T^(-9/8:ℝ) := by
    calc
      _ ≤ (T/(2*Real.pi))^(-1/8:ℝ)/T := by
        apply div_le_div_of_nonneg_right _ hT0.le
        exact Real.rpow_le_rpow_of_nonpos (by positivity)
          (div_le_div_of_nonneg_right ht (by positivity)) (by norm_num)
      _ = _ := by
        rw [Real.div_rpow hT0.le (by positivity),show (-1/8:ℝ) = -(1/8:ℝ) by ring,
          Real.rpow_neg (show (0:ℝ) ≤ 2*Real.pi by positivity),div_inv_eq_mul]
        rw [show (-9/8:ℝ) = -(1/8:ℝ)+(-1) by ring,Real.rpow_add hT0,Real.rpow_neg_one]
        ring
  have he : Real.exp (-T^2/64) ≤ 64/T^2 := by
    rw [show -T^2/64 = -(T^2/64) by ring,Real.exp_neg]
    have hh : T^2/64 ≤ Real.exp (T^2/64) := by linarith [Real.add_one_le_exp (T^2/64)]
    calc
      _ = 1/Real.exp (T^2/64) := by simp
      _ ≤ 1/(T^2/64) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hh
      _ = _ := by field_simp
  have hp : 1/T^2 ≤ T^(-9/8:ℝ) := by
    calc
      _ = T^(-2:ℝ) := by rw [Real.rpow_neg hT0.le]; norm_num [Real.rpow_natCast,one_div]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have htail : (1+(t/(2*Real.pi))^(-1/8:ℝ))*Real.exp (-T^2/64) ≤ 128*T^(-9/8:ℝ) := by
    calc
      _ ≤ 2*(64/T^2) := by gcongr; linarith
      _ = 128*(1/T^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (by norm_num)
  exact (add_le_add hmain htail).trans_eq (by ring)

/-- A genuine small-product improvement: x^(1/8) T^(-9/8), replacing
the old line-Re=2 scale T/x^2. The constant is uniform in all row data. -/
theorem small_product_bound : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℂ,
    ‖a‖ ≤ 1/4 → ‖b‖ ≤ 1/4 → a+b ≠ 0 → ∀ T t x : ℝ,
    256*Real.pi ≤ T → 128 ≤ T → T ≤ t → t ≤ 2*T → 0 < x →
      ‖PRZZAFEGamma.kernel a b x t-sourceW (a+b) (x/(t/(2*Real.pi)))‖ ≤
        C*(1+32/‖a+b‖^2)*x^(1/8:ℝ)*T^(-9/8:ℝ) := by
  obtain ⟨C,hC,h⟩ := difference_uniform
  refine ⟨C*((2*Real.pi)^(1/8:ℝ)+128),by positivity,?_⟩
  intro a b ha hb hs T t x hT hT' ht ht2 hx
  apply (h a b ha hb hs T t x hT hT' ht ht2 hx).trans
  exact (mul_le_mul_of_nonneg_left (scale_cost T t hT hT' ht)
    (show 0 ≤ C*x^(1/8:ℝ)*(1+32/‖a+b‖^2) by positivity)).trans_eq (by ring)

/-- The fixed shift envelope gives one constant for the whole logarithmic
family. Separation of A+B is retained, not absorbed into a height-dependent constant. -/
theorem scaled_small_product (S r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in Filter.atTop, ∀ A B : ℂ,
      ‖A‖ ≤ S → ‖B‖ ≤ S → r ≤ ‖A+B‖ → ∀ t x : ℝ,
      T ≤ t → t ≤ 2*T → 0 < x →
      ‖PRZZAFEGamma.kernel (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ)) x t-
        sourceW ((A+B)/(Real.log T:ℂ)) (x/(t/(2*Real.pi)))‖ ≤
        C*(1+32*(Real.log T)^2/r^2)*x^(1/8:ℝ)*T^(-9/8:ℝ) := by
  obtain ⟨C,hC,h⟩ := small_product_bound
  refine ⟨C,hC,?_⟩
  filter_upwards [PRZZGammaCentral.log_scaled_shifts_eventually S,
    Filter.eventually_ge_atTop (256*Real.pi),Filter.eventually_ge_atTop (128:ℝ)] with T hsmall hT hT'
  have hL : 0 < Real.log T := Real.log_pos (by linarith)
  have hLc : (Real.log T:ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  intro A B hA hB hsep t x ht ht2 hx
  have hab : A+B ≠ 0 := norm_pos_iff.mp (hr.trans_le hsep)
  have hs : A/(Real.log T:ℂ)+B/(Real.log T:ℂ) ≠ 0 := by
    rw [← add_div]; exact div_ne_zero hab hLc
  have hh := h _ _ (hsmall A B hA hB).1 (hsmall A B hA hB).2 hs T t x hT hT' ht ht2 hx
  rw [← add_div] at hh
  have he : 32/‖(A+B)/(Real.log T:ℂ)‖^2 = 32*(Real.log T)^2/‖A+B‖^2 := by
    rw [norm_div,div_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    field_simp
  rw [he] at hh
  apply hh.trans
  gcongr

#print axioms scaled_small_product
#print axioms scale_cost
#print axioms small_product_bound
#print axioms integrand_uniform
#print axioms difference_uniform
end XiPrime8845.PRZZLeftUniform
