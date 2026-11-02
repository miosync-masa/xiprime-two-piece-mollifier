import PRZZCombinedBudget

/-! Scalar powers in PRZZ 1802.10521v3 section 4, last Type II display.
The frequency scale must be substituted BEFORE dyadic summation. This
module does not assert that totalBudget retains that scale localization. -/
noncomputable section
open scoped BigOperators
namespace XiPrime8845.PRZZOptimalPowers
open PRZZDISeven
set_option maxHeartbeats 2000000

def target (N T : ℝ) : ℝ := N^(7/4:ℝ)+T^(1/2:ℝ)*N^(7/8:ℝ)

theorem scale_identity (T X V p u v : ℝ) (hT : 0 < T) (hX : 0 < X) (hV : 0 < V) :
    T/(X*V)*((X*V/T)^p*X^u*V^v) =
      T^(1-p)*X^(p+u-1)*V^(p+v-1) := by
  rw [Real.div_rpow (mul_pos hX hV).le hT.le,Real.mul_rpow hX.le hV.le]
  rw [Real.rpow_sub hT,Real.rpow_sub hX,Real.rpow_sub hV,
    Real.rpow_add hX,Real.rpow_add hV]
  simp only [Real.rpow_one]
  field_simp

theorem mixed_power (N T a b : ℝ) (hN : 1 ≤ N) (hNT : N ≤ T)
    (ha : a ≤ 1/2) (hab : a+b ≤ 11/8) :
    T^a*N^b ≤ T^(1/2:ℝ)*N^(7/8:ℝ) := by
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (hN.trans hNT)
  calc
    _ ≤ T^a*N^((7/8:ℝ)+(1/2-a)) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hN (by linarith)) (Real.rpow_nonneg hT.le _)
    _ = T^a*(N^(7/8:ℝ)*N^(1/2-a)) := by rw [Real.rpow_add (by linarith : 0 < N)]
    _ ≤ T^a*(N^(7/8:ℝ)*T^(1/2-a)) := by gcongr
    _ = _ := by rw [mul_left_comm,← Real.rpow_add hT]; ring_nf

theorem seven_term_bound (N T X V : ℝ) (hN : 1 ≤ N) (hNT : N ≤ T)
    (hX : 0 < X) (hXN : X ≤ N) (hV : 0 < V) (hVN : V ≤ N) (i : Fin 7) :
    T/(X*V)*((X*V/T)^(ap i)*X^(balancedPower i)*V^(vp i)) ≤ target N T := by
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (hN.trans hNT)
  rw [scale_identity T X V _ _ _ hT hX hV]
  have hx : 0 ≤ ap i+balancedPower i-1 := by fin_cases i <;> norm_num [ap,balancedPower]
  have hv : 0 ≤ ap i+vp i-1 := by fin_cases i <;> norm_num [ap,vp]
  have hb : T^(1-ap i)*X^(ap i+balancedPower i-1)*V^(ap i+vp i-1) ≤
      T^(1-ap i)*N^(2*ap i+balancedPower i+vp i-2) := by
    calc
      _ ≤ T^(1-ap i)*N^(ap i+balancedPower i-1)*N^(ap i+vp i-1) := by gcongr
      _ = _ := by rw [mul_assoc,← Real.rpow_add (by linarith : 0 < N)]; congr 2; ring
  apply hb.trans
  have hn : 0 ≤ N^(7/4:ℝ) := Real.rpow_nonneg (by linarith) _
  have ht : 0 ≤ T^(1/2:ℝ)*N^(7/8:ℝ) := by positivity
  have hm (a b : ℝ) (ha : a ≤ 1/2) (hab : a+b ≤ 11/8) :
      T^a*N^b ≤ target N T := (mixed_power N T a b hN hNT ha hab).trans (by unfold target; linarith)
  have hp (b : ℝ) (hb : b ≤ 7/4) : N^b ≤ target N T :=
    (Real.rpow_le_rpow_of_exponent_le hN hb).trans (by unfold target; linarith)
  fin_cases i <;> norm_num [ap,balancedPower,vp]
  all_goals first | exact hm _ _ (by norm_num) (by norm_num) | exact hp _ (by norm_num)

theorem seven_bound (N T X V : ℝ) (hN : 1 ≤ N) (hNT : N ≤ T)
    (hX : 0 < X) (hXN : X ≤ N) (hV : 0 < V) (hVN : V ≤ N) :
    T/(X*V)*envelope X (X*V/T) V ≤ 7*target N T := by
  unfold envelope
  rw [Finset.mul_sum]
  exact (Finset.sum_le_sum (fun i _ => seven_term_bound N T X V hN hNT hX hXN hV hVN i)).trans_eq (by simp)

#print axioms scale_identity
#print axioms mixed_power
#print axioms seven_term_bound
#print axioms seven_bound

theorem typeI_bound (N T X V : ℝ) (hN : 1 ≤ N) (hNT : N ≤ T)
    (hX : 0 < X) (hXN : X ≤ N) (hV : 0 < V) (hVN : V ≤ N) :
    T/(X*V)*PRZZCombinedBudget.typeI X (X*V/T) V ≤ 4*target N T := by
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (hN.trans hNT)
  have hN0 : 0 < N := by linarith
  have hs : (2*V)^(1/2:ℝ) ≤ 2*N^(1/2:ℝ) := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hV.le]
    apply mul_le_mul
    · simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) (by norm_num : (1/2:ℝ) ≤ 1)
    · exact Real.rpow_le_rpow hV.le hVN (by norm_num)
    · positivity
    · norm_num
  have hi : V*X^(1/4:ℝ)+X ≤ N*N^(1/4:ℝ)+N := by gcongr
  have hid : T/(X*V)*PRZZCombinedBudget.typeI X (X*V/T) V =
      (2*V)^(1/2:ℝ)*(V*X^(1/4:ℝ)+X) := by
    unfold PRZZCombinedBudget.typeI
    field_simp
  rw [hid]
  apply (mul_le_mul hs hi (by positivity) (by positivity)).trans
  have he : 2*N^(1/2:ℝ)*(N*N^(1/4:ℝ)+N) = 2*(N^(7/4:ℝ)+N^(3/2:ℝ)) := by
    rw [show (7/4:ℝ) = 1/2+(1+1/4) by norm_num,
      show (3/2:ℝ) = 1/2+1 by norm_num]
    simp only [Real.rpow_add hN0,Real.rpow_one]
    ring
  rw [he]
  have hn := Real.rpow_le_rpow_of_exponent_le hN (by norm_num : (3/2:ℝ) ≤ 7/4)
  have ht : 0 ≤ T^(1/2:ℝ)*N^(7/8:ℝ) := by positivity
  unfold target
  nlinarith

/-- The nine terms have the published two-power shape once the local
frequency scale and the local outer mass have actually been supplied. -/
theorem combined_bound (N T X V d : ℝ) (hN : 1 ≤ N) (hNT : N ≤ T)
    (hX : 0 < X) (hXN : X ≤ N) (hV : 0 < V) (hVN : V ≤ N) (hd : 0 < d) :
    T/(d*X*V)*PRZZCombinedBudget.total X (X*V/T) V ≤ 11*target N T/d := by
  have hi := typeI_bound N T X V hN hNT hX hXN hV hVN
  have hii := seven_bound N T X V hN hNT hX hXN hV hVN
  have h := div_le_div_of_nonneg_right (add_le_add hi hii) hd.le
  exact h.trans_eq (by ring) |>.trans' (le_of_eq (by unfold PRZZCombinedBudget.total; ring))

#print axioms typeI_bound
#print axioms combined_bound

/-- A frequency enlargement (in particular T^epsilon) costs at most its
first power: all seven frequency exponents lie in [0,1]. -/
theorem frequency_bound (X V A A0 lam : ℝ) (hX : 0 ≤ X) (hV : 0 ≤ V)
    (hA : 0 ≤ A) (hA0 : 0 ≤ A0) (hlam : 1 ≤ lam) (hAA : A ≤ lam*A0) :
    PRZZCombinedBudget.total X A V ≤ lam*PRZZCombinedBudget.total X A0 V := by
  have hl : 0 ≤ lam := by linarith
  have hi : PRZZCombinedBudget.typeI X A V ≤ lam*PRZZCombinedBudget.typeI X A0 V := by
    unfold PRZZCombinedBudget.typeI
    nlinarith [mul_le_mul_of_nonneg_right hAA
      (show 0 ≤ (2*V)^(1/2:ℝ)*(V*X^(1/4:ℝ)+X) by positivity)]
  have hs : envelope X A V ≤ lam*envelope X A0 V := by
    unfold envelope
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hp : 0 ≤ ap i ∧ ap i ≤ 1 := by fin_cases i <;> norm_num [ap]
    have ha : A^(ap i) ≤ lam*A0^(ap i) := by
      calc
        _ ≤ (lam*A0)^(ap i) := Real.rpow_le_rpow hA hAA hp.1
        _ = lam^(ap i)*A0^(ap i) := Real.mul_rpow hl hA0
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (by simpa using Real.rpow_le_rpow_of_exponent_le hlam hp.2)
          (Real.rpow_nonneg hA0 _)
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg hX _))
      (Real.rpow_nonneg hV _)).trans_eq (by ring)
  unfold PRZZCombinedBudget.total
  linarith

theorem source_frequency_bound (N T X V d A lam : ℝ) (hN : 1 ≤ N) (hNT : N ≤ T)
    (hX : 0 < X) (hXN : X ≤ N) (hV : 0 < V) (hVN : V ≤ N) (hd : 0 < d)
    (hA : 0 ≤ A) (hlam : 1 ≤ lam) (hfreq : A ≤ lam*(X*V/T)) :
    T/(d*X*V)*PRZZCombinedBudget.total X A V ≤ lam*(11*target N T/d) := by
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (hN.trans hNT)
  calc
    _ ≤ T/(d*X*V)*(lam*PRZZCombinedBudget.total X (X*V/T) V) :=
      mul_le_mul_of_nonneg_left
        (frequency_bound X V A (X*V/T) lam hX.le hV.le hA (by positivity) hlam hfreq)
        (by positivity)
    _ = lam*(T/(d*X*V)*PRZZCombinedBudget.total X (X*V/T) V) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (combined_bound N T X V d hN hNT hX hXN hV hVN hd) (by linarith)

#print axioms frequency_bound
#print axioms source_frequency_bound
/-- The absolute small-cell term is normalized before summing boxes. -/
theorem small_frequency_bound (N T X V d A lam : ℝ)
    (hN : 1 ≤ N) (hT : 0 < T) (hX : 0 < X) (hV : 0 < V) (hVN : V ≤ N)
    (hd : 0 < d) (hl : 0 ≤ lam) (hA : A ≤ lam*(X*V/T)) :
    T/(d*X*V)*(A*V) ≤ lam*target N T/d := by
  have hn : V ≤ target N T := by
    have hh : N ≤ N^(7/4:ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_le hN (by norm_num : (1:ℝ) ≤ 7/4)
    exact (hVN.trans hh).trans (le_add_of_nonneg_right (by positivity))
  calc
    _ ≤ T/(d*X*V)*(lam*(X*V/T)*V) := by gcongr
    _ = lam*V/d := by field_simp
    _ ≤ _ := by gcongr

/-- Keep the original outer V while DI uses a clipped modulus endpoint W.
The factor two is the dyadic width, not a loss depending on N or T. -/
theorem clipped_frequency_bound (N T X V W d A lam : ℝ)
    (hN : 1 ≤ N) (hNT : N ≤ T) (hX : 0 < X) (hXN : X ≤ N)
    (hV : 0 < V) (hVW : V ≤ W) (hWV : W ≤ 2*V) (hWN : W ≤ N)
    (hd : 0 < d) (hA : 0 ≤ A) (hl : 1 ≤ lam) (hfreq : A ≤ lam*(X*V/T)) :
    T/(d*X*V)*PRZZCombinedBudget.total X A W ≤ 22*lam*target N T/d := by
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (hN.trans hNT)
  have hW : 0 < W := hV.trans_le hVW
  have hf : A ≤ lam*(X*W/T) := hfreq.trans (by gcongr)
  have hb := source_frequency_bound N T X W d A lam hN hNT hX hXN hW hWN hd hA hl hf
  have hratio : W/V ≤ 2 := (div_le_iff₀ hV).mpr (by linarith)
  calc
    _ = (W/V)*(T/(d*X*W)*PRZZCombinedBudget.total X A W) := by field_simp
    _ ≤ 2*(lam*(11*target N T/d)) := mul_le_mul hratio hb
      (by unfold PRZZCombinedBudget.total PRZZCombinedBudget.typeI PRZZDISeven.envelope; positivity)
      (by norm_num)
    _ = _ := by ring

#print axioms small_frequency_bound
#print axioms clipped_frequency_bound
end XiPrime8845.PRZZOptimalPowers
