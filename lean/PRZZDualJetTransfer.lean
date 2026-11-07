import PRZZDualHigherJets

/-! Transfer genuine logarithmic jets to every derivative of the actual
dual Gamma multiplier. Constants are finite binomial recurrences, selected
before height and the logarithmically scaled shift family. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex Set Filter Topology MeasureTheory Finset
namespace XiPrime8845.PRZZDualJetTransfer
open PRZZDualFirstJet PRZZDualHigherJets
set_option maxHeartbeats 10000000

theorem factor_derivative (a d : ℂ) (e t : ℝ)
    (h0 : 0 < (point a e t).re) (h1 : 0 < (point a e t+d).re) :
    HasDerivAt (factor a d e)
      (factor a d e t*difference 0 a d e t*((e:ℂ)*I/2)) t := by
  have hh := ratio_derivative ((1/2+a)/2+d) ((1/2+a)/2) ((e:ℂ)*I/2) t
    (by simpa only [point,add_right_comm] using h1) h0
  convert hh using 1 <;>
    first | (funext u; unfold factor; rw [add_right_comm _ d]) |
      (simp only [factor,difference,iteratedDeriv_zero,point,add_right_comm])

theorem multiplier_derivative (a b : ℂ) (ha : ‖a‖ ≤ 1/16) (hb : ‖b‖ ≤ 1/16)
    (t : ℝ) (ht : 2 ≤ t) :
    HasDerivAt (PRZZAFEDual.dualMultiplier a b)
      (PRZZAFEDual.dualMultiplier a b t*costJet 0 a b t) t := by
  let d := -(a+b)/2
  have hL := geometry 2 t 1 a d (by norm_num) ht (by norm_num) ha (shift_norm a b ha hb)
  have hR := geometry 2 t (-1) b d (by norm_num) ht (by norm_num) hb (shift_norm a b ha hb)
  have hl := factor_derivative a d 1 t
    (by have hh := hL.1 0 (by norm_num); simp only [ofReal_zero,zero_mul,add_zero] at hh; linarith)
    (by have hh := hL.1 1 (by norm_num); simp only [ofReal_one,one_mul] at hh; linarith)
  have hr := factor_derivative b d (-1) t
    (by have hh := hR.1 0 (by norm_num); simp only [ofReal_zero,zero_mul,add_zero] at hh; linarith)
    (by have hh := hR.1 1 (by norm_num); simp only [ofReal_one,one_mul] at hh; linarith)
  have hh := (hl.mul hr).const_mul ((Real.pi:ℂ)^(a+b))
  have heq : PRZZAFEDual.dualMultiplier a b = fun u : ℝ =>
      (Real.pi:ℂ)^(a+b)*(factor a d 1 u*factor b d (-1) u) := funext (multiplier_factors a b)
  rw [heq]
  convert hh using 1 <;>
    first | rfl | (simp only [costJet,pow_one,Complex.ofReal_one,Complex.ofReal_neg,one_mul,neg_mul,d]; ring)

theorem psi_line_smooth (n : ℕ) (c k : ℂ) (hc : 1/16 < c.re) (hk : k.re = 0) :
    ContDiff ℝ ∞ (fun t : ℝ => iteratedDeriv n digamma (c+(t:ℂ)*k)) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  have hz : 1/16 < (c+(t:ℂ)*k).re := by simpa [hk] using hc
  have hpath : ContDiff ℝ ∞ (fun t : ℝ => c+(t:ℂ)*k) :=
    contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const)
  exact ((psi_analytic n _ hz).contDiffAt.restrict_scalars ℝ).comp t hpath.contDiffAt

theorem difference_smooth (n : ℕ) (a d : ℂ) (e : ℝ) (he : |e| = 1)
    (ha : ‖a‖ ≤ 1/16) (hd : ‖d‖ ≤ 1/16) : ContDiff ℝ ∞ (difference n a d e) := by
  have hg := geometry 2 2 e a d (by norm_num) le_rfl he ha hd
  have hc : 1/16 < ((1/2+a)/2).re := by
    have hh := hg.1 0 (by norm_num)
    simp only [point,ofReal_zero,zero_mul,add_zero] at hh
    have hk : (((e:ℂ)*I/2)).re = 0 := by simp
    simp only [add_re,mul_re,ofReal_re,ofReal_im,hk,zero_mul,mul_zero,sub_zero,add_zero] at hh
    linarith
  have hc' : 1/16 < ((1/2+a)/2+d).re := by
    have hh := hg.1 1 (by norm_num)
    simp [point] at hh ⊢
    linarith
  have h0 := psi_line_smooth n ((1/2+a)/2) ((e:ℂ)*I/2) hc (by simp)
  have h1 := psi_line_smooth n ((1/2+a)/2+d) ((e:ℂ)*I/2) hc' (by simp)
  convert h1.sub h0 using 1
  funext t
  unfold difference point
  rw [add_right_comm _ d]

theorem cost_smooth (a b : ℂ) (ha : ‖a‖ ≤ 1/16) (hb : ‖b‖ ≤ 1/16) :
    ContDiff ℝ ∞ (costJet 0 a b) := by
  have hL := difference_smooth 0 a (-(a+b)/2) 1 (by norm_num) ha (shift_norm a b ha hb)
  have hR := difference_smooth 0 b (-(a+b)/2) (-1) (by norm_num) hb (shift_norm a b ha hb)
  exact (contDiff_const.mul hL).add (contDiff_const.mul hR)

def constant : ℕ → ℝ
  | 0 => 1
  | n+1 => ∑ i ∈ range (n+1), if hi : i ≤ n then
      (n.choose i:ℝ)*constant i*logConstant (n-i) else 0
termination_by n => n
decreasing_by omega

theorem constant_succ (n : ℕ) :
    constant (n+1) = ∑ i ∈ range (n+1), (n.choose i:ℝ)*constant i*logConstant (n-i) := by
  rw [constant]
  apply sum_congr rfl; intro i hi
  rw [dif_pos (by have := mem_range.mp hi; omega)]

theorem constant_nonneg (n : ℕ) : 0 ≤ constant n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [constant]
    | succ n =>
      rw [constant_succ]
      apply sum_nonneg; intro i hi
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (ih i (by have := mem_range.mp hi; omega)))
        (logConstant_nonneg _)

theorem relative_bound (n : ℕ) (T t : ℝ) (a b : ℂ) (hT : 4 ≤ T) (ht : T ≤ t)
    (ha : ‖a‖ ≤ 1/16) (hb : ‖b‖ ≤ 1/16) :
    ‖iteratedDeriv n (PRZZAFEDual.dualMultiplier a b) t‖ ≤
      ‖PRZZAFEDual.dualMultiplier a b t‖*constant n/T^n := by
  have hT0 : 0 < T := by linarith
  have ht2 : 2 < t := by linarith
  have hG := PRZZDualSmooth.multiplier_contDiff a b (by linarith) (by linarith)
  have hL := cost_smooth a b ha hb
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [constant]
    | succ n =>
      have he : deriv (PRZZAFEDual.dualMultiplier a b) =ᶠ[𝓝 t]
          (fun u => PRZZAFEDual.dualMultiplier a b u*costJet 0 a b u) := by
        filter_upwards [eventually_gt_nhds ht2] with u hu
        exact (multiplier_derivative a b ha hb u hu.le).deriv
      rw [iteratedDeriv_succ']
      rw [he.iteratedDeriv_eq]
      have low : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤)
      rw [iteratedDeriv_fun_mul (hG.contDiffAt.of_le low) (hL.contDiffAt.of_le low)]
      apply (norm_sum_le _ _).trans
      rw [constant_succ,mul_sum,Finset.sum_div]
      apply sum_le_sum; intro i hi
      have hin : i ≤ n := by have := mem_range.mp hi; omega
      have hCi := constant_nonneg i
      simp only [norm_mul,Complex.norm_natCast,cost_iterated (n-i) a b ha hb t ht2]
      rw [mul_assoc]
      have hh := mul_le_mul
        (ih i (by omega)) (cost_bound (n-i) T t a b (by linarith) ht ha hb)
        (norm_nonneg _) (div_nonneg (mul_nonneg (norm_nonneg _) hCi) (pow_nonneg hT0.le i))
      have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ (n.choose i:ℝ) by positivity)
      apply hh'.trans_eq
      have hp : T^i*T^(n-i+1) = T^(n+1) := by rw [← pow_add]; congr 1; omega
      rw [← hp]
      field_simp
      <;> ring

theorem scaled_cap (S : ℝ) (hS : 0 ≤ S) :
    ∀ᶠ T : ℝ in atTop, ∀ A B : ℂ, ‖A‖ ≤ S → ‖B‖ ≤ S →
      ∀ n : ℕ, ∀ t ∈ Set.Icc T (2*T),
        ‖iteratedDeriv n (PRZZAFEDual.dualMultiplier (A/(Real.log T:ℂ)) (B/(Real.log T:ℂ))) t‖ ≤
          Real.exp (2*S+7)*constant n/T^n := by
  filter_upwards [PRZZDualError.multiplier_scaled_cap S hS,
    PRZZScaledReplacement.shifts_eventually S (1/16) (by norm_num),
    eventually_ge_atTop (4:ℝ)] with T hcap hsmall hT
  intro A B hA hB n t ht
  apply (relative_bound n T t _ _ hT ht.1 (hsmall.2 A hA) (hsmall.2 B hB)).trans
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hcap A B hA hB t ht)
    (constant_nonneg n)) (by positivity)

#print axioms factor_derivative
#print axioms multiplier_derivative
#print axioms psi_line_smooth
#print axioms difference_smooth
#print axioms cost_smooth
#print axioms constant_succ
#print axioms constant_nonneg
#print axioms relative_bound
#print axioms scaled_cap
end XiPrime8845.PRZZDualJetTransfer
