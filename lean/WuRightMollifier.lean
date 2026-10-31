import WuLeftReturn
import Zeta23.RvM.ZetaGrowth

/-! The actual height-dependent mollifier on a right half-plane. The cutoff,
profiles and R/log T translation are retained. Uniformity in the imaginary
part comes from a summable coefficient error, not from a fixed-T right limit. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Filter Topology Finset
namespace XiPrime8845.WuRightMollifier
open WuAuxiliary
set_option maxHeartbeats 2000000

theorem coefficient_tendsto (θ : ℝ) (hθ : 0 < θ) (n : ℕ) :
    Tendsto (fun T => PRZZ.coefficient PRZZ.witness θ T n) atTop (nhds (μ n:ℂ)) := by
  by_cases hn : n = 0
  · subst n
    simp [PRZZ.coefficient]
  have hn1 : 1 ≤ n := by omega
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn
  have hlen : Tendsto (PRZZ.length θ) atTop atTop := tendsto_rpow_atTop hθ
  have hl := Real.tendsto_log_atTop.comp hlen
  have hi := tendsto_inv_atTop_zero.comp hl
  have hu : Tendsto (fun T => Real.log (PRZZ.length θ T/n)/Real.log (PRZZ.length θ T))
      atTop (nhds 1) := by
    have hh : Tendsto (fun T => 1-Real.log n*(Real.log (PRZZ.length θ T))⁻¹)
        atTop (nhds 1) := by simpa using tendsto_const_nhds.sub (hi.const_mul (Real.log n))
    apply hh.congr'
    filter_upwards [hlen.eventually (eventually_gt_atTop (1:ℝ))] with T hT
    rw [Real.log_div (by linarith : PRZZ.length θ T ≠ 0) hn0,sub_div,
      div_self (Real.log_pos hT).ne',div_eq_mul_inv]
  have hP := (PRZZ.witness.conrey.continuous.tendsto 1).comp hu
  have hG := (PRZZ.witness.feng.continuous.tendsto 1).comp hu
  have hreal := (hP.const_mul (PRZZ.muReal n)).add
    ((hG.const_mul (PRZZ.fengArithmetic n)).mul (hi.pow 2))
  have hh : Tendsto (fun T => ((PRZZ.muReal n * PRZZ.witness.conrey.eval
      (Real.log (PRZZ.length θ T/n)/Real.log (PRZZ.length θ T))+
      PRZZ.fengArithmetic n * PRZZ.witness.feng.eval
      (Real.log (PRZZ.length θ T/n)/Real.log (PRZZ.length θ T)) /
      (Real.log (PRZZ.length θ T))^2 : ℝ):ℂ)) atTop (nhds (μ n:ℂ)) := by
    simpa [Function.comp_def,PRZZ.witness_endpoints.2.2,PRZZ.muReal,div_eq_mul_inv,inv_pow] using
      (Complex.continuous_ofReal.tendsto _).comp hreal
  apply hh.congr'
  filter_upwards [hlen.eventually (eventually_ge_atTop (n:ℝ))] with T hT
  simp [PRZZ.coefficient,hn1,hT]

def shiftedCoefficient (T : ℝ) (n : ℕ) : ℂ :=
  PRZZ.coefficient PRZZ.witness PRZZAsymptotic.theta T n /
    (n:ℂ)^((PRZZAsymptotic.R/Real.log T:ℝ):ℂ)

theorem shift_tendsto : Tendsto (fun T : ℝ => PRZZAsymptotic.R/Real.log T) atTop (nhds 0) := by
  simpa only [div_eq_mul_inv,mul_zero,Function.comp_def] using
    (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul PRZZAsymptotic.R

theorem shiftedCoefficient_tendsto (n : ℕ) :
    Tendsto (fun T => shiftedCoefficient T n) atTop (nhds (μ n:ℂ)) := by
  by_cases hn : n = 0
  · subst n; simp [shiftedCoefficient,PRZZ.coefficient]
  have hnc : (n:ℂ) ≠ 0 := by exact_mod_cast hn
  have hc : Continuous (fun z : ℂ => (n:ℂ)^z) := continuous_id.const_cpow (Or.inl hnc)
  have ht := hc.tendsto 0 |>.comp ((Complex.continuous_ofReal.tendsto 0).comp shift_tendsto)
  simpa only [shiftedCoefficient,Function.comp_def,Pi.div_def,Complex.ofReal_zero,Complex.cpow_zero,div_one] using
    (coefficient_tendsto PRZZAsymptotic.theta (by norm_num [PRZZAsymptotic.theta]) n).div ht
      (by simp)

theorem shiftedCoefficient_bound (T : ℝ) (hT : 2 ≤ T) (n : ℕ) :
    ‖shiftedCoefficient T n‖ ≤ 7 := by
  by_cases hn : n = 0
  · subst n; simp [shiftedCoefficient,PRZZ.coefficient]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hnpos
  have hR : 0 ≤ PRZZAsymptotic.R/Real.log T :=
    div_nonneg PRZZAsymptotic.radius_pos.le (Real.log_nonneg (by linarith))
  rw [shiftedCoefficient,norm_div,Complex.norm_natCast_cpow_of_pos hnpos,Complex.ofReal_re]
  have hp := Real.one_le_rpow hn1 hR
  exact (div_le_self (norm_nonneg _) hp).trans
    ((PRZZ.witness_coefficient_bound _ T (by norm_num [PRZZAsymptotic.theta]) hT n).trans (by norm_num))

def errorMass (T : ℝ) : ℝ := ∑' n : ℕ, ‖shiftedCoefficient T n-(μ n:ℂ)‖/(n:ℝ)^2

theorem error_term_bound (T : ℝ) (hT : 2 ≤ T) (n : ℕ) :
    ‖shiftedCoefficient T n-(μ n:ℂ)‖/(n:ℝ)^2 ≤ 8*(1/(n:ℝ)^2) := by
  have hm : ‖(μ n:ℂ)‖ ≤ 1 := FengMixedInterior.moebius_norm n
  have hh := (norm_sub_le (shiftedCoefficient T n) (μ n:ℂ)).trans
    (add_le_add (shiftedCoefficient_bound T hT n) hm)
  exact (div_le_div_of_nonneg_right hh (sq_nonneg _)).trans_eq (by ring)

theorem errorMass_tendsto : Tendsto errorMass atTop (nhds 0) := by
  change Tendsto (fun T => errorMass T) atTop (nhds 0)
  have hb : Summable (fun n : ℕ => 8*(1/(n:ℝ)^2)) := hasSum_zeta_two.summable.mul_left 8
  have h := tendsto_tsum_of_dominated_convergence hb
    (g := fun _ : ℕ => (0:ℝ)) (f := fun T n => ‖shiftedCoefficient T n-(μ n:ℂ)‖/(n:ℝ)^2)
    (fun n => by simpa using ((shiftedCoefficient_tendsto n).sub_const (μ n:ℂ)).norm.div_const ((n:ℝ)^2))
    (by
      filter_upwards [eventually_ge_atTop (2:ℝ)] with T hT n
      rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (norm_nonneg _) (sq_nonneg _))]
      exact error_term_bound T hT n)
  simpa only [errorMass,tsum_zero] using h

theorem psi_eq_LSeries (T : ℝ) (hT : 2 ≤ T) (s : ℂ) :
    psi T s = LSeries (shiftedCoefficient T) s := by
  rw [psi,PRZZ.dirichletPolynomial,LSeries]
  rw [tsum_eq_sum (s := Icc 1 (PRZZ.cutoff PRZZAsymptotic.theta T)) (by
    intro n hn
    by_cases hn0 : n = 0
    · simp [hn0]
    · have hc : PRZZ.coefficient PRZZ.witness PRZZAsymptotic.theta T n = 0 := by
        apply PRZZ.coefficient_support
        intro hs
        apply hn
        exact mem_Icc.mpr ⟨hs.1,(Nat.le_floor_iff (Real.rpow_nonneg (by linarith : 0 ≤ T) _)).mpr hs.2⟩
      simp [LSeries.term,hn0,shiftedCoefficient,hc])]
  apply sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
  have hnc : (n:ℂ) ≠ 0 := by exact_mod_cast hn0
  rw [LSeries.term_of_ne_zero hn0,shiftedCoefficient,Complex.cpow_add _ _ hnc]
  ring

theorem inverse_error_bound (T : ℝ) (hT : 2 ≤ T) (s : ℂ) (hs : 2 ≤ s.re) :
    ‖psi T s-LSeries (fun n => (μ n:ℂ)) s‖ ≤ errorMass T := by
  have ha : LSeriesSummable (shiftedCoefficient T) s :=
    LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => shiftedCoefficient_bound T hT n) (by linarith)
  have hm : LSeriesSummable (fun n => (μ n:ℂ)) s :=
    LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => FengMixedInterior.moebius_norm n) (by linarith)
  rw [psi_eq_LSeries T hT,← LSeries_sub ha hm,LSeries]
  have hb : Summable (fun n : ℕ => ‖shiftedCoefficient T n-(μ n:ℂ)‖/(n:ℝ)^2) :=
    (hasSum_zeta_two.summable.mul_left 8).of_nonneg_of_le
      (fun _ => div_nonneg (norm_nonneg _) (sq_nonneg _)) (error_term_bound T hT)
  have ht (n : ℕ) : ‖LSeries.term (shiftedCoefficient T-(fun n => (μ n:ℂ))) s n‖ ≤
      ‖shiftedCoefficient T n-(μ n:ℂ)‖/(n:ℝ)^2 := by
    by_cases hn : n = 0
    · simp [hn]
    have hp : 0 < n := Nat.pos_of_ne_zero hn
    rw [LSeries.term_of_ne_zero hn,Pi.sub_apply,norm_div,Complex.norm_natCast_cpow_of_pos hp]
    apply div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le
      (show (1:ℝ) ≤ n by exact_mod_cast hp) hs
  exact (norm_tsum_le_tsum_norm (ha.sub hm).norm).trans ((ha.sub hm).norm.tsum_le_tsum ht hb)

/-- Uniform over the entire right half-plane, including unbounded heights. -/
theorem zeta_psi_uniform :
    TendstoUniformlyOn (fun T s => riemannZeta s*psi T s) (fun _ => 1)
      atTop {s : ℂ | 2 ≤ s.re} := by
  have ht := errorMass_tendsto.const_mul (Real.pi^2/6)
  simp only [mul_zero] at ht
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [eventually_ge_atTop (2:ℝ),ht.eventually (gt_mem_nhds hε)] with T hT hsmall
  intro s hs
  have he : riemannZeta s*LSeries (fun n => (μ n:ℂ)) s = 1 := by
    simpa only [ArithmeticFunction.LSeries_zeta_eq_riemannZeta (show 1<s.re by linarith)] using
      ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius (show 1<s.re by linarith)
  rw [dist_comm,dist_eq_norm,← he,← mul_sub,norm_mul]
  exact (mul_le_mul (Zeta23.RvM.norm_riemannZeta_le_of_two_le_re hs)
    (inverse_error_bound T hT s hs) (norm_nonneg _) (by positivity)).trans_lt hsmall

/-- A common envelope for finite or infinite Dirichlet series. -/
theorem LSeries_bound (a : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (ha : ∀ n, ‖a n‖ ≤ M) (s : ℂ) (hs : 2 ≤ s.re) :
    ‖LSeries a s‖ ≤ M*(Real.pi^2/6) := by
  have has : LSeriesSummable a s := LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => ha n) (by linarith)
  have ht (n : ℕ) : ‖LSeries.term a s n‖ ≤ M*(1/(n:ℝ)^2) := by
    by_cases hn : n = 0
    · simp [hn]
    have hp := Nat.pos_of_ne_zero hn
    rw [LSeries.term_of_ne_zero hn,norm_div,Complex.norm_natCast_cpow_of_pos hp]
    apply (div_le_div_of_nonneg_right (ha n) (Real.rpow_nonneg (Nat.cast_nonneg _) _)).trans
    rw [mul_one_div]
    apply div_le_div_of_nonneg_left hM (by positivity)
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le
      (show (1:ℝ) ≤ n by exact_mod_cast hp) hs
  have hh := (norm_tsum_le_tsum_norm has.norm).trans
    (has.norm.tsum_le_tsum ht (hasSum_zeta_two.summable.mul_left M))
  exact hh.trans_eq ((hasSum_zeta_two.mul_left M).tsum_eq)

theorem psi_bound (T : ℝ) (hT : 2 ≤ T) (s : ℂ) (hs : 2 ≤ s.re) :
    ‖psi T s‖ ≤ 7*(Real.pi^2/6) := by
  rw [psi_eq_LSeries T hT]
  exact LSeries_bound _ 7 (by norm_num) (shiftedCoefficient_bound T hT) s hs

#print axioms coefficient_tendsto
#print axioms shift_tendsto
#print axioms shiftedCoefficient_tendsto
#print axioms shiftedCoefficient_bound
#print axioms error_term_bound
#print axioms errorMass_tendsto
#print axioms psi_eq_LSeries
#print axioms inverse_error_bound
#print axioms zeta_psi_uniform
#print axioms LSeries_bound
#print axioms psi_bound
end XiPrime8845.WuRightMollifier
