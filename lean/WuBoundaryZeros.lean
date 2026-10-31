import WuAuxiliaryBoundary
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic

/-! Zeros of the actual moving auxiliary, with T frozen before any edge is
chosen. The left logarithm is integrable even when the line contains zeros.
This does not extend Littlewood across boundary zeros or supply a uniform
horizontal argument bound. The fixed-T right limit below is not such a bound. -/
noncomputable section
open scoped BigOperators
open Set Filter Topology MeasureTheory
namespace XiPrime8845.WuBoundaryZeros
open WuAuxiliary WuAuxiliaryBoundary WuSubintervalLog WuUnsmoothing
set_option maxHeartbeats 2000000

theorem coefficient_one (T : ℝ) (hT : 1 < T) :
    PRZZ.coefficient PRZZ.witness PRZZAsymptotic.theta T 1 = 1 := by
  have hlen : 1 < PRZZ.length PRZZAsymptotic.theta T :=
    Real.one_lt_rpow hT (by norm_num [PRZZAsymptotic.theta])
  have hl := (Real.log_pos hlen).ne'
  simp [PRZZ.coefficient, hlen.le, div_self hl, PRZZ.muReal,
    PRZZ.fengArithmetic, PRZZ.witness_endpoints.2.2]

/-- A finite Dirichlet polynomial with constant coefficient one tends to one
as its real argument tends right. N and every coefficient are fixed here. -/
theorem dirichletPolynomial_tendsto (a : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N) :
    Tendsto (fun σ : ℝ => PRZZ.dirichletPolynomial a N (σ:ℂ)) atTop (nhds (a 1)) := by
  have ht (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      Tendsto (fun σ : ℝ => a n/(n:ℂ)^(σ:ℂ)) atTop (nhds (if n=1 then a 1 else 0)) := by
    by_cases he : n = 1
    · subst n; simp
    · rw [if_neg he]
      have hn1 : (1:ℝ) < n := by
        have := (Finset.mem_Icc.mp hn).1
        exact_mod_cast (show 1 < n by omega)
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      have hh := (tendsto_inv_atTop_zero.comp (tendsto_rpow_atTop_of_base_gt_one (n:ℝ) hn1)).const_mul ‖a n‖
      have heq (σ : ℝ) : ‖a n/(n:ℂ)^(σ:ℂ)‖ = ‖a n‖*((n:ℝ)^σ)⁻¹ := by
        rw [norm_div]
        change ‖a n‖/‖((n:ℝ):ℂ)^(σ:ℂ)‖ = _
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : (0:ℝ)<n)]
        rfl
      simpa only [heq,Function.comp_def,mul_zero] using hh
  have hh := tendsto_finsetSum (Finset.Icc 1 N) ht
  simpa [PRZZ.dirichletPolynomial, hN] using hh

theorem psi_tendsto_right (T : ℝ) (hT : 1 < T) :
    Tendsto (fun σ : ℝ => psi T (σ:ℂ)) atTop (nhds 1) := by
  have hlen : 1 < PRZZ.length PRZZAsymptotic.theta T :=
    Real.one_lt_rpow hT (by norm_num [PRZZAsymptotic.theta])
  have hN : 1 ≤ PRZZ.cutoff PRZZAsymptotic.theta T :=
    (Nat.le_floor_iff (by linarith : 0 ≤ PRZZ.length PRZZAsymptotic.theta T)).mpr (by exact_mod_cast hlen.le)
  have hh := (dirichletPolynomial_tendsto
    (PRZZ.coefficient PRZZ.witness PRZZAsymptotic.theta T) _ hN).comp
    (tendsto_atTop_add_const_right atTop (PRZZAsymptotic.R/Real.log T) tendsto_id)
  simpa only [Function.comp_def,id_eq,Complex.ofReal_add,coefficient_one T hT,psi] using hh

theorem psi_not_identically_zero (T : ℝ) (hT : 1 < T) : ∃ s : ℂ, psi T s ≠ 0 := by
  by_contra! hh
  have ht := psi_tendsto_right T hT
  simp only [hh] at ht
  have he : (0:ℂ) = 1 := tendsto_nhds_unique tendsto_const_nhds ht
  norm_num at he

theorem auxiliary_not_identically_zero (T : ℝ) (hT : 1 < T) :
    ∃ s : ℂ, auxiliary T s ≠ 0 := by
  obtain ⟨s,hs⟩ := eta_not_identically_zero (Real.log T) (Real.log_pos hT).ne'
  obtain ⟨z,hz⟩ := psi_not_identically_zero T hT
  by_contra! hh
  have heta : AnalyticOnNhd ℂ (eta (Real.log T)) univ := fun s _ => (eta_entire _).analyticAt s
  have hpsi : AnalyticOnNhd ℂ (psi T) univ := fun s _ => (psi_entire T).analyticAt s
  have he := heta.eq_zero_or_eq_zero_of_mul_eq_zero hpsi (fun w _ => hh w) isPreconnected_univ
  rcases he with he | he
  · exact hs (he s (mem_univ _))
  · exact hz (he z (mem_univ _))

theorem entire_zeros_countable (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hn : ∃ s, f s ≠ 0) : {s | f s = 0}.Countable := by
  obtain ⟨s,hs⟩ := hn
  have ha : AnalyticOnNhd ℂ f univ := fun s _ => hf.analyticAt s
  have hh := ha.preimage_zero_mem_codiscrete hs
  have hc : IsClosed {s | f s = 0} ∧ IsDiscrete {s | f s = 0} :=
    compl_mem_codiscrete_iff.mp hh
  exact hc.1.isLindelof.countable_of_isDiscrete hc.2

theorem auxiliary_zeros_countable (T : ℝ) (hT : 1 < T) :
    {s | auxiliary T s = 0}.Countable :=
  entire_zeros_countable _ (auxiliary_entire T) (auxiliary_not_identically_zero T hT)

/-- At each fixed height the ACTUAL auxiliary supplies the countability
required by independent inward endpoint selection. No diagonal avoidance. -/
theorem safe_window_log_input :
    ∃ ρ0 : ℝ, 0 < ρ0 ∧ ∀ δ : ℝ, 0 < δ → δ < 1/2 →
      ∀ᶠ T : ℝ in atTop,
        ∃ u ∈ Ioo ((1+δ)*T) ((1+δ)*T+1),
          ∃ v ∈ Ioo ((2-δ)*T-1) ((2-δ)*T),
          u < v ∧ u ∉ WuSafeEndpoints.badHeights (auxiliary T) ∧
            v ∉ WuSafeEndpoints.badHeights (auxiliary T) ∧
          ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ0 →
            subLogMean T u v ρ ≤ Real.log WitnessMomentBound.countingCap/2 := by
  obtain ⟨ρ0,hρ0,h⟩ := WuSubintervalLog.safe_window_log_input
  refine ⟨ρ0,hρ0,?_⟩
  intro δ hδ hd
  filter_upwards [h δ hδ hd,eventually_gt_atTop (1:ℝ)] with T hh hT
  exact hh (auxiliary T) (WuSafeEndpoints.badHeights_countable _ (auxiliary_zeros_countable T hT))

/-- The restriction to a vertical line is real analytic, hence its logarithm
is locally integrable even at isolated zeros. -/
theorem vertical_log_integrable (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (a u v : ℝ) (huv : u ≤ v) :
    IntegrableOn (fun t : ℝ => Real.log ‖f ((a:ℂ)+(t:ℂ)*Complex.I)‖) (Icc u v) := by
  have ha (t : ℝ) : AnalyticAt ℝ (fun t : ℝ => f ((a:ℂ)+(t:ℂ)*Complex.I)) t :=
    (hf.analyticAt _).restrictScalars.comp
      (analyticAt_const.add ((Complex.ofRealCLM.analyticAt t).mul analyticAt_const))
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le huv).mp
    (MeromorphicOn.intervalIntegrable_log_norm
      (f := fun t : ℝ => f ((a:ℂ)+(t:ℂ)*Complex.I)) (fun t _ => (ha t).meromorphicAt))

theorem auxiliary_left_ae_nonzero (T : ℝ) (hT : 1 < T) :
    ∀ᵐ t : ℝ, auxiliary T (leftPoint T t) ≠ 0 := by
  have hinj : Function.Injective (leftPoint T) := by
    intro t r he
    have hh := congrArg Complex.im he
    simpa [leftPoint] using hh
  have hc := (auxiliary_zeros_countable T hT).preimage hinj
  simpa only [ae_iff,not_not,Set.preimage_ofPred_eq] using hc.measure_zero volume

/-- The actual left-edge estimate now permits zeros ON that edge. Their
logarithmic singularities are integrable and the exceptional set is null. -/
theorem left_log_integral_le (T u v ρ c : ℝ) (hT : 1 < T) (huv : u < v) (hρ : 0 < ρ)
    (hH : ∀ t ∈ Icc u v, WuStirling.H (leftPoint T t) ≠ 0)
    (hHc : ContinuousOn (fun t => WuStirling.H (leftPoint T t)) (Icc u v))
    (hd : ContinuousOn (density T) (Icc u v))
    (hmean : subLogMean T u v ρ ≤ Real.log c/2) :
    (∫ t in Icc u v, Real.log ‖auxiliary T (leftPoint T t)‖-
      Real.log ‖WuStirling.H (leftPoint T t)‖) ≤ (v-u)*Real.log c/2 := by
  have hi := (vertical_log_integrable _ (auxiliary_entire T)
    (1/2-PRZZAsymptotic.R/Real.log T) u v huv.le).sub
      ((hHc.norm.log (fun t ht => norm_ne_zero_iff.mpr (hH t ht))).integrableOn_compact isCompact_Icc)
  have hr : IntegrableOn (fun t => Real.log (density T t+ρ)) (Icc u v) :=
    ((hd.add continuousOn_const).log (fun t ht => ne_of_gt (by
      have hn : 0 ≤ density T t := sq_nonneg _
      change 0 < density T t+ρ
      linarith))).integrableOn_compact isCompact_Icc
  have hb : (∫ t in Icc u v, Real.log ‖auxiliary T (leftPoint T t)‖-
      Real.log ‖WuStirling.H (leftPoint T t)‖) ≤
      ∫ t in Icc u v, Real.log (density T t+ρ)/2 := by
    apply setIntegral_mono_ae_restrict hi (hr.div_const 2)
    filter_upwards [ae_restrict_of_ae (auxiliary_left_ae_nonzero T hT),
      ae_restrict_mem measurableSet_Icc] with t ht hmem
    exact log_auxiliary_left_le T t ρ hρ (hH t hmem) ht
  rw [integral_div] at hb
  have hm := (div_le_iff₀ (show 0 < 2*(v-u) by linarith)).mp hmean
  exact hb.trans (by nlinarith)

theorem left_log_eventually_le :
    ∀ δ : ℝ, 0 < δ → δ < 1/2 → ∀ᶠ T : ℝ in atTop,
      ∀ u ∈ Icc ((1+δ)*T) ((1+δ)*T+1), ∀ v ∈ Icc ((2-δ)*T-1) ((2-δ)*T),
      (∫ t in Icc u v, Real.log ‖auxiliary T (leftPoint T t)‖-
        Real.log ‖WuStirling.H (leftPoint T t)‖) ≤
        (v-u)*Real.log WitnessMomentBound.countingCap/2 := by
  obtain ⟨ρ0,hρ0,hmean⟩ := subLogMean_eventually_le
  intro δ hδ hd
  filter_upwards [hmean δ hδ hd,H_left_eventually_nonzero,WuStirlingTransfer.leftPoint_strip,
    WuTrimmedLog.density_continuous] with T hm hH hs hdensity
  intro u hu v hv
  have hsub : Icc u v ⊆ Icc T (2*T) := by
    intro t ht
    constructor <;> nlinarith [hu.1,hv.2,ht.1,ht.2,hs.1]
  apply left_log_integral_le T u v ρ0 _ (by linarith [hs.1]) (hm u hu v hv).1 hρ0
    (fun t ht => hH t (hsub ht)) _ (hdensity.mono hsub)
    ((hm u hu v hv).2 ρ0 hρ0 le_rfl)
  intro t ht
  have hp : Continuous (fun t => leftPoint T t) := by unfold leftPoint; fun_prop
  have hr : 0 < (leftPoint T t).re := by
    simp only [leftPoint,Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_self,add_zero]
    linarith [hs.2.2.1]
  exact ((WuStirling.H_analytic _ hr).continuousAt.comp hp.continuousAt).continuousWithinAt

#print axioms coefficient_one
#print axioms dirichletPolynomial_tendsto
#print axioms psi_tendsto_right
#print axioms psi_not_identically_zero
#print axioms auxiliary_not_identically_zero
#print axioms entire_zeros_countable
#print axioms auxiliary_zeros_countable
#print axioms safe_window_log_input
#print axioms vertical_log_integrable
#print axioms auxiliary_left_ae_nonzero
#print axioms left_log_integral_le
#print axioms left_log_eventually_le
end XiPrime8845.WuBoundaryZeros
