import WuEtaMainPhase

/-! Return the actual quotient logarithm to the original left line.
The auxiliary is entire; H is only used on a compact positive-height,
positive-real-part strip. Equalities of logarithms are almost everywhere,
not identities at the totalized value log 0. -/
noncomputable section
open Set Filter Topology MeasureTheory Complex
namespace XiPrime8845.WuQuotientReturn
open WuLittlewood WuAuxiliary WuAuxiliaryBoundary WuStirling WuLeftReturn WuBoundaryZeros
set_option maxHeartbeats 2000000

def logDensity (T a t : ℝ) : ℝ :=
  Real.log ‖auxiliary T (point a t)‖-Real.log ‖H (point a t)‖

def logIntegral (T a u v : ℝ) : ℝ := ∫ t in Icc u v, logDensity T a t

theorem Hlog_continuous (a b u v : ℝ) (ha : 0 < a) (hu : 0 < u) :
    ContinuousOn (fun p : ℝ × ℝ => Real.log ‖H (point p.1 p.2)‖)
      (Icc a b ×ˢ Icc u v) := by
  intro p hp
  have hr : 0 < (point p.1 p.2).re := by simp [point]; exact ha.trans_le hp.1.1
  have hn := H_ne_zero _ hr (WuGammaPhase.point_ne_one _ _ (hu.trans_le hp.2.1))
  have hc : Continuous (fun p : ℝ × ℝ => point p.1 p.2) := by unfold point; fun_prop
  exact (((H_analytic _ hr).continuousAt.comp (f := fun p : ℝ × ℝ => point p.1 p.2)
    hc.continuousAt).norm.log
    (norm_ne_zero_iff.mpr hn)).continuousWithinAt

theorem logDensity_integrable (T a u v : ℝ) (ha : 0 < a) (hu : 0 < u) (huv : u ≤ v) :
    IntegrableOn (logDensity T a) (Icc u v) := by
  have hc : ContinuousOn (fun t => Real.log ‖H (point a t)‖) (Icc u v) := by
    intro t ht
    have hh := Hlog_continuous a a u v ha hu
    exact (hh.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨⟨le_rfl,le_rfl⟩,ht⟩)) t ht
  exact (vertical_log_integrable _ (auxiliary_entire T) a u v huv).sub
    (hc.integrableOn_compact isCompact_Icc)

theorem quotient_log_ae (T a u v : ℝ) (hT : 1 < T) (ha : 0 < a) (hu : 0 < u) :
    (fun t => Real.log ‖V T (point a t)*psi T (point a t)‖) =ᵐ[volume.restrict (Icc u v)]
      logDensity T a := by
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae (vertical_ae_nonzero _ (auxiliary_entire T)
      (auxiliary_not_identically_zero T hT) a)] with t ht hn
  have hH := H_ne_zero (point a t) (by simpa [point] using ha)
    (WuGammaPhase.point_ne_one a t (hu.trans_le ht.1))
  rw [show V T (point a t)*psi T (point a t) = auxiliary T (point a t)/H (point a t) by
    unfold V auxiliary; ring,norm_div,Real.log_div (norm_ne_zero_iff.mpr hn) (norm_ne_zero_iff.mpr hH)]
  rfl

theorem quotient_integral_eq (T a u v : ℝ) (hT : 1 < T) (ha : 0 < a)
    (hu : 0 < u) (huv : u ≤ v) :
    (∫ t in u..v, Real.log ‖V T (point a t)*psi T (point a t)‖) = logIntegral T a u v := by
  rw [intervalIntegral.integral_of_le huv,← integral_Icc_eq_integral_Ioc]
  exact integral_congr_ae (quotient_log_ae T a u v hT ha hu)

/-- Reverse Fatou applies to the difference. The continuous H logarithm
has a compact bound; no global analyticity of V psi is asserted. -/
theorem logIntegral_return (T a u v ε : ℝ) (hT : 1 < T) (ha : 0 < a)
    (hu : 0 < u) (huv : u ≤ v) (hε : 0 < ε) :
    ∀ᶠ x in nhds a, logIntegral T x u v < logIntegral T a u v+ε := by
  let K := Icc (a/2) (a+1) ×ˢ Icc u v
  have hH := Hlog_continuous (a/2) (a+1) u v (by linarith) hu
  have hc : ContinuousOn (fun p : ℝ × ℝ => ‖auxiliary T (point p.1 p.2)‖-
      Real.log ‖H (point p.1 p.2)‖) K := by
    apply ContinuousOn.sub _ hH
    apply Continuous.continuousOn
    apply ((auxiliary_entire T).continuous.comp ?_).norm
    unfold point; fun_prop
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).bddAbove_image hc
  have hx : ∀ᶠ x in nhds a, x ∈ Icc (a/2) (a+1) :=
    Icc_mem_nhds (by linarith) (by linarith)
  apply integral_eventually_lt_of_upper_bound (fun x t => logDensity T x t)
    (logDensity T a) (fun _ => C) ?_
    (logDensity_integrable T a u v ha hu huv) (integrable_const C) ?_ ?_ ε hε
  · filter_upwards [hx] with x hx
    exact logDensity_integrable T x u v (by linarith [hx.1]) hu huv
  · filter_upwards [hx] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (sub_le_sub_right (Real.log_le_self (norm_nonneg _)) _).trans
      (hC ⟨(x,t),⟨hx,ht⟩,rfl⟩)
  · filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (vertical_ae_nonzero _ (auxiliary_entire T)
        (auxiliary_not_identically_zero T hT) a)] with t ht hn
    have hp : Continuous (fun x : ℝ => point x t) := by unfold point; fun_prop
    have hr : 0 < (point a t).re := by simpa [point] using ha
    have hHn := H_ne_zero _ hr (WuGammaPhase.point_ne_one a t (hu.trans_le ht.1))
    exact (((auxiliary_entire T).continuous.comp hp).norm.continuousAt.log
      (norm_ne_zero_iff.mpr hn)).tendsto.sub
      ((((H_analytic _ hr).continuousAt.comp (f := fun x : ℝ => point x t)
        hp.continuousAt).norm.log
        (norm_ne_zero_iff.mpr hHn)).tendsto)

theorem exists_safe_left (T a u v ε w : ℝ) (hT : 1 < T) (ha : 0 < a)
    (hu : 0 < u) (huv : u ≤ v) (hε : 0 < ε) (hw : 0 < w) :
    ∃ x ∈ Ioo (a-w) a, (∀ t : ℝ, auxiliary T (point x t) ≠ 0) ∧
      logIntegral T x u v < logIntegral T a u v+ε := by
  obtain ⟨l,r,⟨hl,hr⟩,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (logIntegral_return T a u v ε hT ha hu huv hε)
  let bad : Set ℝ := Complex.re '' {s | auxiliary T s = 0}
  have hc : bad.Countable := (auxiliary_zeros_countable T hT).image _
  obtain ⟨x,hx,hint⟩ := (hc.dense_compl ℝ).exists_between
    (show max (a-w) l < a from max_lt (by linarith) hl)
  refine ⟨x,⟨(le_max_left _ _).trans_lt hint.1,hint.2⟩,?_,?_⟩
  · intro t hz
    exact hx ⟨point x t,hz,by simp [point]⟩
  · exact hsub ⟨(le_max_right _ _).trans_lt hint.1,hint.2.trans hr⟩

theorem original_budget (δ : ℝ) (hδ : 0 < δ) (hd : δ < 1/2) :
    ∀ᶠ T : ℝ in atTop, ∀ u ∈ Icc ((1+δ)*T) ((1+δ)*T+1),
      ∀ v ∈ Icc ((2-δ)*T-1) ((2-δ)*T),
      logIntegral T (1/2-PRZZAsymptotic.R/Real.log T) u v ≤
        (v-u)*Real.log WitnessMomentBound.countingCap/2 :=
  WuBoundaryZeros.left_log_eventually_le δ hδ hd

#print axioms Hlog_continuous
#print axioms logDensity_integrable
#print axioms quotient_log_ae
#print axioms quotient_integral_eq
#print axioms logIntegral_return
#print axioms exists_safe_left
#print axioms original_budget
end XiPrime8845.WuQuotientReturn
