import WuAuxiliaryMultiplicity

/-! One-sided return to the ORIGINAL left line. Reverse Fatou is expressed
as an eventual epsilon bound, avoiding finite-real limsup conventions.
Only an upper envelope for the moving logarithms is used. No continuity of
the singular logarithmic integral, right-edge estimate or phase count is
asserted. The height T is fixed throughout each left-side perturbation. -/
noncomputable section
open scoped BigOperators
open Set Filter Topology MeasureTheory
namespace XiPrime8845.WuLeftReturn
open WuAuxiliary WuAuxiliaryBoundary WuBoundaryZeros WuAuxiliaryMultiplicity WuLittlewood
set_option maxHeartbeats 2000000

/-- Reverse Fatou in the form needed by Littlewood. The max with the limit
has a two-sided integrable bound; the original family has only an upper one. -/
theorem integral_eventually_lt_of_upper_bound {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} {l : Filter ι} [l.IsCountablyGenerated]
    (F : ι → α → ℝ) (f g : α → ℝ)
    (hF : ∀ᶠ i in l, Integrable (F i) μ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hbound : ∀ᶠ i in l, F i ≤ᵐ[μ] g)
    (hlim : ∀ᵐ t ∂μ, Tendsto (fun i => F i t) l (nhds (f t)))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ i in l, (∫ t, F i t ∂μ) < (∫ t, f t ∂μ)+ε := by
  have hm : Tendsto (fun i => ∫ t, max (F i t) (f t) ∂μ) l (nhds (∫ t, f t ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun t => |g t|+|f t|)
    · exact hF.mono (fun i hi => (hi.sup hf).aestronglyMeasurable)
    · filter_upwards [hbound] with i hi
      filter_upwards [hi] with t ht
      rw [Real.norm_eq_abs,abs_le]
      constructor
      · have := le_max_right (F i t) (f t)
        have := neg_abs_le (f t)
        linarith [abs_nonneg (g t)]
      · exact max_le (ht.trans ((le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))))
          ((le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _)))
    · exact hg.abs.add hf.abs
    · filter_upwards [hlim] with t ht
      simpa only [max_self] using ht.max (tendsto_const_nhds (x := f t))
  filter_upwards [hF,hm.eventually (gt_mem_nhds (lt_add_of_pos_right _ hε))] with i hi hh
  exact (integral_mono hi (hi.sup hf) (fun t => le_max_left _ _)).trans_lt hh

theorem vertical_ae_nonzero (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hn : ∃ s, f s ≠ 0) (a : ℝ) : ∀ᵐ t : ℝ, f (point a t) ≠ 0 := by
  have hinj : Function.Injective (point a) := by
    intro t r he
    simpa [point] using congrArg Complex.im he
  have hc := (entire_zeros_countable f hf hn).preimage hinj
  simpa only [ae_iff,not_not,Set.preimage_ofPred_eq] using hc.measure_zero volume

/-- Upper semicontinuity of the vertical log integral, even at a line
containing zeros. The compact-strip norm bound controls logs from above. -/
theorem vertical_log_eventually_lt (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hn : ∃ s, f s ≠ 0) (a u v ε : ℝ) (huv : u ≤ v) (hε : 0 < ε) :
    ∀ᶠ x in nhds a,
      (∫ t in Icc u v, Real.log ‖f (point x t)‖) <
        (∫ t in Icc u v, Real.log ‖f (point a t)‖)+ε := by
  have hc : Continuous (fun p : ℝ × ℝ => ‖f (point p.1 p.2)‖) := by
    apply (hf.continuous.comp ?_).norm
    unfold point
    fun_prop
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).bddAbove_image
    (K := (Icc (a-1) (a+1)) ×ˢ (Icc u v)) hc.continuousOn
  apply integral_eventually_lt_of_upper_bound
    (fun x t => Real.log ‖f (point x t)‖) (fun t => Real.log ‖f (point a t)‖) (fun _ => C)
    (Eventually.of_forall (fun x => vertical_log_integrable f hf x u v huv))
    (vertical_log_integrable f hf a u v huv) (integrable_const C)
    ?_ ?_ ε hε
  · filter_upwards [Icc_mem_nhds (show a-1<a by linarith) (show a<a+1 by linarith)] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (Real.log_le_self (norm_nonneg _)).trans (hC ⟨(x,t),⟨hx,ht⟩,rfl⟩)
  · filter_upwards [ae_restrict_of_ae (vertical_ae_nonzero f hf hn a)] with t ht
    have hp : Continuous (fun x : ℝ => point x t) := by unfold point; fun_prop
    exact ((hf.continuous.comp hp).norm.continuousAt.log (norm_ne_zero_iff.mpr ht)).tendsto

/-- Freeze the actual T-dependent auxiliary before taking the side limit. -/
theorem auxiliary_left_return (T a u v ε : ℝ) (hT : 1 < T) (huv : u ≤ v) (hε : 0 < ε) :
    ∀ᶠ x in nhds a,
      (∫ t in Icc u v, Real.log ‖auxiliary T (point x t)‖) <
        (∫ t in Icc u v, Real.log ‖auxiliary T (point a t)‖)+ε :=
  vertical_log_eventually_lt _ (auxiliary_entire T) (auxiliary_not_identically_zero T hT)
    a u v ε huv hε

/-- Avoid the countable bad abscissae INSIDE the neighborhood supplied by
reverse Fatou. The perturbation width and the integral error are independent. -/
theorem exists_safe_left (T a u v ε w : ℝ) (hT : 1 < T) (huv : u ≤ v)
    (hε : 0 < ε) (hw : 0 < w) :
    ∃ x ∈ Ioo (a-w) a, (∀ t : ℝ, auxiliary T (point x t) ≠ 0) ∧
      (∫ t in Icc u v, Real.log ‖auxiliary T (point x t)‖) <
        (∫ t in Icc u v, Real.log ‖auxiliary T (point a t)‖)+ε := by
  obtain ⟨l,r,⟨hl,hr⟩,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (auxiliary_left_return T a u v ε hT huv hε)
  let bad : Set ℝ := Complex.re '' {s | auxiliary T s = 0}
  have hc : bad.Countable := (auxiliary_zeros_countable T hT).image _
  obtain ⟨x,hx,hint⟩ := (hc.dense_compl ℝ).exists_between
    (show max (a-w) l < a from max_lt (by linarith) hl)
  refine ⟨x,⟨(le_max_left _ _).trans_lt hint.1,hint.2⟩,?_,?_⟩
  · intro t hz
    exact hx ⟨point x t,hz,by simp [point]⟩
  · exact hsub ⟨(le_max_right _ _).trans_lt hint.1,hint.2.trans hr⟩

/-- Only the left edge moves. A zero-free right edge is an explicit input,
not inferred from the fixed-T limit of the mollifier. The original left
integral controls the perturbed Littlewood identity up to epsilon. -/
theorem littlewood_fixed_right (T a b u v ε w : ℝ) (hT : 1 < T) (hab : a ≤ b)
    (huv : u ≤ v) (hε : 0 < ε) (hw : 0 < w)
    (hu : u ∉ WuSafeEndpoints.badHeights (auxiliary T))
    (hv : v ∉ WuSafeEndpoints.badHeights (auxiliary T))
    (hb : ∀ t ∈ Icc u v, auxiliary T (point b t) ≠ 0) :
    ∃ x ∈ Ioo (a-w) a, ∃ Z : Finset ℂ, ∃ q : BoundaryLogs (auxiliary T) x b u v,
      (∀ s, s ∈ Z ↔ s ∈ Complex.Rectangle (point x u) (point b v) ∧ auxiliary T s = 0) ∧
      2*Real.pi*(∑ s ∈ Z, (analyticOrderNatAt (auxiliary T) s:ℝ)*(s.re-x)) =
        boundaryLog (auxiliary T) x b u v q ∧
      (∫ t in Icc u v, Real.log ‖auxiliary T (point x t)‖) <
        (∫ t in Icc u v, Real.log ‖auxiliary T (point a t)‖)+ε := by
  obtain ⟨x,hx,hn,hi⟩ := exists_safe_left T a u v ε w hT huv hε hw
  obtain ⟨Z,q,hZ,hq⟩ := WuSafeEndpoints.littlewood_of_safe_heights (auxiliary T) x b u v
    (hx.2.le.trans hab) huv (fun s _ => (auxiliary_entire T).analyticAt s)
    hu hv (fun t _ => hn t) hb
  exact ⟨x,hx,Z,q,hZ,hq,hi⟩

/-- Both moving the left edge outwards and including additional zeros
increase the weighted sum. Orders are the actual analytic multiplicities. -/
theorem weighted_sum_mono (T a' a : ℝ) (haa : a' ≤ a) (Z Z' : Finset ℂ)
    (hZZ : Z ⊆ Z') (hZ' : ∀ s ∈ Z', a' ≤ s.re) :
    (∑ s ∈ Z, (analyticOrderNatAt (auxiliary T) s:ℝ)*(s.re-a)) ≤
      ∑ s ∈ Z', (analyticOrderNatAt (auxiliary T) s:ℝ)*(s.re-a') := by
  apply (Finset.sum_le_sum (fun s (_ : s ∈ Z) =>
    mul_le_mul_of_nonneg_left (sub_le_sub_left haa s.re) (Nat.cast_nonneg _))).trans
  exact Finset.sum_le_sum_of_subset_of_nonneg hZZ
    (fun s hs _ => mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (hZ' s hs)))

/-- Original-line H integral and moment budget, with only epsilon added.
T and both chosen horizontal heights are frozen BEFORE selecting x. -/
theorem safe_left_budget_eventually (δ : ℝ) (hδ : 0 < δ) (hd : δ < 1/2) :
    ∀ᶠ T : ℝ in atTop,
      ∀ u ∈ Icc ((1+δ)*T) ((1+δ)*T+1), ∀ v ∈ Icc ((2-δ)*T-1) ((2-δ)*T),
      ∀ ε > 0, ∀ w > 0,
      ∃ x ∈ Ioo (1/2-PRZZAsymptotic.R/Real.log T-w) (1/2-PRZZAsymptotic.R/Real.log T),
        (∀ t : ℝ, auxiliary T (point x t) ≠ 0) ∧
        (∫ t in Icc u v, Real.log ‖auxiliary T (point x t)‖) <
          (∫ t in Icc u v, Real.log ‖WuStirling.H (leftPoint T t)‖)+
            (v-u)*Real.log WitnessMomentBound.countingCap/2+ε := by
  have hw : 0 < 1-2*δ := by linarith
  filter_upwards [WuBoundaryZeros.left_log_eventually_le δ hδ hd,
    H_left_eventually_nonzero,WuStirlingTransfer.leftPoint_strip,
    eventually_gt_atTop (3/(1-2*δ))] with T hb hH hs hlarge
  intro u hu v hv ε hε w hw'
  have hT : 1 < T := by linarith [hs.1]
  have huv : u < v := by
    have hh := (div_lt_iff₀ hw).mp hlarge
    nlinarith [hu.2,hv.1]
  have hsub : Icc u v ⊆ Icc T (2*T) := by
    intro t ht
    constructor <;> nlinarith [hu.1,hv.2,ht.1,ht.2,hs.1]
  have hHc : ContinuousOn (fun t => WuStirling.H (leftPoint T t)) (Icc u v) := by
    intro t ht
    have hp : Continuous (fun t => leftPoint T t) := by unfold leftPoint; fun_prop
    have hr : 0 < (leftPoint T t).re := by
      simp only [leftPoint,Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
        Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_self,add_zero]
      linarith [hs.2.2.1]
    exact ((WuStirling.H_analytic _ hr).continuousAt.comp hp.continuousAt).continuousWithinAt
  have hiH : IntegrableOn (fun t => Real.log ‖WuStirling.H (leftPoint T t)‖) (Icc u v) :=
    (hHc.norm.log (fun t ht => norm_ne_zero_iff.mpr (hH t (hsub ht)))).integrableOn_compact isCompact_Icc
  have hi := vertical_log_integrable _ (auxiliary_entire T)
    (1/2-PRZZAsymptotic.R/Real.log T) u v huv.le
  change IntegrableOn (fun t => Real.log ‖auxiliary T (leftPoint T t)‖) (Icc u v) at hi
  have hbudget := hb u hu v hv
  rw [integral_sub hi hiH] at hbudget
  obtain ⟨x,hx,hn,hret⟩ := exists_safe_left T (1/2-PRZZAsymptotic.R/Real.log T)
    u v ε w hT huv.le hε hw'
  refine ⟨x,hx,hn,?_⟩
  change (∫ t in Icc u v, Real.log ‖auxiliary T (point x t)‖) <
    (∫ t in Icc u v, Real.log ‖WuStirling.H (leftPoint T t)‖)+
      (v-u)*Real.log WitnessMomentBound.countingCap/2+ε
  change (∫ t in Icc u v, Real.log ‖auxiliary T (point x t)‖) <
    (∫ t in Icc u v, Real.log ‖auxiliary T (leftPoint T t)‖)+ε at hret
  linarith

#print axioms integral_eventually_lt_of_upper_bound
#print axioms vertical_ae_nonzero
#print axioms vertical_log_eventually_lt
#print axioms auxiliary_left_return
#print axioms exists_safe_left
#print axioms littlewood_fixed_right
#print axioms weighted_sum_mono
#print axioms safe_left_budget_eventually
end XiPrime8845.WuLeftReturn
