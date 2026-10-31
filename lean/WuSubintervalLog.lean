import WuIndependentWindows

/-! Jensen on independently shortened interior windows, with the original
height, shifts and mollifier fixed. Only the nonnegative density integral
is restricted; the logarithm itself is not assumed nonnegative. The unit
trimming correction is uniform in both chosen endpoints. -/
noncomputable section
open Filter Topology MeasureTheory Set
namespace XiPrime8845.WuSubintervalLog
open WuTrimmedLog WuUnsmoothing WitnessMomentBound
set_option maxHeartbeats 2000000

def subLogMean (T u v ρ : ℝ) : ℝ :=
  (∫ t in Icc u v, Real.log (density T t+ρ))/(2*(v-u))

/-- Tangent-line Jensen with an integral budget. No pointwise upper bound
on the density and no comparison between logarithmic integrals is used. -/
theorem jensen_of_integral (f : ℝ → ℝ) (u v ρ c : ℝ) (huv : u < v)
    (hf : ContinuousOn f (Icc u v)) (hn : ∀ t ∈ Icc u v, 0 ≤ f t)
    (hρ : 0 < ρ) (hc : 0 < c)
    (hm : (∫ t in Icc u v, f t) ≤ (v-u)*(c-ρ)) :
    (∫ t in Icc u v, Real.log (f t+ρ))/(2*(v-u)) ≤ Real.log c/2 := by
  have hi : IntegrableOn f (Icc u v) := hf.integrableOn_compact isCompact_Icc
  have hlog : IntegrableOn (fun t => Real.log (f t+ρ)) (Icc u v) :=
    ((hf.add continuousOn_const).log (fun t ht => ne_of_gt (by
      change 0 < f t+ρ
      linarith [hn t ht]))).integrableOn_compact isCompact_Icc
  have hci (a : ℝ) : IntegrableOn (fun _ : ℝ => a) (Icc u v) :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  have hid : IntegrableOn (fun t => (f t+ρ)/c) (Icc u v) := (hi.add (hci ρ)).div_const c
  have his : IntegrableOn (fun t => Real.log c+(f t+ρ)/c) (Icc u v) := (hci (Real.log c)).add hid
  have hconst (a : ℝ) : (∫ _ in Icc u v, a) = (v-u)*a := by
    simp only [setIntegral_const,Real.volume_real_Icc_of_le huv.le,smul_eq_mul]
  have hb : (∫ t in Icc u v, Real.log (f t+ρ)) ≤
      (v-u)*Real.log c+((∫ t in Icc u v, f t)+(v-u)*ρ)/c-(v-u) := by
    calc
      _ ≤ ∫ t in Icc u v, Real.log c+(f t+ρ)/c-1 := by
        apply setIntegral_mono_on hlog (his.sub (hci 1)) measurableSet_Icc
        intro t ht
        exact log_tangent _ c (by linarith [hn t ht]) hc
      _ = _ := by
        rw [integral_sub his (hci 1),integral_add (hci (Real.log c)) hid,
          integral_div,integral_add hi (hci ρ),hconst,hconst,hconst]
        ring
  have hh : ((∫ t in Icc u v, f t)+(v-u)*ρ)/c ≤ v-u :=
    (div_le_iff₀ hc).mpr (by nlinarith)
  apply (div_le_iff₀ (by linarith : 0 < 2*(v-u))).mpr
  nlinarith

theorem integral_density_subinterval (δ T u v : ℝ) (hd : δ < 1/2) (hT : 0 < T)
    (hu : (1+δ)*T ≤ u) (hv : v ≤ (2-δ)*T)
    (hf : ContinuousOn (density T) (interval δ T)) :
    (∫ t in Icc u v, density T t) ≤ length δ T*trimmedMean δ T := by
  rw [← integral_density δ T hd hT]
  exact setIntegral_mono_set (hf.integrableOn_compact isCompact_Icc)
    (Eventually.of_forall (fun t => sq_nonneg _))
    (Eventually.of_forall (fun t ht => ⟨hu.trans ht.1,ht.2.trans hv⟩))

/-- Exact finite-T length-ratio correction for any retained subinterval. -/
theorem subLogMean_le (δ T u v ρ c : ℝ) (hd : δ < 1/2) (hT : 0 < T)
    (hu : (1+δ)*T ≤ u) (hv : v ≤ (2-δ)*T) (huv : u < v)
    (hρ : 0 < ρ) (hc : 0 < c) (hf : ContinuousOn (density T) (interval δ T))
    (hm : length δ T/(v-u)*trimmedMean δ T+ρ ≤ c) :
    subLogMean T u v ρ ≤ Real.log c/2 := by
  apply jensen_of_integral (density T) u v ρ c huv
    (hf.mono (fun t ht => ⟨hu.trans ht.1,ht.2.trans hv⟩))
    (fun _ _ => sq_nonneg _) hρ hc
  apply (integral_density_subinterval δ T u v hd hT hu hv hf).trans
  have hlen : 0 < v-u := sub_pos.mpr huv
  have hh := mul_le_mul_of_nonneg_right hm hlen.le
  have he : (length δ T/(v-u)*trimmedMean δ T+ρ)*(v-u) =
      length δ T*trimmedMean δ T+ρ*(v-u) := by field_simp
  rw [he] at hh
  nlinarith

/-- The numerical slack absorbs the length loss, uniformly over ALL inward
unit trims. Width is fixed before T; rho0 does not depend on that width. -/
theorem subLogMean_eventually_le :
    ∃ ρ0 : ℝ, 0 < ρ0 ∧ ∀ δ : ℝ, 0 < δ → δ < 1/2 →
      ∀ᶠ T : ℝ in atTop, ∀ u ∈ Icc ((1+δ)*T) ((1+δ)*T+1),
        ∀ v ∈ Icc ((2-δ)*T-1) ((2-δ)*T),
        u < v ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ0 → subLogMean T u v ρ ≤ Real.log countingCap/2 := by
  let gap := countingCap-NumericalGate.actual.re
  have hgap : 0 < gap := by
    have hh := LogarithmicBudget.actual_le_cap.trans_lt (show LogarithmicBudget.certifiedCap < countingCap by
      norm_num [LogarithmicBudget.certifiedCap,countingCap])
    dsimp [gap]; linarith
  have hcap : 0 < countingCap := by norm_num [countingCap]
  refine ⟨gap/4,by positivity,?_⟩
  intro δ hδ hd
  have hw : 0 < 1-2*δ := by linarith
  have hmid : NumericalGate.actual.re < countingCap-gap/2 := by dsimp [gap]; linarith
  filter_upwards [density_continuous,eventually_gt_atTop (0:ℝ),
    eventually_gt_atTop ((8*countingCap/gap+3)/(1-2*δ)),
    (trimmedMean_tendsto δ hδ hd).eventually (gt_mem_nhds hmid)] with T hf hT hlarge hm
  have hlarge' : 8*countingCap/gap+3 < length δ T := by
    simpa only [length,mul_comm T] using (div_lt_iff₀ hw).mp hlarge
  have hlen : 2 < length δ T := by
    have : 0 < 8*countingCap/gap := by positivity
    linarith
  have hbudget : 8*countingCap < length δ T*gap := by
    have hh : 8*countingCap/gap < length δ T := by linarith
    exact (div_lt_iff₀ hgap).mp hh
  have hf' : ContinuousOn (density T) (interval δ T) := hf.mono (by
    intro t ht
    dsimp [interval] at ht
    constructor <;> nlinarith [ht.1,ht.2])
  intro u hu v hv
  have hs : length δ T-2 ≤ v-u ∧ v-u ≤ length δ T := by
    dsimp [length]; constructor <;> linarith [hu.1,hu.2,hv.1,hv.2]
  have huv : u < v := by linarith [hs.1]
  refine ⟨huv,?_⟩
  intro ρ hρ hr
  apply subLogMean_le δ T u v ρ countingCap hd hT hu.1 hv.2 huv hρ hcap hf'
  have hmul := mul_le_mul_of_nonneg_left hm.le (length_pos δ T hd hT).le
  have hrmul := mul_le_mul hr hs.2 (by linarith : 0 ≤ v-u) (by positivity : 0 ≤ gap/4)
  have hc := mul_le_mul_of_nonneg_left hs.1 hcap.le
  have he : length δ T*trimmedMean δ T ≤ (countingCap-ρ)*(v-u) := by nlinarith
  rw [div_mul_eq_mul_div]
  exact (by have hh := (div_le_iff₀ (sub_pos.mpr huv)).mpr he; linarith)

/-- Freeze any candidate function at this T, then select its safe edges.
The same moment cap holds for every such choice, without a diagonal
countability premise or a new localized PRZZ input. -/
theorem safe_window_log_input :
    ∃ ρ0 : ℝ, 0 < ρ0 ∧ ∀ δ : ℝ, 0 < δ → δ < 1/2 →
      ∀ᶠ T : ℝ in atTop, ∀ f : ℂ → ℂ, (WuSafeEndpoints.badHeights f).Countable →
        ∃ u ∈ Ioo ((1+δ)*T) ((1+δ)*T+1),
          ∃ v ∈ Ioo ((2-δ)*T-1) ((2-δ)*T),
          u < v ∧ u ∉ WuSafeEndpoints.badHeights f ∧ v ∉ WuSafeEndpoints.badHeights f ∧
          ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ0 → subLogMean T u v ρ ≤ Real.log countingCap/2 := by
  obtain ⟨ρ0,hρ0,h⟩ := subLogMean_eventually_le
  refine ⟨ρ0,hρ0,?_⟩
  intro δ hδ hd
  have hw : 0 < 1-2*δ := by linarith
  filter_upwards [h δ hδ hd,eventually_gt_atTop (3/(1-2*δ))] with T hT hlarge
  intro f hf
  have hlen : 2 < (2-δ)*T-(1+δ)*T := by
    have hh := (div_lt_iff₀ hw).mp hlarge
    nlinarith
  obtain ⟨u,hu,v,hv,huv,hsu,hsv⟩ :=
    WuIndependentWindows.exists_inward_heights f hf _ _ hlen
  exact ⟨u,hu,v,hv,huv,hsu,hsv,(hT u ⟨hu.1.le,hu.2.le⟩ v ⟨hv.1.le,hv.2.le⟩).2⟩

#print axioms jensen_of_integral
#print axioms integral_density_subinterval
#print axioms subLogMean_le
#print axioms subLogMean_eventually_le
#print axioms safe_window_log_input
end XiPrime8845.WuSubintervalLog
