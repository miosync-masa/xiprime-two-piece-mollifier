import PRZZLocalization
import PRZZAsymptotic

/-! The audited localized estimate, if supplied, gives the actual uniform
normalized residual on the same witness bidisc. No localized estimate or gcd
main-term limit is assumed silently. No height in the coefficients is changed. -/
noncomputable section
open Filter Topology
namespace XiPrime8845.PRZZLocalizedError
open PRZZ PRZZLocalization PRZZAsymptotic

theorem normalized_difference_bound (hlocal : LocalizedEstimate)
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (Phi : ℝ → ℝ) (hPhi : SmoothWeightOn a b Phi)
    (bound gap : ℝ) (hb : 0 < bound) (hg : 0 < gap) :
    ∃ C T0 : ℝ, 0 < C ∧ 2 ≤ T0 ∧ ∀ T, T0 ≤ T →
      ∀ p ∈ shiftSet bound gap,
        ‖normalizedMoment Phi T p-normalizedGcd Phi T p‖ ≤ C*errorEnvelope T := by
  have ht : 0 < PRZZAsymptotic.theta := by norm_num [PRZZAsymptotic.theta]
  obtain ⟨C,T0,hC,hT0,h⟩ := hlocal a b ha hab witness witness PRZZAsymptotic.theta ht
    (by norm_num [PRZZAsymptotic.theta]) (witness_subpower PRZZAsymptotic.theta ht)
    (witness_subpower PRZZAsymptotic.theta ht)
    Phi hPhi bound gap (7/16000000) hb hg (by norm_num)
  refine ⟨C,T0,hC,hT0,?_⟩
  intro T hT p hp
  have hpos : 0 < T := lt_of_lt_of_le (by norm_num) (hT0.trans hT)
  have he := div_le_div_of_nonneg_right
    (h T hT p.1 p.2 hp.1 hp.2.1 hp.2.2) hpos.le
  simpa only [normalizedMoment,normalizedGcd,← sub_div,norm_div,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hpos,errorEnvelope,
    mul_div_assoc,mul_assoc] using he

theorem normalized_difference_uniform (hlocal : LocalizedEstimate)
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (Phi : ℝ → ℝ) (hPhi : SmoothWeightOn a b Phi)
    (bound gap : ℝ) (hb : 0 < bound) (hg : 0 < gap) :
    TendstoUniformlyOn (fun T p => normalizedMoment Phi T p-normalizedGcd Phi T p)
      (fun _ => 0) atTop (shiftSet bound gap) := by
  obtain ⟨C,T0,hC,hT0,h⟩ := normalized_difference_bound hlocal a b ha hab Phi hPhi bound gap hb hg
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  have hlim : Tendsto (fun T => C*errorEnvelope T) atTop (nhds 0) := by
    simpa using errorEnvelope_tendsto.const_mul C
  filter_upwards [eventually_ge_atTop T0,hlim.eventually (gt_mem_nhds heps)] with T hT he
  intro p hp
  simpa only [dist_zero_left] using (h T hT p hp).trans_lt he

theorem normalized_difference_on_bidisc (hlocal : LocalizedEstimate)
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (Phi : ℝ → ℝ) (hPhi : SmoothWeightOn a b Phi) :
    TendstoUniformlyOn (fun T p => normalizedMoment Phi T p-normalizedGcd Phi T p)
      (fun _ => 0) atTop witnessBidisc :=
  (normalized_difference_uniform hlocal a b ha hab Phi hPhi (5*R/4) (3*R/2)
    (by have := radius_pos; positivity) (by have := radius_pos; positivity)).mono witnessBidisc_subset

theorem moment_uniform_limit_of_gcd_limit (hlocal : LocalizedEstimate)
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (Phi : ℝ → ℝ) (hPhi : SmoothWeightOn a b Phi) (K : ℂ × ℂ → ℂ)
    (hmain : TendstoUniformlyOn (normalizedGcd Phi) K atTop witnessBidisc) :
    TendstoUniformlyOn (normalizedMoment Phi) K atTop witnessBidisc := by
  simpa only [Pi.add_def,sub_add_cancel,zero_add] using
    (normalized_difference_on_bidisc hlocal a b ha hab Phi hPhi).add hmain

#print axioms normalized_difference_bound
#print axioms normalized_difference_uniform
#print axioms normalized_difference_on_bidisc
#print axioms moment_uniform_limit_of_gcd_limit
end XiPrime8845.PRZZLocalizedError
