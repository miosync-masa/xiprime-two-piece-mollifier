import PRZZAsymptotic

/-! Uniform scaling of the two zeta poles in the literal gcd main term.
This does not evaluate the remaining arithmetic double sum. -/
noncomputable section
open Filter Topology
namespace XiPrime8845.ZetaPoleScaling

def annulus (bound gap : ℝ) : Set ℂ := {z | ‖z‖ ≤ bound ∧ gap ≤ ‖z‖}

/-- The residue theorem gives a simultaneous limit, not merely a limit at
each fixed shift. The gap is needed when dividing the residue by z. -/
theorem scaled_zeta_uniform (bound gap : ℝ) (hg : 0 < gap) :
    TendstoUniformlyOn
      (fun T z => riemannZeta (1 + z / (Real.log T : ℂ)) / (Real.log T : ℂ))
      (fun z => 1 / z) atTop (annulus bound gap) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  obtain ⟨delta, hd, hres⟩ := Metric.tendsto_nhdsWithin_nhds.mp
    riemannZeta_residue_one (eps * gap) (mul_pos heps hg)
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (bound / delta))] with T hT hlog
  intro z hz
  have hL : 0 < Real.log T := Real.log_pos hT
  have hLc : (Real.log T : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hz0 : z ≠ 0 := by
    intro h; have := hz.2; simp [h] at this; linarith
  have hnear : dist (1 + z / (Real.log T : ℂ)) 1 < delta := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hL]
    apply (div_lt_iff₀ hL).mpr
    exact hz.1.trans_lt (by nlinarith [(div_lt_iff₀ hd).mp hlog])
  have hne : 1 + z / (Real.log T : ℂ) ≠ 1 := by
    intro h
    have h' : z / (Real.log T : ℂ) = 0 := by linear_combination h
    exact hz0 ((div_eq_zero_iff).mp h' |>.resolve_right hLc)
  have hr := hres (by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hne) hnear
  have he : riemannZeta (1 + z / (Real.log T : ℂ)) / (Real.log T : ℂ) - 1 / z =
      (((1 + z / (Real.log T : ℂ)) - 1) *
        riemannZeta (1 + z / (Real.log T : ℂ)) - 1) / z := by field_simp; ring
  rw [dist_comm, dist_eq_norm, he, norm_div]
  apply (div_lt_iff₀ (norm_pos_iff.mpr hz0)).mpr
  have hr' : ‖((1 + z / (Real.log T : ℂ)) - 1) *
      riemannZeta (1 + z / (Real.log T : ℂ)) - 1‖ < eps * gap := by
    simpa only [dist_eq_norm] using hr
  exact hr'.trans_le (mul_le_mul_of_nonneg_left hz.2 heps.le)

theorem scaled_zeta_minus_uniform (bound gap : ℝ) (hg : 0 < gap) :
    TendstoUniformlyOn
      (fun T z => riemannZeta (1 - z / (Real.log T : ℂ)) / (Real.log T : ℂ))
      (fun z => -(1 / z)) atTop (annulus bound gap) := by
  have h := scaled_zeta_uniform bound gap hg
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h eps heps] with T hT
  intro z hz
  have hn : -z ∈ annulus bound gap := by simpa only [annulus, Set.mem_ofPred_eq, norm_neg] using hz
  simpa only [neg_div, div_neg, sub_eq_add_neg] using hT (-z) hn

open PRZZAsymptotic

theorem direct_pole_on_bidisc :
    TendstoUniformlyOn
      (fun (T : ℝ) (p : ℂ × ℂ) => riemannZeta (1 + (p.1+p.2)/(Real.log T : ℂ)) /
        (Real.log T : ℂ)) (fun p => 1/(p.1+p.2)) atTop witnessBidisc := by
  have h := scaled_zeta_uniform (5*R/2) (3*R/2) (by have := radius_pos; positivity)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h eps heps] with T hT
  intro p hp
  have hb := witnessBidisc_subset hp
  apply hT (p.1+p.2)
  exact ⟨(norm_add_le _ _).trans (by linarith [hb.1, hb.2.1]), hb.2.2⟩

theorem dual_pole_on_bidisc :
    TendstoUniformlyOn
      (fun (T : ℝ) (p : ℂ × ℂ) => riemannZeta (1 - (p.1+p.2)/(Real.log T : ℂ)) /
        (Real.log T : ℂ)) (fun p => -(1/(p.1+p.2))) atTop witnessBidisc := by
  have h := scaled_zeta_minus_uniform (5*R/2) (3*R/2) (by have := radius_pos; positivity)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h eps heps] with T hT
  intro p hp
  have hb := witnessBidisc_subset hp
  apply hT (p.1+p.2)
  exact ⟨(norm_add_le _ _).trans (by linarith [hb.1, hb.2.1]), hb.2.2⟩

#print axioms scaled_zeta_uniform
#print axioms scaled_zeta_minus_uniform
#print axioms direct_pole_on_bidisc
#print axioms dual_pole_on_bidisc
end XiPrime8845.ZetaPoleScaling
