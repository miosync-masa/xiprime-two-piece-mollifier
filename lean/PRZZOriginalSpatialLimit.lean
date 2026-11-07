import PRZZPartitionDiscrepancy

/-! Removal of the original one-sided spatial partition after time
integration. Its limit retains the low-scale seed. The difference from
the two-sided exhaustion is identified under the actual core integral. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex MeasureTheory Set Filter Topology Finset
namespace XiPrime8845.PRZZOriginalSpatialLimit
open PRZZPartitionDiscrepancy PRZZPartitionMass PRZZZeroSpatialLimit
open PRZZZeroGap PRZZZeroGapExchange
set_option maxHeartbeats 4000000

theorem original_integrable (S : ℝ → ℝ) (hS : Continuous S) (hm : Antitone S)
    (hlo : ∀ x, 0 ≤ S x) (hhi : ∀ x, S x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), S x = 1) (hright : ∀ x, 1 ≤ x → S x = 0)
    (Phi : ℝ → ℂ) (hPhi : Continuous Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (K : ℕ) (T u : ℝ) (sigma : ℂ) (delta : ℝ)
    (hT : 0 < T) (hu : 0 < u) (hs : sigma ≠ 0) :
    Integrable (fun x : ℝ => original S K x*core Phi T u sigma delta x) := by
  obtain ⟨hp,hsp,hcap⟩ := profile_data S hS hm hlo hhi hleft hright
  have he : (fun x : ℝ => original S K x*core Phi T u sigma delta x) =
      (fun x => ∑ k ∈ range K, row (profile S) Phi ((2:ℝ)^k) T u sigma delta x) := by
    funext x
    simp only [original,row,Finset.sum_mul]
  rw [he]
  exact integrable_finsetSum _ (fun k hk =>
    row_integrable _ _ hp hPhi hsp hsPhi _ T u sigma delta (by positivity) hT hu hs)

theorem spatial_limit (S : ℝ → ℝ) (hS : Continuous S) (hm : Antitone S)
    (hlo : ∀ x, 0 ≤ S x) (hhi : ∀ x, S x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), S x = 1) (hright : ∀ x, 1 ≤ x → S x = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (T u : ℝ) (sigma : ℂ) (delta : ℝ)
    (hT : 0 < T) (hu : 0 < u) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8) (hd : delta ≠ 0) :
    Tendsto (fun L : ℕ => ∫ x in Ioi (0:ℝ), original S (L+2) x*core Phi T u sigma delta x)
      atTop (𝓝 (∫ x in Ioi (0:ℝ), (1-(S x:ℂ))*core Phi T u sigma delta x)) := by
  obtain ⟨B,hB,hb⟩ := core_envelope Phi hPhi hcPhi hsPhi sigma T u hs hn hT hu
  let g := fun x : ℝ => (B/|delta|^2)*envelope x
  have hg : IntegrableOn g (Ioi (0:ℝ)) := envelope_integrable.const_mul _
  have hmeas (L : ℕ) : AEStronglyMeasurable
      (fun x : ℝ => original S (L+2) x*core Phi T u sigma delta x)
        (volume.restrict (Ioi (0:ℝ))) :=
    (original_integrable S hS hm hlo hhi hleft hright Phi hPhi.continuous hsPhi
      _ T u sigma delta hT hu hs).aestronglyMeasurable.restrict
  apply tendsto_integral_of_dominated_convergence g hmeas hg
  · intro L
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have ho : ‖original S (L+2) x‖ ≤ 1 := by
      apply (norm_sum_le _ _).trans
      simp_rw [profile_scaled]
      simpa only [mul_one] using piece_mass S hm hlo hhi 1 x (L+2) (by norm_num) hx.le
    rw [norm_mul]
    exact ((mul_le_mul_of_nonneg_right ho (norm_nonneg _)).trans_eq (one_mul _)).trans
      ((hb delta x hd hx).trans_eq (by dsimp [g]; ring))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [original_eventually S hleft x] with L hL
    rw [hL]

/-- The missing low spatial range survives integration for each actual
signed nonzero gap. Its integral is not silently declared negligible. -/
theorem discrepancy_limit (S : ℝ → ℝ) (hS : Continuous S) (hm : Antitone S)
    (hlo : ∀ x, 0 ≤ S x) (hhi : ∀ x, S x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), S x = 1) (hright : ∀ x, 1 ≤ x → S x = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (T u : ℝ) (sigma : ℂ) (delta : ℝ)
    (hT : 0 < T) (hu : 0 < u) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8) (hd : delta ≠ 0) :
    Tendsto (fun L : ℕ => ∫ x in Ioi (0:ℝ),
      (cutoff S L x-original S (L+2) x)*core Phi T u sigma delta x)
      atTop (𝓝 (∫ x in Ioi (0:ℝ), (S x:ℂ)*core Phi T u sigma delta x)) := by
  obtain ⟨B,hB,hb⟩ := core_envelope Phi hPhi hcPhi hsPhi sigma T u hs hn hT hu
  let g := fun x : ℝ => (2*B/|delta|^2)*envelope x
  have hg : IntegrableOn g (Ioi (0:ℝ)) := envelope_integrable.const_mul _
  have hmeas (L : ℕ) : AEStronglyMeasurable
      (fun x : ℝ => (cutoff S L x-original S (L+2) x)*core Phi T u sigma delta x)
        (volume.restrict (Ioi (0:ℝ))) := by
    have hi : Integrable (fun x : ℝ =>
        (cutoff S L x-original S (L+2) x)*core Phi T u sigma delta x) := by
      convert (cutoff_integrable S hS hm hlo hhi hleft hright Phi hPhi.continuous hsPhi
        L T u sigma delta hT hu hs).sub
        (original_integrable S hS hm hlo hhi hleft hright Phi hPhi.continuous hsPhi
          (L+2) T u sigma delta hT hu hs) using 1
      funext x
      dsimp only [Pi.sub_apply]
      ring
    exact hi.aestronglyMeasurable.restrict
  apply tendsto_integral_of_dominated_convergence g hmeas hg
  · intro L
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have ho : ‖original S (L+2) x‖ ≤ 1 := by
      apply (norm_sum_le _ _).trans
      simp_rw [profile_scaled]
      simpa only [mul_one] using piece_mass S hm hlo hhi 1 x (L+2) (by norm_num) hx.le
    have hh : ‖cutoff S L x-original S (L+2) x‖ ≤ 2 :=
      (norm_sub_le _ _).trans (by linarith [cutoff_bound S hm hlo hhi L x hx])
    rw [norm_mul]
    exact (mul_le_mul hh (hb delta x hd hx) (norm_nonneg _) (by norm_num)).trans_eq
      (by dsimp [g]; ring)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [difference_eventually S hleft hright x hx] with L hL
    rw [hL]

#print axioms original_integrable
#print axioms spatial_limit
#print axioms discrepancy_limit
end XiPrime8845.PRZZOriginalSpatialLimit
