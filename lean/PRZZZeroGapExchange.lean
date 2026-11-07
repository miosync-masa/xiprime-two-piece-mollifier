import PRZZZeroGap

/-! Absolute removal of the signed gap cutoff for the actual zero mode
on each original compact spatial piece. Time integration is performed
first; the improper cosine Mellin transform is not an assumed formula. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex MeasureTheory Set Filter Topology
namespace XiPrime8845.PRZZZeroGapExchange
open PRZZZeroGap PRZZCentralFubini
set_option maxHeartbeats 5000000

def row (F Phi : ℝ → ℂ) (M T u : ℝ) (sigma : ℂ) (delta x : ℝ) : ℂ :=
  F (M⁻¹*x)*core Phi T u sigma delta x

def pair (F Phi : ℝ → ℂ) (M T u : ℝ) (sigma : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  row F Phi M T u sigma ((n+1:ℕ):ℝ) x+
    row F Phi M T u sigma (-((n+1:ℕ):ℝ)) x

theorem row_integrable (F Phi : ℝ → ℂ) (hF : Continuous F) (hPhi : Continuous Phi)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (M T u : ℝ) (sigma : ℂ) (delta : ℝ)
    (hM : 0 < M) (hT : 0 < T) (hu : 0 < u) (hs : sigma ≠ 0) :
    Integrable (row F Phi M T u sigma delta) := by
  have hi := kernel_integrable F Phi hF hPhi M u delta T 0 (sigma+1) sigma
    hM hu hT hs hsF hsPhi
  change Integrable (fun x => F (M⁻¹*x)*core Phi T u sigma delta x)
  simpa only [Function.uncurry,kernel_time] using hi.integral_prod_left

theorem pair_integrable (F Phi : ℝ → ℂ) (hF : Continuous F) (hPhi : Continuous Phi)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (M T u : ℝ) (sigma : ℂ) (n : ℕ)
    (hM : 0 < M) (hT : 0 < T) (hu : 0 < u) (hs : sigma ≠ 0) :
    Integrable (pair F Phi M T u sigma n) :=
  (row_integrable F Phi hF hPhi hsF hsPhi M T u sigma _ hM hT hu hs).fun_add
    (row_integrable F Phi hF hPhi hsF hsPhi M T u sigma _ hM hT hu hs)

/-- Cutoff values of norm at most one cost no new spatial multiplicity.
The cap is supplied by sourceW and the fixed smooth time cutoff. -/
theorem paired_domination (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hcPhi : HasCompactSupport Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (sigma : ℂ) (T u : ℝ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (hT : 0 < T) (hu : 0 < u) :
    ∃ B : ℝ, 0 < B ∧ ∀ (F : ℝ → ℂ) (M : ℝ),
      (∀ y : ℝ, 0 < y → ‖F y‖ ≤ 1) → 0 < M → ∀ (n : ℕ) (x : ℝ), 0 < x →
      ‖pair F Phi M T u sigma n x‖ ≤ 2*B*envelope x/(((n+1:ℕ):ℝ)^2) := by
  obtain ⟨B,hB,hb⟩ := core_envelope Phi hPhi hcPhi hsPhi sigma T u hs hn hT hu
  refine ⟨B,hB,?_⟩
  intro F M hF hM n x hx
  have hr (delta : ℝ) : ‖row F Phi M T u sigma delta x‖ ≤ ‖core Phi T u sigma delta x‖ := by
    rw [row,norm_mul]
    exact (mul_le_mul_of_nonneg_right (hF (M⁻¹*x) (by positivity)) (norm_nonneg _)).trans_eq (one_mul _)
  have hp := hb ((n+1:ℕ):ℝ) x (by positivity) hx
  have hm := hb (-((n+1:ℕ):ℝ)) x (neg_ne_zero.mpr (by positivity)) hx
  simp only [abs_neg,abs_of_pos (show (0:ℝ) < (n+1:ℕ) by positivity)] at hp hm
  exact ((norm_add_le _ _).trans (add_le_add ((hr _).trans hp) ((hr _).trans hm))).trans_eq (by ring)

/-- Absolute-integral summability is established before any infinite
gap/spatial interchange. No gap derivative bound or Fubini premise. -/
theorem absolute_exchange (F Phi : ℝ → ℂ) (hF : Continuous F)
    (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hcap : ∀ y : ℝ, 0 < y → ‖F y‖ ≤ 1)
    (sigma : ℂ) (M T u : ℝ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (hM : 0 < M) (hT : 0 < T) (hu : 0 < u) :
    (∀ n, IntegrableOn (pair F Phi M T u sigma n) (Ioi (0:ℝ))) ∧
      Summable (fun n : ℕ => ∫ x in Ioi (0:ℝ), ‖pair F Phi M T u sigma n x‖) := by
  have hi (n : ℕ) := (pair_integrable F Phi hF hPhi.continuous hsF hsPhi
    M T u sigma n hM hT hu hs).integrableOn (s := Ioi (0:ℝ))
  refine ⟨hi,?_⟩
  obtain ⟨B,hB,hb⟩ := paired_domination Phi hPhi hcPhi hsPhi sigma T u hs hn hT hu
  let J := ∫ x in Ioi (0:ℝ), envelope x
  have hJ : 0 ≤ J := integral_nonneg (fun x => envelope_nonneg x)
  have hbound (n : ℕ) : (∫ x in Ioi (0:ℝ), ‖pair F Phi M T u sigma n x‖) ≤
      (2*B*J)*(1/(((n+1:ℕ):ℝ)^2)) := by
    have hg : IntegrableOn (fun x : ℝ => 2*B*envelope x/(((n+1:ℕ):ℝ)^2)) (Ioi (0:ℝ)) := by
      have he : (fun x : ℝ => 2*B*envelope x/(((n+1:ℕ):ℝ)^2)) =
          (fun x => (2*B/(((n+1:ℕ):ℝ)^2))*envelope x) := by funext x; ring
      rw [he]
      exact envelope_integrable.const_mul _
    have hh := integral_mono_ae (hi n).norm hg (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact hb F M hcap hM n x hx)
    rw [integral_div,integral_const_mul] at hh
    exact hh.trans_eq (by dsimp [J]; ring)
  have hp : Summable (fun n : ℕ => 1/(((n+1:ℕ):ℝ)^2)) :=
    (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  exact (hp.mul_left (2*B*J)).of_nonneg_of_le
    (fun n => integral_nonneg (fun x => norm_nonneg _)) hbound

theorem gap_spatial_exchange (F Phi : ℝ → ℂ) (hF : Continuous F)
    (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hcap : ∀ y : ℝ, 0 < y → ‖F y‖ ≤ 1)
    (sigma : ℂ) (M T u : ℝ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (hM : 0 < M) (hT : 0 < T) (hu : 0 < u) :
    (∑' n : ℕ, ∫ x in Ioi (0:ℝ), pair F Phi M T u sigma n x) =
      ∫ x in Ioi (0:ℝ), ∑' n : ℕ, pair F Phi M T u sigma n x := by
  obtain ⟨hi,ha⟩ := absolute_exchange F Phi hF hPhi hcPhi hsF hsPhi hcap sigma M T u
    hs hn hM hT hu
  exact integral_tsum_of_summable_integral_norm hi ha

theorem finite_gap_limit (F Phi : ℝ → ℂ) (hF : Continuous F)
    (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (hcap : ∀ y : ℝ, 0 < y → ‖F y‖ ≤ 1)
    (sigma : ℂ) (M T u : ℝ) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8)
    (hM : 0 < M) (hT : 0 < T) (hu : 0 < u) :
    Tendsto (fun L : ℕ => ∑ n ∈ Finset.range L,
      ∫ x in Ioi (0:ℝ), pair F Phi M T u sigma n x) atTop
      (𝓝 (∫ x in Ioi (0:ℝ), ∑' n : ℕ, pair F Phi M T u sigma n x)) := by
  obtain ⟨hi,ha⟩ := absolute_exchange F Phi hF hPhi hcPhi hsF hsPhi hcap sigma M T u
    hs hn hM hT hu
  exact (hasSum_integral_of_summable_integral_norm hi ha).tendsto_sum_nat

#print axioms row_integrable
#print axioms pair_integrable
#print axioms paired_domination
#print axioms absolute_exchange
#print axioms gap_spatial_exchange
#print axioms finite_gap_limit
end XiPrime8845.PRZZZeroGapExchange
