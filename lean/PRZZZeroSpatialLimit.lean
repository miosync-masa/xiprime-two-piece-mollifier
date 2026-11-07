import PRZZZeroGapExchange
import PRZZPartitionMass

/-! Two-sided spatial exhaustion of the actual zero Fourier integral.
The seed plateaus supply partition unity; sourceW supplies a common
integrable bound. This is a genuine limit, not a finite-height boundary
error estimate or an evaluation of the improper cosine Mellin transform. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex MeasureTheory Set Filter Topology Finset
namespace XiPrime8845.PRZZZeroSpatialLimit
open PRZZZeroGap PRZZZeroGapExchange PRZZPartitionMass PRZZAFEProgression
set_option maxHeartbeats 5000000

def cutoff (S : ℝ → ℝ) (L : ℕ) (x : ℝ) : ℂ :=
  (S (x/(2:ℝ)^L):ℂ)-(S ((2:ℝ)^L*x):ℂ)

theorem profile_data (S : ℝ → ℝ) (hS : Continuous S) (hm : Antitone S)
    (hlo : ∀ x, 0 ≤ S x) (hhi : ∀ x, S x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), S x = 1) (hright : ∀ x, 1 ≤ x → S x = 0) :
    Continuous (profile S) ∧ Function.support (profile S) ⊆ Icc (1/2:ℝ) 3 ∧
      ∀ x : ℝ, 0 < x → ‖profile S x‖ ≤ 1 := by
  refine ⟨?_,?_,?_⟩
  · unfold profile piece
    fun_prop
  · have hh := piece_support (fun x => (S x:ℂ)) 1 (by norm_num)
      (by intro x hx; simp [hleft x hx]) (by intro x hx; simp [hright x hx])
    intro x hx
    have he := hh hx
    norm_num only [mul_one,one_div] at he
    exact ⟨he.1,he.2.trans (by norm_num)⟩
  · intro x hx
    change ‖piece (fun x => (S x:ℂ)) 1 x‖ ≤ 1
    rw [piece_norm S hm 1 x (by norm_num) hx.le]
    linarith [hhi (x/(2*1)),hlo (x/1)]

theorem cutoff_bound (S : ℝ → ℝ) (hm : Antitone S)
    (hlo : ∀ x, 0 ≤ S x) (hhi : ∀ x, S x ≤ 1) (L : ℕ) (x : ℝ) (hx : 0 < x) :
    ‖cutoff S L x‖ ≤ 1 := by
  have hp : 1 ≤ (2:ℝ)^L := one_le_pow₀ (by norm_num)
  have ho : x/(2:ℝ)^L ≤ (2:ℝ)^L*x :=
    (div_le_self hx.le hp).trans (by nlinarith)
  have hs : 0 ≤ S (x/(2:ℝ)^L)-S ((2:ℝ)^L*x) := sub_nonneg.mpr (hm ho)
  rw [cutoff,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hs]
  linarith [hhi (x/(2:ℝ)^L),hlo ((2:ℝ)^L*x)]

/-- The exact finite set of dyadic pieces, including the lower boundary.
There is no bounded-overlap or partition identity premise. -/
theorem cutoff_sum (S : ℝ → ℝ) (L : ℕ) (x : ℝ) :
    (∑ k ∈ range (2*L), profile S (((2:ℝ)^k*((2:ℝ)^L)⁻¹)⁻¹*x)) = cutoff S L x := by
  simp_rw [profile_scaled]
  rw [piece_telescope]
  have hp : (2:ℝ)^L ≠ 0 := by positivity
  have he : (2:ℝ)^(2*L)*((2:ℝ)^L)⁻¹ = (2:ℝ)^L := by
    rw [show 2*L=L+L by omega,pow_add]
    field_simp
  rw [he]
  have hl : x/((2:ℝ)^L)⁻¹ = (2:ℝ)^L*x := by rw [div_inv_eq_mul,mul_comm]
  rw [hl]
  rfl

theorem cutoff_eventually (S : ℝ → ℝ)
    (hleft : ∀ x ≤ (1/2:ℝ), S x = 1) (hright : ∀ x, 1 ≤ x → S x = 0)
    (x : ℝ) (hx : 0 < x) : ∀ᶠ L : ℕ in atTop, cutoff S L x = 1 := by
  have hg : Tendsto (fun L : ℕ => (2:ℝ)^L) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  filter_upwards [hg.eventually (eventually_ge_atTop (2*x)),
    hg.eventually (eventually_ge_atTop (1/x))] with L h1 h2
  have hp : (0:ℝ) < 2^L := by positivity
  have hl : x/(2:ℝ)^L ≤ 1/2 := (div_le_iff₀ hp).mpr (by linarith)
  have hr : 1 ≤ (2:ℝ)^L*x := (div_le_iff₀ hx).mp h2
  simp only [cutoff,hleft _ hl,hright _ hr,Complex.ofReal_one,Complex.ofReal_zero,sub_zero]

theorem cutoff_rows (S : ℝ → ℝ) (L : ℕ) (Phi : ℝ → ℂ)
    (T u : ℝ) (sigma : ℂ) (delta x : ℝ) :
    (∑ k ∈ range (2*L), row (profile S) Phi ((2:ℝ)^k*((2:ℝ)^L)⁻¹) T u sigma delta x) =
      cutoff S L x*core Phi T u sigma delta x := by
  simp only [row,← Finset.sum_mul,cutoff_sum]

theorem cutoff_integrable (S : ℝ → ℝ) (hS : Continuous S) (hm : Antitone S)
    (hlo : ∀ x, 0 ≤ S x) (hhi : ∀ x, S x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), S x = 1) (hright : ∀ x, 1 ≤ x → S x = 0)
    (Phi : ℝ → ℂ) (hPhi : Continuous Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (L : ℕ) (T u : ℝ) (sigma : ℂ) (delta : ℝ)
    (hT : 0 < T) (hu : 0 < u) (hs : sigma ≠ 0) :
    Integrable (fun x : ℝ => cutoff S L x*core Phi T u sigma delta x) := by
  obtain ⟨hp,hsp,hcap⟩ := profile_data S hS hm hlo hhi hleft hright
  have he : (fun x : ℝ => cutoff S L x*core Phi T u sigma delta x) =
      (fun x => ∑ k ∈ range (2*L), row (profile S) Phi ((2:ℝ)^k*((2:ℝ)^L)⁻¹) T u sigma delta x) := by
    funext x
    exact (cutoff_rows S L Phi T u sigma delta x).symm
  rw [he]
  apply integrable_finsetSum
  intro k hk
  exact row_integrable (profile S) Phi hp hPhi hsp hsPhi _ T u sigma delta (by positivity) hT hu hs

/-- Remove both spatial boundaries after time integration, for every
nonzero signed gap. The original finite dyadic pieces are cutoff_rows.
The bound is valid at both ends of the spatial half-line. -/
theorem spatial_limit (S : ℝ → ℝ) (hS : Continuous S) (hm : Antitone S)
    (hlo : ∀ x, 0 ≤ S x) (hhi : ∀ x, S x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), S x = 1) (hright : ∀ x, 1 ≤ x → S x = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (T u : ℝ) (sigma : ℂ) (delta : ℝ)
    (hT : 0 < T) (hu : 0 < u) (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8) (hd : delta ≠ 0) :
    IntegrableOn (core Phi T u sigma delta) (Ioi (0:ℝ)) ∧
      Tendsto (fun L : ℕ => ∫ x in Ioi (0:ℝ), cutoff S L x*core Phi T u sigma delta x)
        atTop (𝓝 (∫ x in Ioi (0:ℝ), core Phi T u sigma delta x)) := by
  obtain ⟨B,hB,hb⟩ := core_envelope Phi hPhi hcPhi hsPhi sigma T u hs hn hT hu
  let g := fun x : ℝ => (B/|delta|^2)*envelope x
  have hg : IntegrableOn g (Ioi (0:ℝ)) := envelope_integrable.const_mul _
  have hmeas (L : ℕ) : AEStronglyMeasurable
      (fun x : ℝ => cutoff S L x*core Phi T u sigma delta x) (volume.restrict (Ioi (0:ℝ))) :=
    (cutoff_integrable S hS hm hlo hhi hleft hright Phi hPhi.continuous hsPhi L T u sigma delta
      hT hu hs).aestronglyMeasurable.restrict
  have hlim : ∀ᵐ x : ℝ ∂volume.restrict (Ioi (0:ℝ)),
      Tendsto (fun L : ℕ => cutoff S L x*core Phi T u sigma delta x) atTop
        (𝓝 (core Phi T u sigma delta x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [cutoff_eventually S hleft hright x hx] with L hL
    rw [hL,one_mul]
  have hbound (L : ℕ) : ∀ᵐ x : ℝ ∂volume.restrict (Ioi (0:ℝ)),
      ‖cutoff S L x*core Phi T u sigma delta x‖ ≤ g x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [norm_mul]
    have hh := (mul_le_mul_of_nonneg_right (cutoff_bound S hm hlo hhi L x hx)
      (norm_nonneg (core Phi T u sigma delta x))).trans_eq (one_mul _)
    exact (hh.trans (hb delta x hd hx)).trans_eq (by dsimp [g]; ring)
  refine ⟨?_,tendsto_integral_of_dominated_convergence g hmeas hg hbound hlim⟩
  apply hg.mono' (aestronglyMeasurable_of_tendsto_ae atTop hmeas hlim)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (hb delta x hd hx).trans_eq (by dsimp [g]; ring)

#print axioms profile_data
#print axioms cutoff_bound
#print axioms cutoff_sum
#print axioms cutoff_eventually
#print axioms cutoff_rows
#print axioms cutoff_integrable
#print axioms spatial_limit
end XiPrime8845.PRZZZeroSpatialLimit
