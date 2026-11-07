import PRZZZeroSpatialLimit

/-! Simultaneous signed-gap and two-sided dyadic-M exhaustion of the
actual zero Fourier kernels. This closes a dominated limit, not the
finite-height error rate or the subsequent cosine Mellin evaluation. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex MeasureTheory Set Filter Topology Finset
namespace XiPrime8845.PRZZZeroCutoffLimit
open PRZZZeroGap PRZZZeroGapExchange PRZZZeroSpatialLimit PRZZPartitionMass
set_option maxHeartbeats 5000000

def corePair (Phi : ℝ → ℂ) (T u : ℝ) (sigma : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  core Phi T u sigma ((n+1:ℕ):ℝ) x+core Phi T u sigma (-((n+1:ℕ):ℝ)) x

theorem core_pair_bound (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hcPhi : HasCompactSupport Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (T u : ℝ) (sigma : ℂ) (hT : 0 < T) (hu : 0 < u)
    (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8) :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      ‖corePair Phi T u sigma n x‖ ≤ (2*B*envelope x)*(1/(((n+1:ℕ):ℝ)^2)) := by
  obtain ⟨B,hB,hb⟩ := paired_domination Phi hPhi hcPhi hsPhi sigma T u hs hn hT hu
  refine ⟨B,hB,?_⟩
  intro n x hx
  simpa only [PRZZZeroGapExchange.pair,row,one_mul,corePair,mul_one_div] using
    hb (fun _ => (1:ℂ)) 1 (by intro y hy; norm_num) (by norm_num) n x hx

theorem rectangle_integral (S : ℝ → ℝ) (hS : Continuous S) (hm : Antitone S)
    (hlo : ∀ x, 0 ≤ S x) (hhi : ∀ x, S x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), S x = 1) (hright : ∀ x, 1 ≤ x → S x = 0)
    (Phi : ℝ → ℂ) (hPhi : Continuous Phi) (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (L : ℕ) (T u : ℝ) (sigma : ℂ) (hT : 0 < T) (hu : 0 < u) (hs : sigma ≠ 0) :
    (∑ k ∈ range (2*L), ∑ n ∈ range L,
      ∫ x in Ioi (0:ℝ), PRZZZeroGapExchange.pair (profile S) Phi
        ((2:ℝ)^k*((2:ℝ)^L)⁻¹) T u sigma n x) =
      ∫ x in Ioi (0:ℝ), cutoff S L x*(∑ n ∈ range L, corePair Phi T u sigma n x) := by
  obtain ⟨hp,hsp,hcap⟩ := profile_data S hS hm hlo hhi hleft hright
  have hi (k n : ℕ) : IntegrableOn (PRZZZeroGapExchange.pair (profile S) Phi
      ((2:ℝ)^k*((2:ℝ)^L)⁻¹) T u sigma n) (Ioi (0:ℝ)) :=
    (pair_integrable (profile S) Phi hp hPhi hsp hsPhi _ T u sigma n (by positivity) hT hu hs).integrableOn
  have he (k : ℕ) : (∑ n ∈ range L,
      ∫ x in Ioi (0:ℝ), PRZZZeroGapExchange.pair (profile S) Phi
        ((2:ℝ)^k*((2:ℝ)^L)⁻¹) T u sigma n x) =
      ∫ x in Ioi (0:ℝ), ∑ n ∈ range L, PRZZZeroGapExchange.pair (profile S) Phi
        ((2:ℝ)^k*((2:ℝ)^L)⁻¹) T u sigma n x :=
    (integral_finsetSum _ (fun n hn => hi k n)).symm
  simp_rw [he]
  rw [← integral_finsetSum _ (fun k hk => integrable_finsetSum _ (fun n hn => hi k n))]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  rw [Finset.sum_comm]
  simp only [PRZZZeroGapExchange.pair,Finset.sum_add_distrib,cutoff_rows,
    corePair,mul_add,Finset.mul_sum]

theorem joint_limit (S : ℝ → ℝ) (hS : Continuous S) (hm : Antitone S)
    (hlo : ∀ x, 0 ≤ S x) (hhi : ∀ x, S x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), S x = 1) (hright : ∀ x, 1 ≤ x → S x = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (T u : ℝ) (sigma : ℂ) (hT : 0 < T) (hu : 0 < u)
    (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8) :
    Tendsto (fun L : ℕ => ∫ x in Ioi (0:ℝ), cutoff S L x*
      (∑ n ∈ range L, corePair Phi T u sigma n x)) atTop
      (𝓝 (∫ x in Ioi (0:ℝ), ∑' n : ℕ, corePair Phi T u sigma n x)) := by
  obtain ⟨B,hB,hb⟩ := core_pair_bound Phi hPhi hcPhi hsPhi T u sigma hT hu hs hn
  let p := fun n : ℕ => 1/(((n+1:ℕ):ℝ)^2)
  have hp : Summable p := (summable_nat_add_iff 1).mpr
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  let Z := ∑' n : ℕ, p n
  have hZ : 0 ≤ Z := tsum_nonneg (fun n => by dsimp [p]; positivity)
  let g := fun x : ℝ => (2*B*Z)*envelope x
  have hg : IntegrableOn g (Ioi (0:ℝ)) := envelope_integrable.const_mul _
  have hsum (x : ℝ) (hx : 0 < x) : Summable (fun n : ℕ => corePair Phi T u sigma n x) :=
    (hp.mul_left (2*B*envelope x)).of_norm_bounded (fun n => hb n x hx)
  have hpartial (L : ℕ) (x : ℝ) (hx : 0 < x) :
      ‖∑ n ∈ range L, corePair Phi T u sigma n x‖ ≤ g x := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ n ∈ range L, (2*B*envelope x)*p n := sum_le_sum (fun n hn => hb n x hx)
      _ = (2*B*envelope x)*(∑ n ∈ range L, p n) := by rw [Finset.mul_sum]
      _ ≤ (2*B*envelope x)*Z := mul_le_mul_of_nonneg_left
        (hp.sum_le_tsum _ (fun n hn => by dsimp [p]; positivity))
        (by exact mul_nonneg (by positivity) (envelope_nonneg x))
      _ = _ := by dsimp [g]; ring
  have hmeas (L : ℕ) : AEStronglyMeasurable (fun x : ℝ => cutoff S L x*
      (∑ n ∈ range L, corePair Phi T u sigma n x)) (volume.restrict (Ioi (0:ℝ))) := by
    have he : (fun x : ℝ => cutoff S L x*(∑ n ∈ range L, corePair Phi T u sigma n x)) =
        (fun x => ∑ n ∈ range L,
          (cutoff S L x*core Phi T u sigma ((n+1:ℕ):ℝ) x+
            cutoff S L x*core Phi T u sigma (-((n+1:ℕ):ℝ)) x)) := by
      funext x
      simp only [corePair,Finset.mul_sum,mul_add]
    rw [he]
    apply Integrable.aestronglyMeasurable
    apply Integrable.integrableOn
    apply integrable_finsetSum
    intro n hn
    exact (cutoff_integrable S hS hm hlo hhi hleft hright Phi hPhi.continuous hsPhi L T u sigma _ hT hu hs).fun_add
      (cutoff_integrable S hS hm hlo hhi hleft hright Phi hPhi.continuous hsPhi L T u sigma _ hT hu hs)
  have hbound (L : ℕ) : ∀ᵐ x : ℝ ∂volume.restrict (Ioi (0:ℝ)),
      ‖cutoff S L x*(∑ n ∈ range L, corePair Phi T u sigma n x)‖ ≤ g x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [norm_mul]
    exact ((mul_le_mul_of_nonneg_right (cutoff_bound S hm hlo hhi L x hx)
      (norm_nonneg (∑ n ∈ range L, corePair Phi T u sigma n x))).trans_eq (one_mul _)).trans
        (hpartial L x hx)
  apply tendsto_integral_of_dominated_convergence g hmeas hg hbound
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hc : Tendsto (fun L : ℕ => cutoff S L x) atTop (𝓝 (1:ℂ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [cutoff_eventually S hleft hright x hx] with L hL
    exact hL.symm
  simpa only [one_mul] using hc.mul (hsum x hx).hasSum.tendsto_sum_nat

theorem actual_joint_limit (S : ℝ → ℝ) (hS : Continuous S) (hm : Antitone S)
    (hlo : ∀ x, 0 ≤ S x) (hhi : ∀ x, S x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), S x = 1) (hright : ∀ x, 1 ≤ x → S x = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (T u : ℝ) (sigma : ℂ) (hT : 0 < T) (hu : 0 < u)
    (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8) :
    Tendsto (fun L : ℕ => ∑ k ∈ range (2*L), ∑ n ∈ range L,
      ∫ x in Ioi (0:ℝ), PRZZZeroGapExchange.pair (profile S) Phi
        ((2:ℝ)^k*((2:ℝ)^L)⁻¹) T u sigma n x) atTop
      (𝓝 (∫ x in Ioi (0:ℝ), ∑' n : ℕ, corePair Phi T u sigma n x)) := by
  simp_rw [rectangle_integral S hS hm hlo hhi hleft hright Phi hPhi.continuous hsPhi _ T u sigma hT hu hs]
  exact joint_limit S hS hm hlo hhi hleft hright Phi hPhi hcPhi hsPhi T u sigma hT hu hs hn

#print axioms core_pair_bound
#print axioms rectangle_integral
#print axioms joint_limit
#print axioms actual_joint_limit
end XiPrime8845.PRZZZeroCutoffLimit
