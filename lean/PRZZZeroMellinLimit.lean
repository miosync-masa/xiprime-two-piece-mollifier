import PRZZZeroMellinSpace
import PRZZZeroCosine

/-! Actual supported zero rows in shifted Mellin form, followed by the
simultaneous dyadic/spatial and signed-gap exhaustion. The limit remains
the actual cosine field with time integration first. No unlocalized
cosine/Mellin interchange or two-branch cancellation is assumed here. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex MeasureTheory Set Filter Topology Finset
namespace XiPrime8845.PRZZZeroMellinLimit
open PRZZZeroMellinSpace PRZZZeroGap PRZZZeroGapExchange PRZZPartitionMass
set_option maxHeartbeats 5000000

def mellinRow (F Phi : ℝ → ℂ) (M T u delta : ℝ) (sigma : ℂ) : ℂ :=
  (1/(2*Real.pi):ℂ)*∫ t in Ioi (0:ℝ), Phi (t/T)*∫ tau : ℝ, ∫ x in Ioi (0:ℝ),
    lifted F M (2*Real.pi*u/t) (delta*t/u) (sigma+1) sigma (5/4) x tau

theorem row_mellin (F Phi : ℝ → ℂ) (hF : Continuous F) (hPhi : Continuous Phi)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (M T u delta : ℝ) (sigma : ℂ)
    (hM : 0 < M) (hT : 0 < T) (hu : 0 < u) (hs : sigma ≠ 0) :
    (∫ x in Ioi (0:ℝ), row F Phi M T u sigma delta x) =
      mellinRow F Phi M T u delta sigma := by
  have h := original_zero_time F Phi hF hPhi hsF hsPhi M u delta T (sigma+1) sigma hM hu hT hs
  simpa only [PRZZZeroGap.kernel_time,row,mellinRow] using h

theorem pair_mellin (F Phi : ℝ → ℂ) (hF : Continuous F) (hPhi : Continuous Phi)
    (hsF : Function.support F ⊆ Icc (1/2:ℝ) 3)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (M T u : ℝ) (sigma : ℂ) (n : ℕ)
    (hM : 0 < M) (hT : 0 < T) (hu : 0 < u) (hs : sigma ≠ 0) :
    (∫ x in Ioi (0:ℝ), pair F Phi M T u sigma n x) =
      mellinRow F Phi M T u ((n+1:ℕ):ℝ) sigma+
        mellinRow F Phi M T u (-((n+1:ℕ):ℝ)) sigma := by
  unfold PRZZZeroGapExchange.pair
  rw [integral_add
    ((row_integrable F Phi hF hPhi hsF hsPhi M T u sigma _ hM hT hu hs).integrableOn)
    ((row_integrable F Phi hF hPhi hsF hsPhi M T u sigma _ hM hT hu hs).integrableOn)]
  rw [row_mellin F Phi hF hPhi hsF hsPhi M T u _ sigma hM hT hu hs,
    row_mellin F Phi hF hPhi hsF hsPhi M T u _ sigma hM hT hu hs]

theorem actual_mellin_exhaustion (S : ℝ → ℝ) (hS : Continuous S) (hm : Antitone S)
    (hlo : ∀ x, 0 ≤ S x) (hhi : ∀ x, S x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), S x = 1) (hright : ∀ x, 1 ≤ x → S x = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (T u : ℝ) (sigma : ℂ) (hT : 0 < T) (hu : 0 < u)
    (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8) :
    Tendsto (fun L : ℕ => ∑ k ∈ range (2*L), ∑ n ∈ range L,
      (mellinRow (profile S) Phi ((2:ℝ)^k*((2:ℝ)^L)⁻¹) T u ((n+1:ℕ):ℝ) sigma+
       mellinRow (profile S) Phi ((2:ℝ)^k*((2:ℝ)^L)⁻¹) T u (-((n+1:ℕ):ℝ)) sigma)) atTop
      (𝓝 (∫ x in Ioi (0:ℝ), PRZZZeroCosine.cosineField Phi T u sigma x)) := by
  obtain ⟨hp,hsp,hcap⟩ := PRZZZeroSpatialLimit.profile_data S hS hm hlo hhi hleft hright
  have he (L k n : ℕ) := pair_mellin (profile S) Phi hp hPhi.continuous hsp hsPhi
    ((2:ℝ)^k*((2:ℝ)^L)⁻¹) T u sigma n (by positivity) hT hu hs
  simp_rw [← he]
  exact PRZZZeroCosine.actual_cosine_limit S hS hm hlo hhi hleft hright Phi hPhi hcPhi hsPhi
    T u sigma hT hu hs hn

#print axioms row_mellin
#print axioms pair_mellin
#print axioms actual_mellin_exhaustion
end XiPrime8845.PRZZZeroMellinLimit
