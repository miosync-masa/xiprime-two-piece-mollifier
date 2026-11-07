import PRZZZeroCutoffLimit
import PRZZZeroReflection

/-! The actual zero mode after removal of both gap/spatial cutoffs,
written with a cosine time integral. The integration order is retained:
this is not the unevaluated conditional cosine Mellin interchange. -/
noncomputable section
open scoped BigOperators ContDiff
open Complex MeasureTheory Set Filter Topology Finset
namespace XiPrime8845.PRZZZeroCosine
open PRZZZeroGap PRZZZeroGapExchange PRZZZeroCutoffLimit PRZZZeroSpatialLimit
open PRZZTimeAmplitude PRZZPartitionMass
set_option maxHeartbeats 5000000

theorem time_integrable (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (T k omega : ℝ) (sigma : ℂ) (hT : 0 < T) (hk : 0 < k) (hs : sigma ≠ 0) :
    Integrable (fun t : ℝ => Complex.exp (I*((t*omega:ℝ):ℂ))*amplitude Phi T k sigma t) := by
  have hc := (smooth Phi hPhi hsPhi T k sigma hT hk hs).continuous
  have hf : Continuous (fun t : ℝ => Complex.exp (I*((t*omega:ℝ):ℂ))*amplitude Phi T k sigma t) := by
    fun_prop
  exact hf.integrable_of_hasCompactSupport ((compact Phi hsPhi T k sigma hT).mul_left)

/-- Pair the actual two gap signs, after time integration. Neither a
Fubini assumption on the unlocalized oscillatory kernel nor a Mellin
transform formula is used. -/
theorem core_cosine (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (T u delta x : ℝ) (sigma : ℂ) (hT : 0 < T) (hu : 0 < u)
    (hx : 0 < x) (hs : sigma ≠ 0) :
    core Phi T u sigma delta x+core Phi T u sigma (-delta) x =
      2*Complex.exp (-(sigma+1)*(Real.log x:ℂ))*
        (∫ t : ℝ, cos ((t*(delta/(u*x)):ℝ):ℂ)*amplitude Phi T (2*Real.pi*u*x^2) sigma t) := by
  have hp := time_integrable Phi hPhi hsPhi T (2*Real.pi*u*x^2) (delta/(u*x)) sigma hT (by positivity) hs
  have hm := time_integrable Phi hPhi hsPhi T (2*Real.pi*u*x^2) ((-delta)/(u*x)) sigma hT (by positivity) hs
  have he (t : ℝ) :
      Complex.exp (I*((t*(delta/(u*x)):ℝ):ℂ))*amplitude Phi T (2*Real.pi*u*x^2) sigma t+
        Complex.exp (I*((t*((-delta)/(u*x)):ℝ):ℂ))*amplitude Phi T (2*Real.pi*u*x^2) sigma t =
      2*(cos ((t*(delta/(u*x)):ℝ):ℂ)*amplitude Phi T (2*Real.pi*u*x^2) sigma t) := by
    have hh (y : ℂ) : Complex.exp (I*y)+Complex.exp (-(I*y)) = 2*cos y := by
      rw [Complex.cos]
      ring_nf
    simp only [neg_div,mul_neg,Complex.ofReal_neg]
    calc
      _ = (Complex.exp (I*((t*(delta/(u*x)):ℝ):ℂ))+
          Complex.exp (-(I*((t*(delta/(u*x)):ℝ):ℂ))))*amplitude Phi T (2*Real.pi*u*x^2) sigma t := by
        ring
      _ = _ := by rw [hh]; ring
  unfold core
  rw [← mul_add,← integral_add hp hm]
  simp_rw [he]
  rw [integral_const_mul]
  ring

def cosineField (Phi : ℝ → ℂ) (T u : ℝ) (sigma : ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℕ, 2*Complex.exp (-(sigma+1)*(Real.log x:ℂ))*
    (∫ t : ℝ, cos ((t*(((n+1:ℕ):ℝ)/(u*x)):ℝ):ℂ)*
      amplitude Phi T (2*Real.pi*u*x^2) sigma t)

theorem core_series_cosine (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (T u x : ℝ) (sigma : ℂ) (hT : 0 < T) (hu : 0 < u)
    (hx : 0 < x) (hs : sigma ≠ 0) :
    (∑' n : ℕ, corePair Phi T u sigma n x) = cosineField Phi T u sigma x := by
  apply tsum_congr
  intro n
  exact core_cosine Phi hPhi hsPhi T u ((n+1:ℕ):ℝ) x sigma hT hu hx hs

/-- Both cutoffs removed in a single actual finite-family limit. The
resulting cosine field still has time integration inside the spatial
integral; its Mellin evaluation must justify changing that order. -/
theorem actual_cosine_limit (S : ℝ → ℝ) (hS : Continuous S) (hm : Antitone S)
    (hlo : ∀ x, 0 ≤ S x) (hhi : ∀ x, S x ≤ 1)
    (hleft : ∀ x ≤ (1/2:ℝ), S x = 1) (hright : ∀ x, 1 ≤ x → S x = 0)
    (Phi : ℝ → ℂ) (hPhi : ContDiff ℝ ∞ Phi) (hcPhi : HasCompactSupport Phi)
    (hsPhi : Function.support Phi ⊆ Icc (1:ℝ) 2)
    (T u : ℝ) (sigma : ℂ) (hT : 0 < T) (hu : 0 < u)
    (hs : sigma ≠ 0) (hn : ‖sigma‖ ≤ 1/8) :
    Tendsto (fun L : ℕ => ∑ k ∈ range (2*L), ∑ n ∈ range L,
      ∫ x in Ioi (0:ℝ), PRZZZeroGapExchange.pair (profile S) Phi
        ((2:ℝ)^k*((2:ℝ)^L)⁻¹) T u sigma n x) atTop
      (𝓝 (∫ x in Ioi (0:ℝ), cosineField Phi T u sigma x)) := by
  have hh := actual_joint_limit S hS hm hlo hhi hleft hright Phi hPhi hcPhi hsPhi T u sigma hT hu hs hn
  have he : (∫ x in Ioi (0:ℝ), ∑' n : ℕ, corePair Phi T u sigma n x) =
      ∫ x in Ioi (0:ℝ), cosineField Phi T u sigma x := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact core_series_cosine Phi hPhi hsPhi T u x sigma hT hu hx hs
  rwa [he] at hh

#print axioms time_integrable
#print axioms core_cosine
#print axioms core_series_cosine
#print axioms actual_cosine_limit
end XiPrime8845.PRZZZeroCosine
