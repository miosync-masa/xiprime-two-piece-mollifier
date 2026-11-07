import PRZZFullWeightJets
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-! Positive supported actual weights are globally smooth, including at zero.
All jets have the original support; Fourier integration by parts therefore
has no boundary premise. The remaining coefficient and frequency costs are explicit. -/
noncomputable section
open scoped ContDiff FourierTransform
open Set Filter Topology MeasureTheory
namespace XiPrime8845.PRZZWeightFourier
open PRZZFullWeightSmooth

theorem support_subset (lo hi : ℝ) (hlo : 0 < lo) (F : ℝ → ℂ) (N k omega : ℝ) (z sigma : ℂ)
    (hN : 0 < N) (hs : Function.support F ⊆ Icc lo hi) :
    Function.support (weight F N k omega z sigma) ⊆ Icc (lo*N) (hi*N) := by
  intro x hx
  have hf : F (N⁻¹*x) ≠ 0 := by
    intro hf
    exact hx (by simp [weight,hf])
  have hh := hs hf
  have he : N*(N⁻¹*x) = x := by field_simp
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hh.1 hN.le,
    mul_le_mul_of_nonneg_left hh.2 hN.le]

theorem compact (lo hi : ℝ) (hlo : 0 < lo) (F : ℝ → ℂ) (N k omega : ℝ) (z sigma : ℂ)
    (hN : 0 < N) (hs : Function.support F ⊆ Icc lo hi) :
    HasCompactSupport (weight F N k omega z sigma) := by
  apply HasCompactSupport.intro isCompact_Icc
  intro x hx
  by_contra hh
  exact hx (support_subset lo hi hlo F N k omega z sigma hN hs hh)

theorem smooth (lo hi : ℝ) (hlo : 0 < lo) (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (N k omega : ℝ) (z sigma : ℂ) (hN : 0 < N) (hk : 0 < k)
    (hsigma : sigma ≠ 0) (hs : Function.support F ⊆ Icc lo hi) :
    ContDiff ℝ ∞ (weight F N k omega z sigma) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : 0 < x
  · exact (weight_smooth F hF N k omega z sigma hk hsigma).contDiffAt (Ioi_mem_nhds hx)
  · have hxn : x < lo*N := by nlinarith [mul_pos hlo hN]
    have he : weight F N k omega z sigma =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [eventually_lt_nhds hxn] with y hy
      by_contra hh
      have := (support_subset lo hi hlo F N k omega z sigma hN hs hh).1
      linarith
    exact contDiffAt_const.congr_of_eventuallyEq he

theorem jet_support (lo hi : ℝ) (hlo : 0 < lo) (F : ℝ → ℂ) (N k omega : ℝ) (z sigma : ℂ)
    (hN : 0 < N) (hs : Function.support F ⊆ Icc lo hi) (n : ℕ) :
    tsupport (iteratedDeriv n (weight F N k omega z sigma)) ⊆ Icc (lo*N) (hi*N) := by
  induction n with
  | zero => exact closure_minimal (support_subset lo hi hlo F N k omega z sigma hN hs) isClosed_Icc
  | succ n ih => rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans ih

/-- Every derivative vanishes outside the original closed support interval. -/
theorem jet_zero (lo hi : ℝ) (hlo : 0 < lo) (F : ℝ → ℂ) (N k omega : ℝ) (z sigma : ℂ)
    (hN : 0 < N) (hs : Function.support F ⊆ Icc lo hi) (n : ℕ)
    (x : ℝ) (hx : x ∉ Icc (lo*N) (hi*N)) :
    iteratedDeriv n (weight F N k omega z sigma) x = 0 := by
  by_contra hh
  exact hx (jet_support lo hi hlo F N k omega z sigma hN hs n (subset_closure hh))

theorem jet_integrable (lo hi : ℝ) (hlo : 0 < lo) (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (N k omega : ℝ) (z sigma : ℂ) (hN : 0 < N) (hk : 0 < k)
    (hsigma : sigma ≠ 0) (hs : Function.support F ⊆ Icc lo hi) (n : ℕ) :
    Integrable (iteratedDeriv n (weight F N k omega z sigma)) := by
  exact ((smooth lo hi hlo F hF N k omega z sigma hN hk hsigma hs).continuous_iteratedDeriv n
    (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))).integrable_of_hasCompactSupport
      (PRZZCutoffJets.jet_support _ (compact lo hi hlo F N k omega z sigma hN hs) n)

/-- Repeated integration by parts for the actual weight, with all global
regularity and integrability supplied from the positive cutoff. -/
theorem fourier_jet (lo hi : ℝ) (hlo : 0 < lo) (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (N k omega : ℝ) (z sigma : ℂ) (hN : 0 < N) (hk : 0 < k)
    (hsigma : sigma ≠ 0) (hs : Function.support F ⊆ Icc lo hi) (n : ℕ) :
    𝓕 (iteratedDeriv n (weight F N k omega z sigma)) =
      fun ξ : ℝ => (2*Real.pi*Complex.I*ξ)^n*𝓕 (weight F N k omega z sigma) ξ := by
  simpa only [smul_eq_mul] using Real.fourier_iteratedDeriv
    (N := ⊤) (smooth lo hi hlo F hF N k omega z sigma hN hk hsigma hs)
    (fun i _ => jet_integrable lo hi hlo F hF N k omega z sigma hN hk hsigma hs i) (by simp : (n:ℕ∞) ≤ ⊤)

theorem norm_fourier_le (f : ℝ → ℂ) (ξ : ℝ) :
    ‖𝓕 f ξ‖ ≤ ∫ x, ‖f x‖ := by
  rw [Real.fourier_eq']
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by simp [norm_smul,Complex.norm_exp])

theorem mass_on_support (lo hi : ℝ) (hlo : 0 < lo) (F : ℝ → ℂ) (N k omega : ℝ) (z sigma : ℂ)
    (hN : 0 < N) (hs : Function.support F ⊆ Icc lo hi) (n : ℕ) :
    (∫ x, ‖iteratedDeriv n (weight F N k omega z sigma) x‖) =
      ∫ x in Icc (lo*N) (hi*N), ‖iteratedDeriv n (weight F N k omega z sigma) x‖ := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [jet_zero lo hi hlo F N k omega z sigma hN hs n x hx,norm_zero]

/-- Exact frequency loss with the derivative L1 mass on the actual support. -/
theorem fourier_bound (lo hi : ℝ) (hlo : 0 < lo) (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (N k omega : ℝ) (z sigma : ℂ) (hN : 0 < N) (hk : 0 < k)
    (hsigma : sigma ≠ 0) (hs : Function.support F ⊆ Icc lo hi)
    (n : ℕ) (ξ : ℝ) (hξ : ξ ≠ 0) :
    ‖𝓕 (weight F N k omega z sigma) ξ‖ ≤
      (∫ x in Icc (lo*N) (hi*N), ‖iteratedDeriv n (weight F N k omega z sigma) x‖)/
        (2*Real.pi*|ξ|)^n := by
  have hh := norm_fourier_le (iteratedDeriv n (weight F N k omega z sigma)) ξ
  rw [fourier_jet lo hi hlo F hF N k omega z sigma hN hk hsigma hs n,
    norm_mul,norm_pow] at hh
  simp only [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos Real.pi_pos,Complex.norm_I,mul_one] at hh
  rw [mass_on_support lo hi hlo F N k omega z sigma hN hs n] at hh
  apply (le_div_iff₀ (pow_pos (by positivity : 0 < 2*Real.pi*|ξ|) n)).mpr
  simpa [mul_comm] using hh

private theorem convolution_continuous (A B : ℝ → ℕ → ℝ) (n : ℕ) (x : ℝ)
    (hA : ∀ i, ContinuousAt (fun y => A y i) x)
    (hB : ∀ i, ContinuousAt (fun y => B y i) x) :
    ContinuousAt (fun y => PRZZFullWeightJets.convolution (A y) (B y) n) x := by
  unfold PRZZFullWeightJets.convolution
  fun_prop

/-- The full explicit all-order envelope is integrated only over the
original support. Constants precede scales, shifts and frequencies. -/
theorem mass_uniform (lo hi : ℝ) (hlo : 0 < lo) (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hs : Function.support F ⊆ Icc lo hi) (a : ℝ) (ha : 0 < a) :
    ∃ C D E : ℕ → ℝ, (∀ n, 0 ≤ C n ∧ 0 ≤ D n ∧ 0 ≤ E n) ∧
      ∀ (n : ℕ) (N k omega R : ℝ) (z sigma : ℂ),
      0 < N → 0 < k → sigma ≠ 0 → (∀ x ∈ Icc (lo*N) (hi*N), |omega/x| ≤ R) →
      (∫ x, ‖iteratedDeriv n (weight F N k omega z sigma) x‖) ≤
        ∫ x in Icc (lo*N) (hi*N), PRZZFullWeightJets.envelope C D E a k x R z sigma n/x^n := by
  have hcF : HasCompactSupport F := HasCompactSupport.intro isCompact_Icc
    (fun x hx => by by_contra hh; exact hx (hs hh))
  obtain ⟨C,D,E,hpos,h⟩ := PRZZFullWeightJets.ordinary_uniform F hF hcF a ha
  refine ⟨C,D,E,hpos,?_⟩
  intro n N k omega R z sigma hN hk hsigma hR
  rw [mass_on_support lo hi hlo F N k omega z sigma hN hs n]
  have he : ContinuousOn
      (fun x : ℝ => PRZZFullWeightJets.envelope C D E a k x R z sigma n/x^n)
      (Icc (lo*N) (hi*N)) := by
    intro x hx
    have hx0 : 0 < x := (mul_pos hlo hN).trans_le hx.1
    have hec : ContinuousAt
        (fun y : ℝ => PRZZFullWeightJets.envelope C D E a k y R z sigma n) x := by
      unfold PRZZFullWeightJets.envelope
      apply convolution_continuous
      · intro i
        apply convolution_continuous
        · intro j
          apply convolution_continuous
          · intro u; exact continuousAt_const
          · intro u
            exact continuousAt_const.mul ((continuousAt_const.mul
              (Real.continuousAt_log hx0.ne')).rexp)
        · intro j; exact continuousAt_const
      · intro i
        apply continuousAt_const.mul
        exact (show ContinuousAt (fun y : ℝ => k*y^2) x from
          continuousAt_const.mul (continuousAt_id.pow 2)).rpow_const
          (Or.inl (mul_ne_zero hk.ne' (pow_ne_zero 2 hx0.ne')))
    exact (hec.div (continuousAt_id.pow n) (pow_ne_zero n hx0.ne')).continuousWithinAt
  apply integral_mono_ae (jet_integrable lo hi hlo F hF N k omega z sigma hN hk hsigma hs n).norm.integrableOn
    (he.integrableOn_compact isCompact_Icc)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact h n N k omega x R z sigma hk ((mul_pos hlo hN).trans_le hx.1) hsigma (hR x hx)

#print axioms mass_uniform
#print axioms norm_fourier_le
#print axioms mass_on_support
#print axioms fourier_bound
#print axioms support_subset
#print axioms compact
#print axioms smooth
#print axioms jet_support
#print axioms jet_zero
#print axioms jet_integrable
#print axioms fourier_jet
end XiPrime8845.PRZZWeightFourier
