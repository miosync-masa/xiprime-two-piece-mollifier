import FengPrimeProfile
import FengPrimeExclusion

/-! The finite outside main proxy converges to the inverse profile, with an
explicit Euler envelope and a growing coprimality modulus. This does not assert
that replacing the actual inner Mobius sums by this proxy costs o(1). -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Finset Filter Topology
namespace XiPrime8845.FengOutsidePrime
open FengPrimeProfile FengPrimeExclusion WeightDerivatives
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

def restrictedTransform (L u θ : ℝ) (g : ℕ) (G : Polynomial ℂ) (A : ℂ) : ℂ :=
  (∑ n ∈ (Ioc 0 ⌊Real.exp (L*u)⌋₊).filter (fun n => n.Coprime g),
    (mass n) • (-first A u θ G (Real.log n/L)))/(L:ℂ)^2

theorem restriction_error (L u θ C U : ℝ) (g : ℕ) (G : Polynomial ℂ) (A : ℂ)
    (hL : 0 < L) (hθ : 0 < θ) (hC : 0 ≤ C) (hu : u ∈ Set.Icc 0 U)
    (hg : g ≠ 0) (hgL : Real.log g ≤ L*U) (hA : ‖A‖ ≤ C) :
    ‖restrictedTransform L u θ g G A-profileTransform L u θ G A‖ ≤
      firstCap G θ C U*(U/L+2*Zeta23.XiPrime.Cdef/L^2) := by
  let s := Ioc 0 ⌊Real.exp (L*u)⌋₊
  let f := fun n => (mass n) • (-first A u θ G (Real.log n/L))
  have hs := sum_filter_add_sum_filter_not s (fun n => n.Coprime g) f
  have he : restrictedTransform L u θ g G A-profileTransform L u θ G A =
      -(∑ n ∈ s.filter (fun n => ¬n.Coprime g), f n)/(L:ℂ)^2 := by
    change (∑ n ∈ s.filter (fun n => n.Coprime g), f n)/(L:ℂ)^2 -
      (∑ n ∈ s, f n)/(L:ℂ)^2 = _
    rw [← hs]; ring
  have hcap : 0 ≤ firstCap G θ C U := firstCap_nonneg G θ C U hθ hC (hu.1.trans hu.2)
  have hb : ‖∑ n ∈ s.filter (fun n => ¬n.Coprime g), f n‖ ≤
      firstCap G θ C U * ∑ n ∈ s.filter (fun n => ¬n.Coprime g), mass n := by
    apply (norm_sum_le _ _).trans
    rw [mul_sum]
    apply sum_le_sum
    intro n hn
    have hni := (mem_filter.mp hn).1
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (mem_Ioc.mp hni).1
    have hnlog : Real.log n ≤ L*u := (Real.log_le_iff_le_exp
      (lt_of_lt_of_le zero_lt_one hn1)).mpr
      ((Nat.le_floor_iff (Real.exp_pos _).le).mp (mem_Ioc.mp hni).2)
    have ht := ShiftWeights.normalized_log_mem n L u hn1 hL hnlog
    dsimp only [f]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (mass_nonneg n),norm_neg]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (first_bound A u θ (Real.log n/L) C U G hθ hA hu.2 ht) (mass_nonneg n)
  rw [he,norm_div,norm_neg,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
  apply (div_le_div_of_nonneg_right hb (sq_nonneg L)).trans
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (excluded_mass_scaled g hg L u U hL hu.1 hgL) hcap

def errorEnvelope (L θ C U : ℝ) (G : Polynomial ℂ) : ℝ :=
  errorCap G θ C U/L+firstCap G θ C U*(U/L+2*Zeta23.XiPrime.Cdef/L^2)

theorem errorEnvelope_tendsto (θ C U : ℝ) (G : Polynomial ℂ) :
    Tendsto (fun L => errorEnvelope L θ C U G) atTop (nhds 0) := by
  have hi := tendsto_inv_atTop_zero (𝕜:=ℝ)
  have h1 := hi.const_mul (errorCap G θ C U)
  have h2 := (hi.const_mul U).add ((hi.pow 2).const_mul (2*Zeta23.XiPrime.Cdef))
  simpa [errorEnvelope,div_eq_mul_inv,inv_pow] using h1.add (h2.const_mul (firstCap G θ C U))

/-- Pointwise form of a uniform estimate on the L-dependent growing-g domain. -/
theorem restrictedTransform_bound (L u θ C U : ℝ) (g : ℕ) (G : Polynomial ℂ)
    (hG : G.eval 0 = 0) (A : ℂ) (hL : 0 < L) (hθ : 0 < θ) (hC : 0 ≤ C)
    (hu : u ∈ Set.Icc 0 U) (hg : g ≠ 0) (hgL : Real.log g ≤ L*U) (hA : ‖A‖ ≤ C) :
    ‖restrictedTransform L u θ g G A-BetaKernel.D (-1) A θ u G‖ ≤ errorEnvelope L θ C U G := by
  have h1 := restriction_error L u θ C U g G A hL hθ hC hu hg hgL hA
  have h2 := profileTransform_bound L u θ C U G A hL hθ hC hu hA
  rw [FengOutsideProfile.convolution_inverse A u θ G hG] at h2
  exact (norm_sub_le_norm_sub_add_norm_sub _ (profileTransform L u θ G A) _).trans
    (by unfold errorEnvelope; linarith)

theorem restrictedTransform_uniform_growing (G : Polynomial ℂ) (hG : G.eval 0 = 0)
    (θ C U : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) :
    ∀ eps > 0, ∀ᶠ L : ℝ in atTop, ∀ g : ℕ, g ≠ 0 → Real.log g ≤ L*U →
      ∀ u ∈ Set.Icc 0 U, ∀ A : ℂ, ‖A‖ ≤ C →
      ‖restrictedTransform L u θ g G A-BetaKernel.D (-1) A θ u G‖ < eps := by
  intro eps heps
  filter_upwards [eventually_gt_atTop (0:ℝ),
    (errorEnvelope_tendsto θ C U G).eventually (gt_mem_nhds heps)] with L hL he
  intro g hg hgL u hu A hA
  exact (restrictedTransform_bound L u θ C U g G hG A hL hθ hC hu hg hgL hA).trans_lt he

/-- Exact bridge to the finite proxy, not an independently chosen model. -/
theorem mainProxy_eq (L u θ : ℝ) (g : ℕ) (G : Polynomial ℂ) (A : ℂ) :
    FengOutside.mainProxy ⌊Real.exp (L*u)⌋₊ g L u θ G A =
      (μ g:ℂ)*(SupportTail.eulerMass g 0:ℂ)*restrictedTransform L u θ g G A := by
  have hs : Icc 1 ⌊Real.exp (L*u)⌋₊ = Ioc 0 ⌊Real.exp (L*u)⌋₊ := by
    ext n; simp only [mem_Icc,mem_Ioc]; omega
  unfold FengOutside.mainProxy FengOutside.transform restrictedTransform
  rw [hs]
  simp only [mul_sum,sum_div]
  apply sum_congr rfl
  intro n hn
  simp only [profile_identity,CoprimeEulerCompletion.zeroEulerMain,FengAtG.mark,
    CoprimeShift.supportFactor,ShiftedMobius.mainTerm,BetaKernel.D,↓reduceIte,
    mass,Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_natCast]
  ring

theorem mainProxy_error (L u θ C U : ℝ) (g : ℕ) (G : Polynomial ℂ)
    (hG : G.eval 0 = 0) (A : ℂ) (hL : 0 < L) (hθ : 0 < θ) (hC : 0 ≤ C)
    (hu : u ∈ Set.Icc 0 U) (hg : g ≠ 0) (hgL : Real.log g ≤ L*U) (hA : ‖A‖ ≤ C) :
    ‖FengOutside.mainProxy ⌊Real.exp (L*u)⌋₊ g L u θ G A-
      (μ g:ℂ)*(SupportTail.eulerMass g 0:ℂ)*BetaKernel.D (-1) A θ u G‖ ≤
      SupportTail.eulerMass g 0*errorEnvelope L θ C U G := by
  rw [mainProxy_eq,← mul_sub,norm_mul,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (CoprimeEndpoint.euler_nonneg g hg)]
  have hm : ‖(μ g:ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_intCast] using (show |(μ g:ℝ)| ≤ 1 by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=g))
  exact mul_le_mul
    (by simpa using mul_le_mul_of_nonneg_right hm (CoprimeEndpoint.euler_nonneg g hg))
    (restrictedTransform_bound L u θ C U g G hG A hL hθ hC hu hg hgL hA)
    (norm_nonneg _) (CoprimeEndpoint.euler_nonneg g hg)

/-- The same error envelope works on both bidiscs and on all g<=exp(L U).
The Euler factor is retained; it is not asserted uniformly bounded in g. -/
theorem mainProxy_twoBidiscs (G : Polynomial ℂ) (hG : G.eval 0 = 0)
    (θ U : ℝ) (hθ : 0 < θ) :
    ∀ eps > 0, ∀ᶠ L : ℝ in atTop, ∀ g : ℕ, g ≠ 0 → Real.log g ≤ L*U →
      ∀ u ∈ Set.Icc 0 U, ∀ p ∈ ElementaryGcd.twoBidiscs,
      ‖FengOutside.mainProxy ⌊Real.exp (L*u)⌋₊ g L u θ G p.2-
        (μ g:ℂ)*(SupportTail.eulerMass g 0:ℂ)*BetaKernel.D (-1) p.2 θ u G‖ ≤
        SupportTail.eulerMass g 0*eps := by
  intro eps heps
  let C := 5*PRZZAsymptotic.R/4
  have hC : 0 ≤ C := by dsimp [C]; have := PRZZAsymptotic.radius_pos; positivity
  filter_upwards [eventually_gt_atTop (0:ℝ),
    (errorEnvelope_tendsto θ C U G).eventually (gt_mem_nhds heps)] with L hL he
  intro g hg hgL u hu p hp
  exact (mainProxy_error L u θ C U g G hG p.2 hL hθ hC hu hg hgL
    (ShiftedMobius.twoBidiscs_norm p hp).2).trans
    (mul_le_mul_of_nonneg_left he.le (CoprimeEndpoint.euler_nonneg g hg))

#print axioms restriction_error
#print axioms errorEnvelope_tendsto
#print axioms restrictedTransform_uniform_growing
#print axioms mainProxy_eq
#print axioms mainProxy_error
#print axioms mainProxy_twoBidiscs
end XiPrime8845.FengOutsidePrime
