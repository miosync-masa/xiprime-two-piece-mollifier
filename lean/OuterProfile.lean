import LogProfileSum
import CoprimeHead
import BetaKernel

/-! Concrete D1 profile products in the outer Euler-weighted sum.
This identifies the model main term, not the error of the full coprime sum. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Filter Topology
namespace XiPrime8845.OuterProfile
open ShiftedMobius ShiftedEndpoint WeightDerivatives ShiftedTotient LogProfileSum
set_option maxHeartbeats 1000000

def profile (θ : ℝ) (P Q : Polynomial ℂ) (A B : ℂ) (u : ℝ) : ℂ :=
  mainTerm u θ P A * mainTerm u θ Q B

def profileDeriv (θ : ℝ) (P Q : Polynomial ℂ) (A B : ℂ) (u : ℝ) : ℂ :=
  mainTerm u θ P.derivative A / θ * mainTerm u θ Q B +
    mainTerm u θ P A * (mainTerm u θ Q.derivative B / θ)

theorem mainTerm_hasDerivAt (u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) :
    HasDerivAt (fun u => mainTerm u θ P A) (mainTerm u θ P.derivative A / θ) u := by
  have h (F : Polynomial ℂ) := (F.hasDerivAt ((u:ℂ)/θ)).comp (u:ℂ)
    ((hasDerivAt_id (u:ℂ)).div_const (θ:ℂ))
  convert! (((h P).const_mul A).add ((h P.derivative).div_const (θ:ℂ))).comp_ofReal using 1
  · funext v; simp [mainTerm, Complex.ofReal_div]
  · simp only [mainTerm, Complex.ofReal_div]; ring

theorem profile_hasDerivAt (u θ : ℝ) (P Q : Polynomial ℂ) (A B : ℂ) :
    HasDerivAt (profile θ P Q A B) (profileDeriv θ P Q A B u) u :=
  (mainTerm_hasDerivAt u θ P A).mul (mainTerm_hasDerivAt u θ Q B)

theorem profileDeriv_continuous (θ : ℝ) (P Q : Polynomial ℂ) (A B : ℂ) :
    Continuous (profileDeriv θ P Q A B) := by unfold profileDeriv mainTerm; fun_prop

def valueCap (P Q : Polynomial ℂ) (θ C U : ℝ) : ℝ :=
  firstCap P θ C U * firstCap Q θ C U

def derivativeCap (P Q : Polynomial ℂ) (θ C U : ℝ) : ℝ :=
  firstCap P.derivative θ C U / θ * firstCap Q θ C U +
    firstCap P θ C U * (firstCap Q.derivative θ C U / θ)

theorem profile_bound (θ C U u : ℝ) (P Q : Polynomial ℂ) (A B : ℂ)
    (hθ : 0 < θ) (hA : ‖A‖ ≤ C) (hB : ‖B‖ ≤ C) (hu : u ∈ Set.Icc 0 U) :
    ‖profile θ P Q A B u‖ ≤ valueCap P Q θ C U := by
  rw [profile, norm_mul]
  exact mul_le_mul (mainTerm_bound P A u θ C U hθ hA hu)
    (mainTerm_bound Q B u θ C U hθ hB hu) (norm_nonneg _)
    (firstCap_nonneg P θ C U hθ ((norm_nonneg A).trans hA) (hu.1.trans hu.2))

theorem profileDeriv_bound (θ C U u : ℝ) (P Q : Polynomial ℂ) (A B : ℂ)
    (hθ : 0 < θ) (hA : ‖A‖ ≤ C) (hB : ‖B‖ ≤ C) (hu : u ∈ Set.Icc 0 U) :
    ‖profileDeriv θ P Q A B u‖ ≤ derivativeCap P Q θ C U := by
  have hC := (norm_nonneg A).trans hA
  have hU := hu.1.trans hu.2
  apply (norm_add_le _ _).trans
  simp only [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hθ]
  exact add_le_add
    (mul_le_mul (div_le_div_of_nonneg_right (mainTerm_bound P.derivative A u θ C U hθ hA hu) hθ.le)
      (mainTerm_bound Q B u θ C U hθ hB hu) (norm_nonneg _)
      (div_nonneg (firstCap_nonneg _ _ _ _ hθ hC hU) hθ.le))
    (mul_le_mul (mainTerm_bound P A u θ C U hθ hA hu)
      (div_le_div_of_nonneg_right (mainTerm_bound Q.derivative B u θ C U hθ hB hu) hθ.le)
      (div_nonneg (norm_nonneg _) hθ.le) (firstCap_nonneg _ _ _ _ hθ hC hU))

theorem profile_sum_uniform (P Q : Polynomial ℂ) (θ C U : ℝ)
    (hθ : 0 < θ) (hC : 0 ≤ C) (hU : 0 ≤ U) (hCU : C*U ≤ 1) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => shiftedSum L U p.1 p.2 (profile θ P Q p.1 p.2))
      (fun p => ∫ u in 0..U, profile θ P Q p.1 p.2 u) atTop
      {p | ‖p.1‖ ≤ C ∧ ‖p.2‖ ≤ C} := by
  apply shifted_family_uniform _ Prod.fst Prod.snd _ _ C U
    (valueCap P Q θ C U) (derivativeCap P Q θ C U) hU
    (mul_nonneg (firstCap_nonneg _ _ _ _ hθ hC hU) (firstCap_nonneg _ _ _ _ hθ hC hU)) hCU
  · exact fun p hp => hp.1
  · exact fun p hp => hp.2
  · exact fun p _ u => profile_hasDerivAt u θ P Q p.1 p.2
  · exact fun p _ => profileDeriv_continuous θ P Q p.1 p.2
  · exact fun p hp u hu => profile_bound θ C U u P Q p.1 p.2 hθ hp.1 hp.2 hu
  · exact fun p hp u hu => profileDeriv_bound θ C U u P Q p.1 p.2 hθ hp.1 hp.2 hu

/-- The concrete integral is exactly the previously certified K00 functional. -/
theorem integral_eq_H00 (θ : ℝ) (P Q : Polynomial ℂ) (A B : ℂ) :
    (∫ u in 0..θ, profile θ P Q A B u) = BetaKernel.H 0 0 A B θ P Q := by
  simp only [BetaKernel.H, BetaKernel.assemble00, Nat.add_zero, pow_zero, div_one,
    BetaKernel.monomialIntegral, Nat.sub_self, pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul]
  have h : (fun v : ℝ => BetaKernel.D 1 A θ (θ-v) P * BetaKernel.D 1 B θ (θ-v) Q) =
      fun v => profile θ P Q A B (θ-v) := by
    funext v
    simp only [BetaKernel.D, ↓reduceIte, mainTerm, profile]
    ring
  rw [h, intervalIntegral.integral_comp_sub_left]
  simp

theorem profile_sum_twoBidiscs (P Q : Polynomial ℂ) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => shiftedSum L PRZZAsymptotic.theta p.1 p.2
        (profile PRZZAsymptotic.theta P Q p.1 p.2))
      (fun p => BetaKernel.H 0 0 p.1 p.2 PRZZAsymptotic.theta P Q)
      atTop ElementaryGcd.twoBidiscs := by
  have h := (profile_sum_uniform P Q PRZZAsymptotic.theta (5*PRZZAsymptotic.R/4)
    PRZZAsymptotic.theta (by norm_num [PRZZAsymptotic.theta])
    (by have := PRZZAsymptotic.radius_pos; positivity)
    (by norm_num [PRZZAsymptotic.theta]) ShiftedEulerUniform.witness_size).mono
      (fun p hp => twoBidiscs_norm p hp)
  simpa only [integral_eq_H00] using h

/-- The finite coprimality head already has the SAME concrete profile factor.
Passing its truncated supported mass to the full Euler factor is not hidden here. -/
theorem headMain_factor (N g : ℕ) (u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) :
    CoprimeHead.headMain N g u θ P A = mainTerm u θ P A *
      (SupportProductTail.supportedSum g (Finset.Icc 1 N) (fun r => 1/(r:ℝ)) : ℂ) := by
  simp only [CoprimeHead.headMain, SupportProductTail.supportedSum,
    Complex.ofReal_sum, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast,
    Finset.mul_sum, mul_one_div]

def eulerMain (L : ℝ) (g : ℕ) (u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) : ℂ :=
  euler (A/L) g * mainTerm u θ P A

theorem eulerMain_product_weight (L u θ : ℝ) (g : ℕ) (P Q : Polynomial ℂ) (A B : ℂ) :
    (μ g:ℂ)^2 * ElementaryGcd.generalizedTotient (1+A/L+B/L) g /
      (g:ℂ)^(2+A/L+B/L) * eulerMain L g u θ P A * eulerMain L g u θ Q B =
      outerWeight (A/L) (B/L) g * profile θ P Q A B u := by
  unfold eulerMain outerWeight profile
  ring

/-- Literal outer expression AFTER inserting the Euler-model inner main terms.
No equality with the actual coprime inner sums is part of this definition. -/
def modelSum (L θ : ℝ) (P Q : Polynomial ℂ) (A B : ℂ) : ℂ :=
  (∑ g ∈ Finset.Ioc 0 ⌊Real.exp (L*θ)⌋₊,
    (μ g:ℂ)^2 * ElementaryGcd.generalizedTotient (1+A/L+B/L) g /
      (g:ℂ)^(2+A/L+B/L) *
      eulerMain L g (coordinate L θ g) θ P A *
      eulerMain L g (coordinate L θ g) θ Q B)/(L:ℂ)

theorem modelSum_eq (L θ : ℝ) (P Q : Polynomial ℂ) (A B : ℂ) :
    modelSum L θ P Q A B = shiftedSum L θ A B (profile θ P Q A B) := by
  unfold modelSum shiftedSum
  simp only [eulerMain_product_weight]

theorem modelSum_twoBidiscs (P Q : Polynomial ℂ) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => modelSum L PRZZAsymptotic.theta P Q p.1 p.2)
      (fun p => BetaKernel.H 0 0 p.1 p.2 PRZZAsymptotic.theta P Q)
      atTop ElementaryGcd.twoBidiscs := by
  simpa only [modelSum_eq] using profile_sum_twoBidiscs P Q

/-- Swapped positive-side evaluation is obtained from the theorem on the union,
not from analytic continuation or pointwise convergence on the negative side. -/
theorem modelSum_reflected (P Q : Polynomial ℂ) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => modelSum L PRZZAsymptotic.theta P Q (-p.2) (-p.1))
      (fun p => BetaKernel.H 0 0 (-p.2) (-p.1) PRZZAsymptotic.theta P Q)
      atTop PRZZAsymptotic.witnessBidisc := by
  have h := modelSum_twoBidiscs P Q
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h eps heps] with L hL
  intro p hp
  exact hL (ElementaryGcd.reflect p) (Or.inr ⟨p,hp,rfl⟩)

#print axioms modelSum_eq
#print axioms modelSum_twoBidiscs
#print axioms modelSum_reflected
#print axioms mainTerm_hasDerivAt
#print axioms profile_sum_uniform
#print axioms integral_eq_H00
#print axioms profile_sum_twoBidiscs
#print axioms headMain_factor
#print axioms eulerMain_product_weight
end XiPrime8845.OuterProfile
