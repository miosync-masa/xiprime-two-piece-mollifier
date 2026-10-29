import FengAtG
import CoprimeEndpoint

/-! Endpoint-safe bounds for the logarithmic block of Feng at g*n.
The prime-power correction is NOT bounded by these theorems. -/
noncomputable section
open scoped BigOperators
open Filter Topology
namespace XiPrime8845.FengLogBounds
open FengAtG ShiftedEndpoint WeightedMobius SupportProductTail
set_option maxHeartbeats 1000000

/-- A fixed radius-one Cauchy margin works for every g and includes u=0. -/
theorem coprime_derivative_bound (k : ℕ) (P : Polynomial ℂ) (hP : P.eval 0 = 0)
    (A : ℂ) (g : ℕ) (L u θ C U K : ℝ) (hL : 0 < L) (hθ : 0 < θ)
    (hA : ‖A‖ ≤ C) (hu : u ∈ Set.Icc 0 U) (hK : 0 ≤ K)
    (hbound : ∀ t : ℝ, 0 ≤ t → absoluteError t ≤ K) :
    ‖iteratedDeriv k (coprimeScaled ⌊Real.exp (L*u)⌋₊ g L u θ P) A‖ ≤
      (k.factorial : ℝ) * (coprimeCap P θ (C+1) U K *
        supportedSum g (Finset.Icc 1 ⌊Real.exp (L*U)⌋₊) (fun r => 1/(r:ℝ))) := by
  have hs := coprimeScaled_entire ⌊Real.exp (L*u)⌋₊ g L u θ P
  have hb : ∀ z ∈ Metric.sphere A 1,
      ‖coprimeScaled ⌊Real.exp (L*u)⌋₊ g L u θ P z‖ ≤
        coprimeCap P θ (C+1) U K *
          supportedSum g (Finset.Icc 1 ⌊Real.exp (L*U)⌋₊) (fun r => 1/(r:ℝ)) := by
    intro z hz
    have hzC : ‖z‖ ≤ C+1 := by
      have hh := norm_add_le (z-A) A
      rw [sub_add_cancel,mem_sphere_iff_norm.mp hz] at hh
      linarith
    exact scaled_coprime_common_bound P hP z g L u θ (C+1) U K hL hθ hzC hu hK hbound
  simpa only [one_pow,div_one] using
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k (by norm_num : (0:ℝ)<1)
      (hs.differentiable (by simp)).diffContOnCl hb

theorem logBlock_bound (P : Polynomial ℂ) (hP : P.eval 0 = 0)
    (A : ℂ) (g : ℕ) (L u θ C U V K : ℝ) (hg : g ≠ 0)
    (hL : 0 < L) (hθ : 0 < θ) (hA : ‖A‖ ≤ C) (hu : u ∈ Set.Icc 0 U)
    (ht : |Real.log g/L| ≤ V) (hK : 0 ≤ K)
    (hbound : ∀ t : ℝ, 0 ≤ t → absoluteError t ≤ K) :
    ‖logBlock ⌊Real.exp (L*u)⌋₊ g L u θ P A‖ ≤
      (V^2+2*V+2) * (coprimeCap P θ (C+1) U K *
        supportedSum g (Finset.Icc 1 ⌊Real.exp (L*U)⌋₊) (fun r => 1/(r:ℝ))) := by
  let B := coprimeCap P θ (C+1) U K *
    supportedSum g (Finset.Icc 1 ⌊Real.exp (L*U)⌋₊) (fun r => 1/(r:ℝ))
  have h0 : ‖coprimeScaled ⌊Real.exp (L*u)⌋₊ g L u θ P A‖ ≤ B := by
    simpa [B] using coprime_derivative_bound 0 P hP A g L u θ C U K hL hθ hA hu hK hbound
  have h1 : ‖iteratedDeriv 1 (coprimeScaled ⌊Real.exp (L*u)⌋₊ g L u θ P) A‖ ≤ B := by
    simpa [B] using coprime_derivative_bound 1 P hP A g L u θ C U K hL hθ hA hu hK hbound
  have h2 : ‖iteratedDeriv 2 (coprimeScaled ⌊Real.exp (L*u)⌋₊ g L u θ P) A‖ ≤ 2*B := by
    simpa [B] using coprime_derivative_bound 2 P hP A g L u θ C U K hL hθ hA hu hK hbound
  have hB : 0 ≤ B := (norm_nonneg _).trans h0
  have hV : 0 ≤ V := (abs_nonneg _).trans ht
  have ht' : ‖((Real.log g/L:ℝ):ℂ)‖ ≤ V := by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using ht
  have hm : ‖(ArithmeticFunction.moebius g:ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_intCast] using
      (show |(ArithmeticFunction.moebius g:ℝ)| ≤ 1 by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=g))
  rw [logBlock_derivatives _ _ _ _ _ _ _ hg,norm_mul]
  apply (mul_le_mul_of_nonneg_right hm (norm_nonneg _)).trans
  rw [one_mul]
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_sub_le _ _) le_rfl).trans
  rw [norm_mul,norm_pow,norm_mul,norm_mul]
  have ha := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) ht' 2) h0 (norm_nonneg _) (sq_nonneg V)
  have hb := mul_le_mul (mul_le_mul_of_nonneg_left ht' (by norm_num : (0:ℝ)≤2)) h1
    (norm_nonneg _) (by positivity : 0≤2*V)
  rw [show ‖(2:ℂ)‖ = (2:ℝ) by norm_num]
  change _ ≤ (V^2+2*V+2)*B
  nlinarith

/-- No fixed-g hypothesis: log(g)/L may range over a whole bounded interval. -/
theorem logBlock_euler_bound (P : Polynomial ℂ) (hP : P.eval 0 = 0)
    (θ C U V : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hU : 0 ≤ U) (hV : 0 ≤ V) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (L : ℝ), 0 < L → ∀ (g : ℕ), g ≠ 0 →
      |Real.log g/L| ≤ V → ∀ u ∈ Set.Icc 0 U, ∀ A : ℂ, ‖A‖ ≤ C →
        ‖logBlock ⌊Real.exp (L*u)⌋₊ g L u θ P A‖ ≤ D*SupportTail.eulerMass g 0 := by
  obtain ⟨K,hK,hbound⟩ := absoluteError_bounded
  let D := (V^2+2*V+2)*coprimeCap P θ (C+1) U K
  have hcap : 0 ≤ coprimeCap P θ (C+1) U K :=
    mul_nonneg (Real.exp_pos _).le (scaledCap_nonneg P θ (C+1) U K hθ (by linarith) hU hK)
  have hD : 0 ≤ D := mul_nonneg (by positivity) hcap
  refine ⟨D,hD,?_⟩
  intro L hL g hg ht u hu A hA
  have hh := logBlock_bound P hP A g L u θ C U V K hg hL hθ hA hu ht hK hbound
  rw [← mul_assoc] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (EulerHead.mass_le _ g hg) hD)

/-- Both reflected regions use one constant, including the cutoff endpoint. -/
theorem logBlock_twoBidiscs (P : Polynomial ℂ) (hP : P.eval 0 = 0)
    (θ U V : ℝ) (hθ : 0 < θ) (hU : 0 ≤ U) (hV : 0 ≤ V) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (L : ℝ), 0 < L → ∀ (g : ℕ), g ≠ 0 →
      |Real.log g/L| ≤ V → ∀ u ∈ Set.Icc 0 U, ∀ p ∈ ElementaryGcd.twoBidiscs,
        ‖logBlock ⌊Real.exp (L*u)⌋₊ g L u θ P p.1‖ ≤ D*SupportTail.eulerMass g 0 ∧
        ‖logBlock ⌊Real.exp (L*u)⌋₊ g L u θ P p.2‖ ≤ D*SupportTail.eulerMass g 0 := by
  obtain ⟨D,hD,h⟩ := logBlock_euler_bound P hP θ (5*PRZZAsymptotic.R/4) U V hθ
    (by have := PRZZAsymptotic.radius_pos; positivity) hU hV
  refine ⟨D,hD,?_⟩
  intro L hL g hg ht u hu p hp
  have hs := ShiftedMobius.twoBidiscs_norm p hp
  exact ⟨h L hL g hg ht u hu p.1 hs.1,h L hL g hg ht u hu p.2 hs.2⟩

#print axioms coprime_derivative_bound
#print axioms logBlock_bound
#print axioms logBlock_euler_bound
#print axioms logBlock_twoBidiscs
end XiPrime8845.FengLogBounds
