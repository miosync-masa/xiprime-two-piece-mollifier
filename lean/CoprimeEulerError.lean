import CoprimeEulerCompletion
import FengSharedInterior

/-! Single-inner errors with the extra Euler mass needed for outer products.
The cutoff array and the harmonic cutoff are arbitrary; u=0 is excluded only
in the convergence theorem, not in the coarse bound. -/
noncomputable section
open scoped BigOperators
open Finset Filter Topology
namespace XiPrime8845.CoprimeEulerError
open CoprimeApproximation CoprimeEulerCompletion SupportTail SupportProductTail
open ShiftedEndpoint ShiftedMobius WeightDerivatives CoprimeHead OuterProfile
set_option maxHeartbeats 1000000

theorem supported_euler_bound (N : ℕ) (s : Finset ℕ) (b : ℕ → ℝ) (B : ℝ)
    (hs : ∀ r ∈ s, r ≠ 0) (hb : RootBound s b B) :
    (∑ g ∈ Icc 1 N, (1/(g:ℝ))*supportedSum g s b*eulerMass g 0) ≤
      SupportTail.harmonic N*(B*productConstant) := by
  have ht : Tendsto (fun K : ℕ => ∑ g ∈ Icc 1 N,
      (1/(g:ℝ))*supportedSum g s b*EulerHead.mass K g) atTop
      (nhds (∑ g ∈ Icc 1 N, (1/(g:ℝ))*supportedSum g s b*eulerMass g 0)) := by
    apply tendsto_finsetSum
    intro g hg
    exact (EulerHead.mass_tendsto g (by have := (mem_Icc.mp hg).1; omega)).const_mul _
  apply le_of_tendsto ht
  filter_upwards [] with K
  have hc := reciprocal_rootBound (Icc 1 K) 1 (by norm_num)
    (fun r hr => by have := (mem_Icc.mp hr).1; omega)
  simpa only [one_div, mul_one_div, mul_one, EulerHead.mass] using
    supported_product_bound N s (Icc 1 K) b (fun r => 1/(r:ℝ)) B 1 hb.1 hc.1 hs
      (fun r hr => by have := (mem_Icc.mp hr).1; omega)
      (fun r hr => (hb.2 r hr).1) (by intros; positivity)
      (fun r hr => (hb.2 r hr).2) (fun r hr => by simpa using (hc.2 r hr).2)

theorem head_completion (Q g : ℕ) (hg : g ≠ 0) (u θ C U : ℝ)
    (P : Polynomial ℂ) (A : ℂ) (hθ : 0 < θ) (hA : ‖A‖ ≤ C)
    (hu : u ∈ Set.Icc 0 U) :
    ‖headMain Q g u θ P A-zeroEulerMain g u θ P A‖ ≤
      firstCap P θ C U*(eulerMass g 0-EulerHead.mass Q g) := by
  rw [headMain_factor,zeroEulerMain]
  change ‖mainTerm u θ P A*(EulerHead.mass Q g:ℂ)-
    (eulerMass g 0:ℂ)*mainTerm u θ P A‖ ≤ _
  rw [show mainTerm u θ P A*(EulerHead.mass Q g:ℂ)-
      (eulerMass g 0:ℂ)*mainTerm u θ P A =
      mainTerm u θ P A*((EulerHead.mass Q g-eulerMass g 0:ℝ):ℂ) by push_cast; ring,
    norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr (EulerHead.mass_le Q g hg))]
  simpa only [neg_sub] using mul_le_mul_of_nonneg_right
    (mainTerm_bound P A u θ C U hθ hA hu) (sub_nonneg.mpr (EulerHead.mass_le Q g hg))

def innerError (L : ℝ) (g : ℕ) (u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) : ℝ :=
  ‖actual L g u θ P A-zeroEulerMain g u θ P A‖

theorem innerError_bound (P : Polynomial ℂ) (hP : P.eval 0 = 0)
    (θ C U : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hU : 0 ≤ U) :
    ∃ D ≥ 0, ∀ L > 0, ∀ g : ℕ, g ≠ 0 → ∀ u ∈ Set.Icc 0 U,
      ∀ A : ℂ, ‖A‖ ≤ C → innerError L g u θ P A ≤ D*eulerMass g 0 := by
  obtain ⟨D,hD,h⟩ := FengSharedInterior.actual_coprime_bound P hP θ C U hθ hC hU
  refine ⟨D+firstCap P θ C U,add_nonneg hD (firstCap_nonneg _ _ _ _ hθ hC hU),?_⟩
  intro L hL g hg u hu A hA
  have he := CoprimeEndpoint.euler_nonneg g hg
  have hz : ‖zeroEulerMain g u θ P A‖ ≤ firstCap P θ C U*eulerMass g 0 := by
    rw [zeroEulerMain,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg he]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (mainTerm_bound P A u θ C U hθ hA hu) he
  exact (norm_sub_le _ _).trans (by nlinarith [h L hL g hg u hu A hA,hz])

/-- Uniform in N and in every interior cutoff array, with an Euler factor
already included. No pointwise uniform convergence in g is claimed. -/
theorem innerError_average (P : Polynomial ℂ) (hP : P.eval 0 = 0)
    (θ C u₀ U : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hu₀ : 0 < u₀) (hU : 0 < U) :
    ∀ eta > 0, ∀ᶠ L : ℝ in atTop, ∀ (N : ℕ) (u : ℕ → ℝ) (A : ℂ),
      ‖A‖ ≤ C → (∀ g ∈ Icc 1 N, u g ∈ Set.Icc u₀ U) →
      (∑ g ∈ Icc 1 N, (1/(g:ℝ))*innerError L g (u g) θ P A*eulerMass g 0) ≤
        SupportTail.harmonic N*eta := by
  obtain ⟨K,hK,hbound⟩ := absoluteError_bounded
  let B := coprimeCap P θ C U K
  let F := firstCap P θ C U
  have hB : 0 ≤ B := mul_nonneg (Real.exp_pos _).le
    (scaledCap_nonneg P θ C U K hθ hC hU.le hK)
  have hF : 0 ≤ F := firstCap_nonneg _ _ _ _ hθ hC hU.le
  let rate := fun q : ℝ => (1/q+(B+F)*q^(-1/4:ℝ))*productConstant
  have hi : Tendsto (fun q : ℝ => 1/q) atTop (nhds 0) := by
    simpa only [one_div] using (tendsto_inv_atTop_zero (𝕜:=ℝ))
  have hp : Tendsto (fun q : ℝ => q^(-1/4:ℝ)) atTop (nhds 0) := by
    simpa only [neg_div] using tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/4)
  have hr : Tendsto rate atTop (nhds 0) := by
    simpa [rate] using (hi.add (hp.const_mul (B+F))).mul_const productConstant
  intro eta heta
  obtain ⟨Q,hQ,hsmall⟩ := ((eventually_gt_atTop (0:ℕ)).and
    ((hr.comp tendsto_natCast_atTop_atTop).eventually (gt_mem_nhds heta))).exists
  have hQr : (0:ℝ)<Q := by exact_mod_cast hQ
  filter_upwards [head_approximation_envelope P hP θ C u₀ U K hθ hC hu₀ hU
    hK hbound Q (1/(Q:ℝ)) (by positivity)] with L hL
  intro N u A hA hu
  let s := Icc 1 ⌊Real.exp (L*U)⌋₊
  let b := errorCoeff (1/(Q:ℝ)) B Q
  have hs : ∀ r ∈ s, r ≠ 0 := by intro r hr; have := (mem_Icc.mp hr).1; omega
  have hb := errorCoeff_rootBound s (1/(Q:ℝ)) B Q (by positivity) hB hQ hs
  have hhead := supported_euler_bound N s b _ hs hb
  have htail := mul_le_mul_of_nonneg_left (EulerHead.full_tail_product N Q hQ) hF
  have hsum : (∑ g ∈ Icc 1 N, (1/(g:ℝ))*innerError L g (u g) θ P A*eulerMass g 0) ≤
      (∑ g ∈ Icc 1 N, (1/(g:ℝ))*supportedSum g s b*eulerMass g 0)+
      F*∑ g ∈ Icc 1 N, (1/(g:ℝ))*(eulerMass g 0-EulerHead.mass Q g)*eulerMass g 0 := by
    rw [mul_sum,← sum_add_distrib]
    apply sum_le_sum
    intro g hg
    have hg0 : g ≠ 0 := by have := (mem_Icc.mp hg).1; omega
    have he := CoprimeEndpoint.euler_nonneg g hg0
    have hpoint := (norm_sub_le_norm_sub_add_norm_sub
      (actual L g (u g) θ P A) (headMain Q g (u g) θ P A) _).trans
      (add_le_add (hL g A hA (u g) (hu g hg))
        (head_completion Q g hg0 (u g) θ C U P A hθ hA
          ⟨hu₀.le.trans (hu g hg).1,(hu g hg).2⟩))
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpoint (by positivity : (0:ℝ)≤1/(g:ℝ))) he
    convert hh using 1
    dsimp only [innerError,b,s,F,B]
    ring
  have hh : (∑ g ∈ Icc 1 N, (1/(g:ℝ))*innerError L g (u g) θ P A*eulerMass g 0) ≤
      SupportTail.harmonic N*rate Q := by
    dsimp only [rate]
    nlinarith [hhead,htail]
  exact hh.trans (mul_le_mul_of_nonneg_left hsmall.le (by unfold SupportTail.harmonic; positivity))

#print axioms supported_euler_bound
#print axioms head_completion
#print axioms innerError_bound
#print axioms innerError_average
end XiPrime8845.CoprimeEulerError
