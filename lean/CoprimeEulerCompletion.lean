import EulerHead
import OuterProfile
import CoprimeApproximation

/-! Complete the coprime finite-head model to the zero-shift Euler mass,
with product-safe averaged errors. Shifted Euler replacement is separate. -/
noncomputable section
open scoped BigOperators
open Finset Filter Topology
namespace XiPrime8845.CoprimeEulerCompletion
open ShiftedMobius WeightDerivatives ShiftedEndpoint CoprimeHead
open CoprimeApproximation SupportTail SupportProductTail OuterProfile
set_option maxHeartbeats 1000000

def zeroEulerMain (g : ℕ) (u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) : ℂ :=
  (eulerMass g 0:ℂ)*mainTerm u θ P A

theorem zeroEulerMain_eq (g : ℕ) (u θ : ℝ) (P : Polynomial ℂ) (A : ℂ) :
    zeroEulerMain g u θ P A = ShiftedTotient.euler 0 g*mainTerm u θ P A := by
  rw [ShiftedTotient.euler_zero]
  rfl

theorem head_product_completion (N Q : ℕ) (hQ : 0 < Q) (P G : Polynomial ℂ)
    (θ C U : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hU : 0 ≤ U)
    (A B : ℂ) (hA : ‖A‖ ≤ C) (hB : ‖B‖ ≤ C) (u v : ℕ → ℝ)
    (hu : ∀ g ∈ Icc 1 N, u g ∈ Set.Icc 0 U)
    (hv : ∀ g ∈ Icc 1 N, v g ∈ Set.Icc 0 U) :
    (∑ g ∈ Icc 1 N, (1/(g:ℝ))*
      ‖headMain Q g (u g) θ P A*headMain Q g (v g) θ G B -
        zeroEulerMain g (u g) θ P A*zeroEulerMain g (v g) θ G B‖) ≤
      SupportTail.harmonic N*(2*valueCap P G θ C U*(Q:ℝ)^(-1/4:ℝ)*productConstant) := by
  have hcap : 0 ≤ valueCap P G θ C U :=
    mul_nonneg (firstCap_nonneg _ _ _ _ hθ hC hU) (firstCap_nonneg _ _ _ _ hθ hC hU)
  have hpoint (g : ℕ) (hg : g ∈ Icc 1 N) :
      ‖headMain Q g (u g) θ P A*headMain Q g (v g) θ G B -
        zeroEulerMain g (u g) θ P A*zeroEulerMain g (v g) θ G B‖ ≤
        2*valueCap P G θ C U*(eulerMass g 0-EulerHead.mass Q g)*eulerMass g 0 := by
    have hg0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hg).1)
    have hm := EulerHead.mass_nonneg Q g
    have hme := EulerHead.mass_le Q g hg0
    have he0 : 0 ≤ eulerMass g 0 := hm.trans hme
    have hprod : ‖mainTerm (u g) θ P A*mainTerm (v g) θ G B‖ ≤ valueCap P G θ C U := by
      rw [norm_mul]
      exact mul_le_mul (mainTerm_bound P A _ θ C U hθ hA (hu g hg))
        (mainTerm_bound G B _ θ C U hθ hB (hv g hg)) (norm_nonneg _)
        (firstCap_nonneg _ _ _ _ hθ hC hU)
    rw [headMain_factor, headMain_factor]
    change ‖(mainTerm (u g) θ P A*(EulerHead.mass Q g:ℂ))*
      (mainTerm (v g) θ G B*(EulerHead.mass Q g:ℂ)) -
      ((eulerMass g 0:ℂ)*mainTerm (u g) θ P A)*
      ((eulerMass g 0:ℂ)*mainTerm (v g) θ G B)‖ ≤ _
    have hid : (mainTerm (u g) θ P A*(EulerHead.mass Q g:ℂ))*
        (mainTerm (v g) θ G B*(EulerHead.mass Q g:ℂ)) -
        ((eulerMass g 0:ℂ)*mainTerm (u g) θ P A)*
        ((eulerMass g 0:ℂ)*mainTerm (v g) θ G B) =
        ((EulerHead.mass Q g^2-eulerMass g 0^2:ℝ):ℂ)*
          (mainTerm (u g) θ P A*mainTerm (v g) θ G B) := by push_cast; ring
    rw [hid, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by nlinarith : EulerHead.mass Q g^2-eulerMass g 0^2 ≤ 0)]
    have hb := mul_le_mul_of_nonneg_left hprod
      (show 0 ≤ -(EulerHead.mass Q g^2-eulerMass g 0^2) by nlinarith)
    have ht : eulerMass g 0^2-EulerHead.mass Q g^2 ≤
        2*(eulerMass g 0-EulerHead.mass Q g)*eulerMass g 0 := by nlinarith [sq_nonneg (eulerMass g 0-EulerHead.mass Q g)]
    have hh := mul_le_mul_of_nonneg_left ht hcap
    nlinarith
  calc
    _ ≤ ∑ g ∈ Icc 1 N, (1/(g:ℝ))*(2*valueCap P G θ C U*
        (eulerMass g 0-EulerHead.mass Q g)*eulerMass g 0) :=
      sum_le_sum (fun g hg => mul_le_mul_of_nonneg_left (hpoint g hg) (by positivity))
    _ = (2*valueCap P G θ C U)*∑ g ∈ Icc 1 N,
        (1/(g:ℝ))*(eulerMass g 0-EulerHead.mass Q g)*eulerMass g 0 := by
      rw [Finset.mul_sum]; apply sum_congr rfl; intros; ring
    _ ≤ (2*valueCap P G θ C U)*(SupportTail.harmonic N*((Q:ℝ)^(-1/4:ℝ)*productConstant)) :=
      mul_le_mul_of_nonneg_left (EulerHead.full_tail_product N Q hQ) (by positivity)
    _ = _ := by ring

/-- Actual arithmetic inner products, with every finite-head error discharged.
The full mass here is E_0(g); no assertion E_(A/L)=E_0 is made. -/
theorem actual_product_completion (P G : Polynomial ℂ)
    (hP : P.eval 0 = 0) (hG : G.eval 0 = 0)
    (θ C u₀ U K : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hu₀ : 0 < u₀) (hU : 0 < U)
    (hK : 0 ≤ K) (hbound : ∀ t : ℝ, 0 ≤ t → WeightedMobius.absoluteError t ≤ K)
    (Q : ℕ) (hQ : 0 < Q) (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ L : ℝ in atTop, ∀ (N : ℕ) (u v : ℕ → ℝ) (A B : ℂ),
      ‖A‖ ≤ C → ‖B‖ ≤ C →
      (∀ g ∈ Icc 1 N, u g ∈ Set.Icc u₀ U) →
      (∀ g ∈ Icc 1 N, v g ∈ Set.Icc u₀ U) →
      (∑ g ∈ Icc 1 N, (1/(g:ℝ))*
        ‖actual L g (u g) θ P A*actual L g (v g) θ G B-
          zeroEulerMain g (u g) θ P A*zeroEulerMain g (v g) θ G B‖) ≤
        SupportTail.harmonic N*((((eps+coprimeCap P θ C U K*(Q:ℝ)^(-1/4:ℝ))*coprimeCap G θ C U K+
          firstCap P θ C U*(eps+coprimeCap G θ C U K*(Q:ℝ)^(-1/4:ℝ)))+
          2*valueCap P G θ C U*(Q:ℝ)^(-1/4:ℝ))*productConstant) := by
  filter_upwards [coprime_product_error_eventually P G hP hG θ C u₀ U K
    hθ hC hu₀ hU hK hbound Q hQ eps heps] with L hL
  intro N u v A B hA hB hu hv
  have hh := head_product_completion N Q hQ P G θ C U hθ hC hU.le A B hA hB u v
    (fun g hg => ⟨hu₀.le.trans (hu g hg).1,(hu g hg).2⟩)
    (fun g hg => ⟨hu₀.le.trans (hv g hg).1,(hv g hg).2⟩)
  have ha := hL N u v A B hA hB hu hv
  have ht : (∑ g ∈ Icc 1 N, (1/(g:ℝ))*
      ‖actual L g (u g) θ P A*actual L g (v g) θ G B-
        zeroEulerMain g (u g) θ P A*zeroEulerMain g (v g) θ G B‖) ≤
      (∑ g ∈ Icc 1 N, (1/(g:ℝ))*
        ‖actual L g (u g) θ P A*actual L g (v g) θ G B-
          headMain Q g (u g) θ P A*headMain Q g (v g) θ G B‖)+
      ∑ g ∈ Icc 1 N, (1/(g:ℝ))*
        ‖headMain Q g (u g) θ P A*headMain Q g (v g) θ G B-
          zeroEulerMain g (u g) θ P A*zeroEulerMain g (v g) θ G B‖ := by
    rw [← Finset.sum_add_distrib]
    apply sum_le_sum
    intro g hg
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (norm_sub_le_norm_sub_add_norm_sub _ _ _) (by positivity)
  nlinarith

/-- Uniform normalized g-average for the actual coprime products. N may grow
arbitrarily with L; the two cutoff arrays remain in the stated interior. -/
theorem actual_product_average_uniform (P G : Polynomial ℂ)
    (hP : P.eval 0 = 0) (hG : G.eval 0 = 0)
    (θ C u₀ U : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hu₀ : 0 < u₀) (hU : 0 < U) :
    ∀ eta > 0, ∀ᶠ L : ℝ in atTop, ∀ (N : ℕ) (u v : ℕ → ℝ) (A B : ℂ),
      ‖A‖ ≤ C → ‖B‖ ≤ C →
      (∀ g ∈ Icc 1 N, u g ∈ Set.Icc u₀ U) →
      (∀ g ∈ Icc 1 N, v g ∈ Set.Icc u₀ U) →
      (∑ g ∈ Icc 1 N, (1/(g:ℝ))*
        ‖actual L g (u g) θ P A*actual L g (v g) θ G B-
          zeroEulerMain g (u g) θ P A*zeroEulerMain g (v g) θ G B‖)/SupportTail.harmonic N < eta := by
  obtain ⟨K,hK,hbound⟩ := absoluteError_bounded
  let CP := coprimeCap P θ C U K
  let CG := coprimeCap G θ C U K
  let FP := firstCap P θ C U
  let M := valueCap P G θ C U
  let rate := fun q : ℝ => (((1/q+CP*q^(-1/4:ℝ))*CG+
    FP*(1/q+CG*q^(-1/4:ℝ)))+2*M*q^(-1/4:ℝ))*productConstant
  have hi : Tendsto (fun q : ℝ => 1/q) atTop (nhds 0) := by
    simpa only [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun q : ℝ => q⁻¹) atTop (nhds 0))
  have hp : Tendsto (fun q : ℝ => q^(-1/4:ℝ)) atTop (nhds 0) := by
    simpa only [neg_div] using tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/4)
  have hr : Tendsto rate atTop (nhds 0) := by
    simpa only [rate,mul_zero,zero_mul,add_zero] using
      ((((hi.add (hp.const_mul CP)).mul_const CG).add
        ((hi.add (hp.const_mul CG)).const_mul FP)).add (hp.const_mul (2*M))).mul_const productConstant
  intro eta heta
  obtain ⟨X,hX⟩ := Metric.tendsto_atTop.mp hr eta heta
  obtain ⟨Q,hQ⟩ := exists_nat_gt (max X 0)
  have hQ0 : (0:ℝ) < Q := (le_max_right X 0).trans_lt hQ
  have hQr : rate Q < eta := by
    have h := hX Q ((le_max_left X 0).trans hQ.le)
    rw [Real.dist_eq,sub_zero] at h
    exact (le_abs_self _).trans_lt h
  filter_upwards [actual_product_completion P G hP hG θ C u₀ U K hθ hC hu₀ hU
    hK hbound Q (by exact_mod_cast hQ0) (1/(Q:ℝ)) (by positivity)] with L hL
  intro N u v A B hA hB hu hv
  have h := hL N u v A B hA hB hu hv
  change _ ≤ SupportTail.harmonic N*rate Q at h
  by_cases hH : SupportTail.harmonic N = 0
  · simp only [hH,div_zero]; exact heta
  have hH0 : 0 < SupportTail.harmonic N := lt_of_le_of_ne
    (by unfold SupportTail.harmonic; positivity) (Ne.symm hH)
  exact ((div_le_iff₀ hH0).mpr (by simpa only [mul_comm] using h)).trans_lt hQr

#print axioms actual_product_average_uniform
#print axioms head_product_completion
#print axioms actual_product_completion
end XiPrime8845.CoprimeEulerCompletion
