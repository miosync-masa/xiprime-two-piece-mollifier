import FengInverseProfile
import CoprimeSingleGluing
import FengOutsideReplacement

/-! Literal outsideProxy to the zero-shift totient profile. Both inner errors
and the growing-g outer weight are estimated, not assumed to disappear. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Finset Filter Topology
namespace XiPrime8845.FengOutsideProxy
open FengCrossAssembly FengOutsidePrime FengInverseProfile CoprimeEndpoint LogProfileSum
open CoprimeApproximation CoprimeEulerCompletion CoprimeEulerError SupportTail
set_option maxHeartbeats 1000000

def zeroModel (L θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) : ℂ :=
  (∑ g ∈ Ioc 0 (cutoff L θ), BareEuler.weight (A/L) (B/L) g *
    zeroEulerMain g (coordinate L θ g) θ P A * (eulerMass g 0:ℂ)*
    BetaKernel.D (-1) B θ (coordinate L θ g) G)/(L:ℂ)

theorem proxy_eq (L θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) :
    outsideProxy L θ P G A B =
      (∑ g ∈ Ioc 0 (cutoff L θ), BareEuler.weight (A/L) (B/L) g *
        actual L g (coordinate L θ g) θ P A * (eulerMass g 0:ℂ)*
        restrictedTransform L (coordinate L θ g) θ g G B)/(L:ℂ) := by
  unfold outsideProxy
  congr 1
  apply sum_congr rfl
  intro g hg
  rw [mainProxy_eq]
  unfold FengMixedInterior.conrey BareEuler.weight FengMixedShift.rawWeight
  ring

theorem proxy_error_bound (L θ C D : ℝ) (P G : Polynomial ℂ) (hG : G.eval 0 = 0)
    (A B : ℂ) (hL : 0 < L) (hθ : 0 < θ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hB : ‖B‖ ≤ C)
    (hx : ∀ g ∈ Ioc 0 (cutoff L θ), ‖actual L g (coordinate L θ g) θ P A‖ ≤ D*eulerMass g 0)
    (hw : ∀ g ∈ Ioc 0 (cutoff L θ), ‖BareEuler.weight (A/L) (B/L) g‖ ≤ 2/(g:ℝ)) :
    ‖outsideProxy L θ P G A B-zeroModel L θ P G A B‖ ≤
      2*D*errorEnvelope L θ C θ G*(SupportTail.harmonic (cutoff L θ)/L)*(1+2*SupportProductTail.productConstant)+
      2*inverseCap G θ C θ*CoprimeSingleGluing.average L θ θ P A := by
  have henv : 0 ≤ errorEnvelope L θ C θ G := by
    have hh := restrictedTransform_bound L 0 θ C θ 1 G hG B hL hθ hC
      ⟨le_rfl,hθ.le⟩ (by norm_num) (by simp; positivity) hB
    exact (norm_nonneg _).trans hh
  have hi := inverseCap_nonneg G θ C θ hθ hθ.le
  rw [proxy_eq,zeroModel,← sub_div,← sum_sub_distrib,norm_div,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
  have hs : (∑ g ∈ Ioc 0 (cutoff L θ),
      ‖BareEuler.weight (A/L) (B/L) g*actual L g (coordinate L θ g) θ P A*(eulerMass g 0:ℂ)*
        restrictedTransform L (coordinate L θ g) θ g G B-
       BareEuler.weight (A/L) (B/L) g*zeroEulerMain g (coordinate L θ g) θ P A*(eulerMass g 0:ℂ)*
        BetaKernel.D (-1) B θ (coordinate L θ g) G‖) ≤
      2*D*errorEnvelope L θ C θ G * ∑ g ∈ Ioc 0 (cutoff L θ), (1/(g:ℝ))*eulerMass g 0^2 +
      2*inverseCap G θ C θ * ∑ g ∈ Ioc 0 (cutoff L θ),
        (1/(g:ℝ))*innerError L g (coordinate L θ g) θ P A*eulerMass g 0 := by
    rw [mul_sum,mul_sum,← sum_add_distrib]
    apply sum_le_sum
    intro g hg
    have hg0 := (mem_Ioc.mp hg).1.ne'
    have hE := euler_nonneg g hg0
    have hgexp := (Nat.le_floor_iff (Real.exp_pos _).le).mp (mem_Ioc.mp hg).2
    have hu := coordinate_mem L θ g hL ⟨by exact_mod_cast (mem_Ioc.mp hg).1,hgexp⟩
    have hb := restrictedTransform_bound L _ θ C θ g G hG B hL hθ hC hu hg0
      ((Real.log_le_iff_le_exp (by exact_mod_cast Nat.pos_of_ne_zero hg0)).mpr hgexp) hB
    have hmain := inverse_bound G B θ C θ _ hθ hB hu
    have heq : BareEuler.weight (A/L) (B/L) g*actual L g (coordinate L θ g) θ P A*(eulerMass g 0:ℂ)*
        restrictedTransform L (coordinate L θ g) θ g G B-
       BareEuler.weight (A/L) (B/L) g*zeroEulerMain g (coordinate L θ g) θ P A*(eulerMass g 0:ℂ)*
        BetaKernel.D (-1) B θ (coordinate L θ g) G =
      BareEuler.weight (A/L) (B/L) g*(eulerMass g 0:ℂ)*
        (actual L g (coordinate L θ g) θ P A*
          (restrictedTransform L (coordinate L θ g) θ g G B-BetaKernel.D (-1) B θ (coordinate L θ g) G)+
         (actual L g (coordinate L θ g) θ P A-zeroEulerMain g (coordinate L θ g) θ P A)*
          BetaKernel.D (-1) B θ (coordinate L θ g) G) := by ring
    rw [heq,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hE]
    have hin : ‖actual L g (coordinate L θ g) θ P A*
          (restrictedTransform L (coordinate L θ g) θ g G B-BetaKernel.D (-1) B θ (coordinate L θ g) G)+
         (actual L g (coordinate L θ g) θ P A-zeroEulerMain g (coordinate L θ g) θ P A)*
          BetaKernel.D (-1) B θ (coordinate L θ g) G‖ ≤
        D*eulerMass g 0*errorEnvelope L θ C θ G+
          innerError L g (coordinate L θ g) θ P A*inverseCap G θ C θ := by
      apply (norm_add_le _ _).trans
      rw [norm_mul,norm_mul]
      exact add_le_add (mul_le_mul (hx g hg) hb (norm_nonneg _) (mul_nonneg hD hE))
        (mul_le_mul_of_nonneg_left hmain (norm_nonneg _))
    have hh := mul_le_mul (mul_le_mul_of_nonneg_right (hw g hg) hE) hin
      (norm_nonneg _) (mul_nonneg (by positivity) hE)
    convert hh using 1
    ring
  have hav := mul_le_mul_of_nonneg_left (FengSharedInterior.euler_square_average (cutoff L θ))
    (show 0 ≤ 2*D*errorEnvelope L θ C θ G by positivity)
  have hh := div_le_div_of_nonneg_right ((norm_sum_le _ _).trans
    (hs.trans (add_le_add hav le_rfl))) hL.le
  apply hh.trans_eq
  unfold CoprimeSingleGluing.average
  ring

theorem proxy_sub_zero_uniform (P G : Polynomial ℂ) (hP : P.eval 0 = 0) (hG : G.eval 0 = 0)
    (θ C : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hsize : C*θ ≤ 1) :
    TendstoUniformlyOn (fun L (p : ℂ × ℂ) => outsideProxy L θ P G p.1 p.2-zeroModel L θ P G p.1 p.2)
      (fun _ => 0) atTop {p | ‖p.1‖ ≤ C ∧ ‖p.2‖ ≤ C} := by
  obtain ⟨D,hD,hbound⟩ := FengSharedInterior.actual_coprime_bound P hP θ C θ hθ hC hθ.le
  let V := inverseCap G θ C θ
  have hV : 0 ≤ V := inverseCap_nonneg G θ C θ hθ hθ.le
  have hlim : Tendsto (fun L : ℝ => 2*D*errorEnvelope L θ C θ G*(SupportTail.harmonic (cutoff L θ)/L)*
      (1+2*SupportProductTail.productConstant)) atTop (nhds 0) := by
    simpa using (((errorEnvelope_tendsto θ C θ G).const_mul (2*D)).mul
      (harmonic_normalized θ hθ.le)).mul_const (1+2*SupportProductTail.productConstant)
  have hin := CoprimeSingleGluing.average_uniform P hP θ C θ hθ hC hθ
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  have heta : 0 < eps/(4*V+2) := by positivity
  filter_upwards [eventually_gt_atTop (0:ℝ),BareEulerUniform.weight_bound_eventually C θ hsize,
    hlim.eventually (gt_mem_nhds (show (0:ℝ)<eps/2 by positivity)),
    Metric.tendstoUniformlyOn_iff.mp hin _ heta] with L hL hw he hi
  intro p hp
  have hinner := hi p.1 hp.1
  rw [dist_comm,Real.dist_eq,sub_zero,
    abs_of_nonneg (CoprimeSingleGluing.average_nonneg L θ θ P p.1 hL.le)] at hinner
  have hm : 2*V*CoprimeSingleGluing.average L θ θ P p.1 < eps/2 := by
    have hh := (lt_div_iff₀ (show 0<4*V+2 by positivity)).mp hinner
    nlinarith [CoprimeSingleGluing.average_nonneg L θ θ P p.1 hL.le]
  rw [dist_comm,dist_eq_norm,sub_zero]
  apply (proxy_error_bound L θ C D P G hG p.1 p.2 hL hθ hC hD hp.2
    (fun g hg => hbound L hL g (mem_Ioc.mp hg).1.ne' _
      (coordinate_mem L θ g hL ⟨by exact_mod_cast (mem_Ioc.mp hg).1,
        (Nat.le_floor_iff (Real.exp_pos _).le).mp (mem_Ioc.mp hg).2⟩) p.1 hp.1)
    (fun g hg => hw g p.1 p.2 (mem_Ioc.mp hg).1.ne'
      ((Nat.le_floor_iff (Real.exp_pos _).le).mp (mem_Ioc.mp hg).2) hp.1 hp.2)).trans_lt
  linarith

theorem zeroModel_factor (L θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) :
    zeroModel L θ P G A B =
      (∑ g ∈ Ioc 0 (cutoff L θ), ShiftedTotient.outerWeight 0 0 g * BareEuler.ratio A B L g *
        profile θ P G A B (coordinate L θ g))/(L:ℂ) := by
  unfold zeroModel
  congr 1
  apply sum_congr rfl
  intro g hg
  rw [zeroEulerMain_eq,← ShiftedTotient.euler_zero]
  calc
    _ = (BareEuler.weight (A/L) (B/L) g*ShiftedTotient.euler 0 g*ShiftedTotient.euler 0 g)*
        profile θ P G A B (coordinate L θ g) := by unfold profile; ring
    _ = _ := by rw [BareEulerUniform.zeroEuler_weight_factor]

theorem zeroModel_error (L θ C eta : ℝ) (P G : Polynomial ℂ) (A B : ℂ)
    (hL : 0 < L) (hθ : 0 < θ) (heta : 0 ≤ eta) (hA : ‖A‖ ≤ C) (hB : ‖B‖ ≤ C)
    (hr : ∀ g ∈ Ioc 0 (cutoff L θ), ‖BareEuler.ratio A B L g-1‖ ≤ eta) :
    ‖zeroModel L θ P G A B-zeroSum L θ (profile θ P G A B)‖ ≤
      (TotientHarmonic.summatory (Real.exp (L*θ))/L)*eta*valueCap P G θ C θ := by
  rw [zeroModel_factor,zeroSum,TotientAbel.testedSum,← sub_div]
  change ‖((∑ g ∈ Ioc 0 (cutoff L θ), ShiftedTotient.outerWeight 0 0 g*BareEuler.ratio A B L g*
      profile θ P G A B (coordinate L θ g))-
    ∑ g ∈ Ioc 0 (cutoff L θ), profile θ P G A B (coordinate L θ g)*(TotientConvolution.weight g:ℂ))/(L:ℂ)‖ ≤ _
  rw [← sum_sub_distrib,norm_div,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
  have hsum : (∑ g ∈ Ioc 0 (cutoff L θ),
      ‖ShiftedTotient.outerWeight 0 0 g*BareEuler.ratio A B L g*profile θ P G A B (coordinate L θ g)-
        profile θ P G A B (coordinate L θ g)*(TotientConvolution.weight g:ℂ)‖) ≤
      TotientHarmonic.summatory (Real.exp (L*θ))*eta*valueCap P G θ C θ := by
    unfold TotientHarmonic.summatory
    rw [sum_mul,sum_mul]
    apply sum_le_sum
    intro g hg
    have hg0 := (mem_Ioc.mp hg).1.ne'
    rw [ShiftedTotient.outerWeight_zero g hg0]
    have he : (TotientConvolution.weight g:ℂ) = (((μ g:ℝ)^2/g.totient:ℝ):ℂ) := rfl
    rw [he,show (((μ g:ℝ)^2/g.totient:ℝ):ℂ)*BareEuler.ratio A B L g*profile θ P G A B (coordinate L θ g)-
        profile θ P G A B (coordinate L θ g)*(((μ g:ℝ)^2/g.totient:ℝ):ℂ) =
        (((μ g:ℝ)^2/g.totient:ℝ):ℂ)*(BareEuler.ratio A B L g-1)*profile θ P G A B (coordinate L θ g) by ring,
      norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hr g hg) (by positivity))
      (profile_bound θ C θ _ P G A B hθ hA hB
        (coordinate_mem L θ g hL ⟨by exact_mod_cast (mem_Ioc.mp hg).1,
          (Nat.le_floor_iff (Real.exp_pos _).le).mp (mem_Ioc.mp hg).2⟩))
      (norm_nonneg _) (by positivity)
  have hh := div_le_div_of_nonneg_right ((norm_sum_le _ _).trans hsum) hL.le
  apply hh.trans_eq
  ring

theorem zeroModel_sub_profile_uniform (P G : Polynomial ℂ) (θ C : ℝ)
    (hθ : 0 < θ) (hC : 0 ≤ C) (hsize : C*θ ≤ 1) :
    TendstoUniformlyOn (fun L (p : ℂ × ℂ) => zeroModel L θ P G p.1 p.2-
      zeroSum L θ (profile θ P G p.1 p.2)) (fun _ => 0) atTop
      {p | ‖p.1‖ ≤ C ∧ ‖p.2‖ ≤ C} := by
  let V := valueCap P G θ C θ
  have hV : 0 ≤ V := mul_nonneg (WeightDerivatives.firstCap_nonneg _ _ _ _ hθ hC hθ.le)
    (inverseCap_nonneg G θ C θ hθ hθ.le)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  let eta := eps/(2*((θ+1)*V+1))
  have heta : 0 < eta := by dsimp [eta]; positivity
  filter_upwards [eventually_gt_atTop (0:ℝ),
    Metric.tendstoUniformlyOn_iff.mp TotientHarmonic.normalized_uniform 1 (by norm_num),
    BareEulerUniform.ratio_uniform C θ hsize eta heta] with L hL ht hr
  intro p hp
  have hmass : TotientHarmonic.summatory (Real.exp (L*θ))/L ≤ θ+1 := by
    have hh := ht θ hθ.le
    rw [dist_comm,Real.dist_eq] at hh
    linarith [le_abs_self (TotientHarmonic.summatory (Real.exp (L*θ))/L-θ)]
  have hb := zeroModel_error L θ C eta P G p.1 p.2 hL hθ heta.le hp.1 hp.2
    (fun g hg => (hr g p.1 p.2 (mem_Ioc.mp hg).1.ne'
      ((Nat.le_floor_iff (Real.exp_pos _).le).mp (mem_Ioc.mp hg).2) hp.1 hp.2).le)
  have hc := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmass heta.le) hV
  have he : eta*((θ+1)*V+1) = eps/2 := by dsimp [eta]; field_simp
  rw [dist_comm,dist_eq_norm,sub_zero]
  exact hb.trans_lt (by nlinarith [hc])

#print axioms proxy_eq
#print axioms proxy_error_bound
#print axioms proxy_sub_zero_uniform
#print axioms zeroModel_factor
#print axioms zeroModel_error
#print axioms zeroModel_sub_profile_uniform
end XiPrime8845.FengOutsideProxy
