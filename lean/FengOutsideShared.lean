import FengOutsideSquare

/-! Actual proxy/shared products converge through the signed marked measure.
The shared prime moment is retained. Euler bounds control errors only; they
do not replace the signed arithmetic measure or assert a shared/shared limit. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Finset Filter Topology
namespace XiPrime8845.FengOutsideShared
open FengAtG FengLogProducts FengOutsidePrime FengInverseProfile CoprimeEndpoint LogProfileSum
open FengSharedLimit (zeroWeight zeroWeight_norm)
open FengSharedTail CoprimeEulerError
set_option maxHeartbeats 1000000

theorem raw_moebius_factor (L : ℝ) (g : ℕ) (A B X : ℂ) :
    FengMixedShift.rawWeight (A/L) (B/L) g * (μ g:ℂ) * X =
      zeroWeight g * (μ g:ℂ) * X * BareEuler.ratio A B L g := by
  by_cases hm : (μ g:ℂ) = 0
  · simp [hm]
  · have he : FengMixedShift.rawWeight (A/L) (B/L) g =
        FengMixedShift.rawWeight 0 0 g * BareEuler.ratio A B L g := by
      apply mul_left_cancel₀ (pow_ne_zero 2 hm)
      convert BareEuler.weight_factor A B L g using 1 <;>
        unfold FengMixedShift.rawWeight BareEuler.weight <;> ring
    rw [he,FengMixedShift.rawWeight_zero]
    ring

def mainSum (L θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) : ℂ :=
  (∑ g ∈ Ioc 0 (cutoff L θ), zeroWeight g * (μ g:ℂ) *
    (SupportTail.eulerMass g 0:ℂ) * BetaKernel.D (-1) A θ (coordinate L θ g) P *
    FengSharedInterior.main L g (coordinate L θ g) θ G B)/(L:ℂ)

/-- The signed weight is mu(g) times primeMoment(g) divided by phi(g).
The two profiles and their shifts are transposed together. -/
theorem mainSum_eq (L θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) :
    mainSum L θ P G A B = FengMixedAbel.profileSum L θ
      (FengInverseProfile.profile θ G P B A) := by
  rw [mainSum,FengMixedAbel.profileSum_eq,sum_div,sum_div]
  apply sum_congr rfl
  intro g hg
  have hg0 : g ≠ 0 := (mem_Ioc.mp hg).1.ne'
  have hgc : (g:ℂ) ≠ 0 := by exact_mod_cast hg0
  have htc : (g.totient:ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_eq_zero.not.mpr hg0)
  simp only [zeroWeight,FengSharedInterior.main,CoprimeEulerCompletion.zeroEulerMain,
    FengMarkedProfile.mark_eq_moment,TotientWeight.eulerMass_zero g hg0,
    FengInverseProfile.profile]
  push_cast
  by_cases hL : (L:ℂ) = 0
  · simp [hL]
  · field_simp

/-- Single shared-block replacement, including the moving cutoff endpoint. -/
theorem shared_error_bound (G : Polynomial ℂ) (hG : G.eval 0 = 0)
    (θ C : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ L : ℝ, 0 < L → ∀ g : ℕ, g ≠ 0 →
      |Real.log g/L| ≤ θ → ∀ u ∈ Set.Icc 0 θ, ∀ B : ℂ, ‖B‖ ≤ C →
      ‖sharedBlock ⌊Real.exp (L*u)⌋₊ g L u θ G B-FengSharedInterior.main L g u θ G B‖ ≤
        (D/L)*SupportTail.eulerMass g 0+θ^2*innerError L g u θ G B := by
  obtain ⟨D,hD,h⟩ := shared_head_error G hG θ C θ θ hθ hC hθ.le hθ.le
  refine ⟨D,hD,?_⟩
  intro L hL g hg ht u hu B hB
  apply (norm_sub_le_norm_sub_add_norm_sub _ (mark g L*CoprimeApproximation.actual L g u θ G B) _).trans
  apply add_le_add (h L hL g hg ht u hu B hB)
  rw [FengSharedInterior.main,← mul_sub,norm_mul]
  exact mul_le_mul_of_nonneg_right (mark_bound g hg L θ hL ht) (norm_nonneg _)

/-- A scalar envelope for a ratio, an inverse-profile error, and the shared error. -/
theorem product_error (r t i s m : ℂ) (E e V S M d k z : ℝ)
    (hE : 0 ≤ E) (he : 0 ≤ e) (hV : 0 ≤ V) (_hS : 0 ≤ S)
    (hr : ‖r‖ ≤ 2) (hr1 : ‖r-1‖ ≤ e) (ht : ‖t-i‖ ≤ e) (hi : ‖i‖ ≤ V)
    (hs : ‖s‖ ≤ S*E) (hm : ‖m‖ ≤ M*E) (hsm : ‖s-m‖ ≤ d*E+k*z) :
    E*‖r*t*s-i*m‖ ≤ (2*e*S+2*V*d+e*V*M)*E^2+(2*V*k)*(z*E) := by
  have hts : ‖t*s-i*m‖ ≤ e*(S*E)+V*(d*E+k*z) := by
    rw [show t*s-i*m=(t-i)*s+i*(s-m) by ring]
    apply (norm_add_le _ _).trans
    rw [norm_mul,norm_mul]
    exact add_le_add (mul_le_mul ht hs (norm_nonneg _) he)
      (mul_le_mul hi hsm (norm_nonneg _) hV)
  have hmain : ‖i*m‖ ≤ V*(M*E) := by
    rw [norm_mul]; exact mul_le_mul hi hm (norm_nonneg _) hV
  have hb : ‖r*t*s-i*m‖ ≤ 2*(e*(S*E)+V*(d*E+k*z))+e*(V*(M*E)) := by
    rw [show r*t*s-i*m=r*(t*s-i*m)+(r-1)*(i*m) by ring]
    apply (norm_add_le _ _).trans
    rw [norm_mul,norm_mul]
    exact add_le_add (mul_le_mul hr hts (norm_nonneg _) (by norm_num))
      (mul_le_mul hr1 hmain (norm_nonneg _) he)
  exact (mul_le_mul_of_nonneg_left hb hE).trans_eq (by ring)

/-- Summing error envelopes uses positive Euler square mass, never positivity
of the signed marked main measure. -/
theorem average_bound (L θ d k : ℝ) (G : Polynomial ℂ) (B : ℂ) (X : ℕ → ℂ)
    (hL : 0 < L) (hd : 0 ≤ d)
    (hX : ∀ g ∈ Ioc 0 (cutoff L θ), ‖X g‖ ≤
      (1/(g:ℝ))*(d*SupportTail.eulerMass g 0^2+
        k*(innerError L g (coordinate L θ g) θ G B*SupportTail.eulerMass g 0))) :
    ‖(∑ g ∈ Ioc 0 (cutoff L θ), X g)/(L:ℂ)‖ ≤
      d*(SupportTail.harmonic (cutoff L θ)/L)*(1+2*SupportProductTail.productConstant)+
        k*CoprimeSingleGluing.average L θ θ G B := by
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
  have hb := (norm_sum_le _ _).trans (sum_le_sum hX)
  apply (div_le_div_of_nonneg_right hb hL.le).trans
  have he : (∑ g ∈ Ioc 0 (cutoff L θ), (1/(g:ℝ))*
      (d*SupportTail.eulerMass g 0^2+k*(innerError L g (coordinate L θ g) θ G B*SupportTail.eulerMass g 0))) =
      d*(∑ g ∈ Ioc 0 (cutoff L θ), (1/(g:ℝ))*SupportTail.eulerMass g 0^2)+
      k*(∑ g ∈ Ioc 0 (cutoff L θ), (1/(g:ℝ))*innerError L g (coordinate L θ g) θ G B*SupportTail.eulerMass g 0) := by
    rw [mul_sum,mul_sum,← sum_add_distrib]
    apply sum_congr rfl; intros; ring
  rw [he,add_div]
  apply add_le_add _ (by unfold CoprimeSingleGluing.average; exact le_of_eq (by ring))
  exact (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (FengSharedInterior.euler_square_average _) hd) hL.le).trans_eq (by ring)


theorem proxy_sub_profile_uniform (P G : Polynomial ℂ)
    (hP : P.eval 0 = 0) (hG : G.eval 0 = 0)
    (θ C : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hsize : C*θ ≤ 1) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => productSum FengOutside.mainProxy sharedBlock L θ P G p.1 p.2-
        FengMixedAbel.profileSum L θ (FengInverseProfile.profile θ G P p.2 p.1))
      (fun _ => 0) atTop {p | ‖p.1‖ ≤ C ∧ ‖p.2‖ ≤ C} := by
  obtain ⟨S,hS,hshared⟩ := FengSharedBounds.sharedBlock_euler_bound G hG θ C θ θ hθ hC hθ.le
  obtain ⟨D,hD,herror⟩ := shared_error_bound G hG θ C hθ hC
  let V := inverseCap P θ C θ
  let M := θ^2*WeightDerivatives.firstCap G θ C θ
  let K := 2*S+2*V+V*M
  let k := 2*V*θ^2
  let F := 1+2*SupportProductTail.productConstant
  have hV : 0 ≤ V := inverseCap_nonneg P θ C θ hθ hθ.le
  have hM : 0 ≤ M := mul_nonneg (sq_nonneg θ)
    (WeightDerivatives.firstCap_nonneg G θ C θ hθ hC hθ.le)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hF : 0 ≤ F := by dsimp [F,SupportProductTail.productConstant]; positivity
  have hd : Tendsto (fun L : ℝ => D/L) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using tendsto_inv_atTop_zero.const_mul D
  have hi := CoprimeSingleGluing.average_uniform G hG θ C θ hθ hC hθ
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  let Z := K*(θ+1)*F+k+1
  have hZ : 0 < Z := by dsimp [Z]; positivity
  let e := min 1 (eps/(2*Z))
  have he : 0 < e := lt_min (by norm_num) (by positivity)
  have he1 : e ≤ 1 := min_le_left _ _
  have heZ : e*Z ≤ eps/2 := by
    have hh := mul_le_mul_of_nonneg_right (min_le_right 1 (eps/(2*Z))) hZ.le
    exact hh.trans_eq (by field_simp)
  filter_upwards [eventually_gt_atTop (0:ℝ),
    (harmonic_normalized θ hθ.le).eventually (gt_mem_nhds (show θ < θ+1 by linarith)),
    BareEulerUniform.ratio_uniform C θ hsize e he,
    (errorEnvelope_tendsto θ C θ P).eventually (gt_mem_nhds he),
    hd.eventually (gt_mem_nhds he),
    Metric.tendstoUniformlyOn_iff.mp hi e he] with L hL hmass hr hEP hDL hinner
  intro p hp
  have hav : CoprimeSingleGluing.average L θ θ G p.2 < e := by
    have hh := hinner p.2 hp.2
    rw [dist_comm,Real.dist_eq,sub_zero] at hh
    exact (le_abs_self _).trans_lt hh
  let X := fun g => FengMixedShift.rawWeight (p.1/L) (p.2/L) g*
    FengOutside.mainProxy ⌊Real.exp (L*coordinate L θ g)⌋₊ g L (coordinate L θ g) θ P p.1*
    sharedBlock ⌊Real.exp (L*coordinate L θ g)⌋₊ g L (coordinate L θ g) θ G p.2-
    zeroWeight g*(μ g:ℂ)*(SupportTail.eulerMass g 0:ℂ)*
      BetaKernel.D (-1) p.1 θ (coordinate L θ g) P*
      FengSharedInterior.main L g (coordinate L θ g) θ G p.2
  have hb := average_bound L θ (e*K) k G p.2 X hL (mul_nonneg he.le hK) (by
    intro g hg
    have hg0 := (mem_Ioc.mp hg).1.ne'
    have hg1 : (1:ℝ) ≤ g := by exact_mod_cast (mem_Ioc.mp hg).1
    have hgexp := (Nat.le_floor_iff (Real.exp_pos _).le).mp (mem_Ioc.mp hg).2
    have hglog := (Real.log_le_iff_le_exp (by positivity : (0:ℝ)<g)).mpr hgexp
    have hu := coordinate_mem L θ g hL ⟨hg1,hgexp⟩
    have ht := ShiftWeights.normalized_log_mem (g:ℝ) L θ hg1 hL hglog
    have ht' : |Real.log g/L| ≤ θ := by rw [abs_of_nonneg ht.1]; exact ht.2
    have hE := euler_nonneg g hg0
    have hr1 := (hr g p.1 p.2 hg0 hgexp hp.1 hp.2).le
    have hr2 : ‖BareEuler.ratio p.1 p.2 L g‖ ≤ 2 := by
      have hh := norm_add_le (BareEuler.ratio p.1 p.2 L g-1) (1:ℂ)
      rw [sub_add_cancel,norm_one] at hh
      linarith
    have hm : ‖FengSharedInterior.main L g (coordinate L θ g) θ G p.2‖ ≤ M*SupportTail.eulerMass g 0 := by
      rw [FengSharedInterior.main,CoprimeEulerCompletion.zeroEulerMain,norm_mul,norm_mul,
        Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hE]
      have hm := mul_le_mul (mark_bound g hg0 L θ hL ht')
        (mul_le_mul_of_nonneg_left (ShiftedEndpoint.mainTerm_bound G p.2 _ θ C θ hθ hp.2 hu) hE)
        (mul_nonneg hE (norm_nonneg _)) (sq_nonneg θ)
      exact hm.trans_eq (by dsimp [M]; ring)
    have hs := (herror L hL g hg0 ht' _ hu p.2 hp.2).trans
      (add_le_add (mul_le_mul_of_nonneg_right hDL.le hE) le_rfl)
    have hpnt := product_error (BareEuler.ratio p.1 p.2 L g)
      (restrictedTransform L (coordinate L θ g) θ g P p.1)
      (BetaKernel.D (-1) p.1 θ (coordinate L θ g) P)
      (sharedBlock ⌊Real.exp (L*coordinate L θ g)⌋₊ g L (coordinate L θ g) θ G p.2)
      (FengSharedInterior.main L g (coordinate L θ g) θ G p.2)
      (SupportTail.eulerMass g 0) e V S M e (θ^2) (innerError L g (coordinate L θ g) θ G p.2)
      hE he.le hV hS hr2 hr1
      ((restrictedTransform_bound L _ θ C θ g P hP p.1 hL hθ hC hu hg0 hglog hp.1).trans hEP.le)
      (inverse_bound P p.1 θ C θ _ hθ hp.1 hu)
      (hshared L hL g hg0 ht' _ hu p.2 hp.2) hm hs
    have hx : X g = zeroWeight g*(μ g:ℂ)*(SupportTail.eulerMass g 0:ℂ)*
        (BareEuler.ratio p.1 p.2 L g*restrictedTransform L (coordinate L θ g) θ g P p.1*
          sharedBlock ⌊Real.exp (L*coordinate L θ g)⌋₊ g L (coordinate L θ g) θ G p.2-
          BetaKernel.D (-1) p.1 θ (coordinate L θ g) P*
            FengSharedInterior.main L g (coordinate L θ g) θ G p.2) := by
      dsimp [X]
      rw [mainProxy_eq]
      have hh := raw_moebius_factor L g p.1 p.2
        ((SupportTail.eulerMass g 0:ℂ)*restrictedTransform L (coordinate L θ g) θ g P p.1*
          sharedBlock ⌊Real.exp (L*coordinate L θ g)⌋₊ g L (coordinate L θ g) θ G p.2)
      linear_combination hh
    rw [hx,norm_mul,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hE]
    have hc : ‖zeroWeight g‖*‖(μ g:ℂ)‖ ≤ 1/(g:ℝ) := by
      simpa only [mul_one] using mul_le_mul (zeroWeight_norm g hg0)
        (FengMixedInterior.moebius_norm g) (norm_nonneg _) (by positivity : (0:ℝ)≤1/(g:ℝ))
    have heq : 2*e*S+2*V*e+e*V*M = e*K := by dsimp only [K]; ring
    rw [heq] at hpnt
    have hh := mul_le_mul hc hpnt (mul_nonneg hE (norm_nonneg _)) (by positivity : (0:ℝ)≤1/(g:ℝ))
    simpa only [k,mul_assoc] using hh)
  rw [dist_comm,dist_eq_norm,sub_zero,← mainSum_eq,productSum,mainSum,← sub_div,← sum_sub_distrib]
  change ‖(∑ g ∈ Ioc 0 (cutoff L θ), X g)/(L:ℂ)‖ < eps
  apply hb.trans_lt
  have h1 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmass.le (mul_nonneg he.le hK)) hF
  have h2 := mul_le_mul_of_nonneg_left hav.le hk
  have hh : (e*K)*(SupportTail.harmonic (cutoff L θ)/L)*F+
      k*CoprimeSingleGluing.average L θ θ G p.2 ≤ e*Z := by
    dsimp [Z]
    nlinarith
  exact hh.trans_lt (heZ.trans_lt (by linarith))

theorem proxy_sub_profile_twoBidiscs (P G : Polynomial ℂ)
    (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => productSum FengOutside.mainProxy sharedBlock L PRZZAsymptotic.theta P G p.1 p.2-
        FengMixedAbel.profileSum L PRZZAsymptotic.theta
          (FengInverseProfile.profile PRZZAsymptotic.theta G P p.2 p.1))
      (fun _ => 0) atTop ElementaryGcd.twoBidiscs :=
  (proxy_sub_profile_uniform P G hP hG PRZZAsymptotic.theta (5*PRZZAsymptotic.R/4)
    (by norm_num [PRZZAsymptotic.theta]) (by have := PRZZAsymptotic.radius_pos; positivity)
    ShiftedEulerUniform.witness_size).mono (fun p hp => ShiftedMobius.twoBidiscs_norm p hp)

theorem proxy_shared_twoBidiscs (P G : Polynomial ℂ) (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => productSum FengOutside.mainProxy sharedBlock L PRZZAsymptotic.theta P G p.1 p.2)
      (fun p => -BetaKernel.monomialIntegral p.1 p.2 PRZZAsymptotic.theta P G (-1) 1 3)
      atTop ElementaryGcd.twoBidiscs := by
  simpa only [Pi.add_def,sub_add_cancel,zero_add] using
    (proxy_sub_profile_twoBidiscs P G hP hG).add (FengInverseProducts.inverse_mixed_twoBidiscs P G)

theorem outside_shared_twoBidiscs (P G : Polynomial ℂ) (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => productSum outsideBlock sharedBlock L PRZZAsymptotic.theta P G p.1 p.2)
      (fun p => -BetaKernel.monomialIntegral p.1 p.2 PRZZAsymptotic.theta P G (-1) 1 3)
      atTop ElementaryGcd.twoBidiscs := by
  simpa only [Pi.add_def,sub_add_cancel,zero_add] using
    (FengOutsidePartner.outside_shared_sub_proxy P G hP hG).add (proxy_shared_twoBidiscs P G hP hG)

theorem shared_outside_twoBidiscs (P G : Polynomial ℂ) (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => productSum sharedBlock outsideBlock L PRZZAsymptotic.theta P G p.1 p.2)
      (fun p => -BetaKernel.monomialIntegral p.1 p.2 PRZZAsymptotic.theta P G 1 (-1) 3)
      atTop ElementaryGcd.twoBidiscs := by
  have h := uniform_transpose outsideBlock sharedBlock P G
    (fun A B => -BetaKernel.monomialIntegral A B PRZZAsymptotic.theta G P (-1) 1 3)
    (outside_shared_twoBidiscs G P hG hP)
  simpa only [BetaKernel.monomialIntegral_swap _ _ _ G P] using h

theorem outside_shared_reflected (P G : Polynomial ℂ) (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => productSum outsideBlock sharedBlock L PRZZAsymptotic.theta P G (-p.2) (-p.1))
      (fun p => -BetaKernel.monomialIntegral (-p.2) (-p.1) PRZZAsymptotic.theta P G (-1) 1 3)
      atTop PRZZAsymptotic.witnessBidisc :=
  ElementaryGcd.uniform_reflected (outside_shared_twoBidiscs P G hP hG)

theorem shared_outside_reflected (P G : Polynomial ℂ) (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => productSum sharedBlock outsideBlock L PRZZAsymptotic.theta P G (-p.2) (-p.1))
      (fun p => -BetaKernel.monomialIntegral (-p.2) (-p.1) PRZZAsymptotic.theta P G 1 (-1) 3)
      atTop PRZZAsymptotic.witnessBidisc :=
  ElementaryGcd.uniform_reflected (shared_outside_twoBidiscs P G hP hG)

#print axioms raw_moebius_factor
#print axioms mainSum_eq
#print axioms shared_error_bound
#print axioms product_error
#print axioms average_bound
#print axioms proxy_sub_profile_uniform
#print axioms proxy_sub_profile_twoBidiscs
#print axioms proxy_shared_twoBidiscs
#print axioms outside_shared_twoBidiscs
#print axioms shared_outside_twoBidiscs
#print axioms outside_shared_reflected
#print axioms shared_outside_reflected


end XiPrime8845.FengOutsideShared
