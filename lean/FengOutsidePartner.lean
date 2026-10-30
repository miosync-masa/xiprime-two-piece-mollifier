import FengLogProducts

/-! Outside replacement against any Euler-dominated partner. The difference
vanishes when mu(g)=0; no squarefree restriction is imposed on the partner.
The limiting integrals of the resulting proxies are separate obligations. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Finset Filter Topology
namespace XiPrime8845.FengOutsidePartner
open FengAtG FengOutsideAverage FengLogProducts CoprimeEndpoint LogProfileSum
set_option maxHeartbeats 1000000

theorem outside_error_weight_factor (L u θ : ℝ) (g : ℕ) (G : Polynomial ℂ)
    (A B Y : ℂ) :
    FengMixedShift.rawWeight (A/L) (B/L) g * Y *
      (outsideBlock (cutoff L u) g L u θ G B-FengOutside.mainProxy (cutoff L u) g L u θ G B) =
    FengSharedLimit.zeroWeight g *
      (Y*(outsideBlock (cutoff L u) g L u θ G B-FengOutside.mainProxy (cutoff L u) g L u θ G B)) *
        BareEuler.ratio A B L g := by
  by_cases hm : (μ g:ℂ) = 0
  · rw [show FengOutside.mainProxy (cutoff L u) g L u θ G B = 0 by
      rw [cutoff,FengOutsidePrime.mainProxy_eq,hm]; ring]
    simp [outsideBlock,hm]
  · have he : FengMixedShift.rawWeight (A/L) (B/L) g =
        FengMixedShift.rawWeight 0 0 g * BareEuler.ratio A B L g := by
      apply mul_left_cancel₀ (pow_ne_zero 2 hm)
      convert BareEuler.weight_factor A B L g using 1
        <;> unfold FengMixedShift.rawWeight BareEuler.weight <;> ring
    rw [he,FengMixedShift.rawWeight_zero]
    ring

def partnerError (L θ : ℝ) (G : Polynomial ℂ) (A B : ℂ) (Y : ℕ → ℂ) : ℂ :=
  (∑ g ∈ Ioc 0 (cutoff L θ), FengMixedShift.rawWeight (A/L) (B/L) g*Y g*
    (outsideBlock (cutoff L (coordinate L θ g)) g L (coordinate L θ g) θ G B-
      FengOutside.mainProxy (cutoff L (coordinate L θ g)) g L (coordinate L θ g) θ G B))/(L:ℂ)

theorem partner_error_bound (L θ D : ℝ) (G : Polynomial ℂ) (A B : ℂ) (Y : ℕ → ℂ)
    (hL : 0 < L) (hD : 0 ≤ D)
    (hx : ∀ g ∈ Ioc 0 (cutoff L θ),
      ‖Y g‖ ≤ D*SupportTail.eulerMass g 0)
    (hr : ∀ g ∈ Ioc 0 (cutoff L θ), ‖BareEuler.ratio A B L g‖ ≤ 2) :
    ‖partnerError L θ G A B Y‖ ≤
      2*D*averageError L θ θ G B := by
  rw [partnerError,norm_div,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
  have hs : (∑ g ∈ Ioc 0 (cutoff L θ),
      ‖FengMixedShift.rawWeight (A/L) (B/L) g*Y g*
        (FengAtG.outsideBlock (cutoff L (coordinate L θ g)) g L (coordinate L θ g) θ G B-
        FengOutside.mainProxy (cutoff L (coordinate L θ g)) g L (coordinate L θ g) θ G B)‖) ≤
      2*D*∑ g ∈ Ioc 0 (cutoff L θ), (1/(g:ℝ))*SupportTail.eulerMass g 0*
        replacementError L (coordinate L θ g) θ g G B := by
    rw [mul_sum]
    apply sum_le_sum
    intro g hg
    rw [outside_error_weight_factor,norm_mul,norm_mul,norm_mul]
    have hE := euler_nonneg g (mem_Ioc.mp hg).1.ne'
    have h1 := mul_le_mul (hx g hg) (le_refl (replacementError L (coordinate L θ g) θ g G B))
      (norm_nonneg _) (mul_nonneg hD hE)
    have h2 := mul_le_mul (FengSharedLimit.zeroWeight_norm g (mem_Ioc.mp hg).1.ne') h1
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity : (0:ℝ)≤1/(g:ℝ))
    have h3 := mul_le_mul h2 (hr g hg) (norm_nonneg _)
      (by exact mul_nonneg (by positivity) (mul_nonneg (mul_nonneg hD hE) (norm_nonneg _)))
    simpa only [replacementError,mul_assoc,mul_left_comm,mul_comm] using h3
  have hh := div_le_div_of_nonneg_right ((norm_sum_le _ _).trans hs) hL.le
  have he : Ioc 0 (cutoff L θ) = Icc 1 (cutoff L θ) := by ext n; simp only [mem_Ioc,mem_Icc]; omega
  unfold averageError
  rw [he] at hh ⊢
  simpa only [mul_div_assoc,cutoff] using hh


/-- The partner can depend on L, both shifts and g. Only its Euler envelope
is used, and the bound is needed only eventually in L. -/
theorem partner_error_uniform (G : Polynomial ℂ) (hG : G.eval 0 = 0)
    (θ C D : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hCθ : C*θ ≤ 1) (hD : 0 ≤ D)
    (Y : ℝ → ℂ → ℂ → ℕ → ℂ)
    (hY : ∀ᶠ L : ℝ in atTop, ∀ A B : ℂ, ‖A‖ ≤ C → ‖B‖ ≤ C →
      ∀ g ∈ Ioc 0 (cutoff L θ), ‖Y L A B g‖ ≤ D*SupportTail.eulerMass g 0) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => partnerError L θ G p.1 p.2 (Y L p.1 p.2))
      (fun _ => 0) atTop {p | ‖p.1‖ ≤ C ∧ ‖p.2‖ ≤ C} := by
  have hh := averageError_uniform G hG θ C θ hθ hC hθ
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  have he : 0 < eps/(2*D+1) := by positivity
  filter_upwards [eventually_gt_atTop (0:ℝ),BareEulerUniform.ratio_uniform C θ hCθ 1 (by norm_num),
    Metric.tendstoUniformlyOn_iff.mp hh _ he,hY] with L hL hr hsmall hYL
  intro p hp
  have hr' : ∀ g ∈ Ioc 0 (cutoff L θ), ‖BareEuler.ratio p.1 p.2 L g‖ ≤ 2 := by
    intro g hg
    have h := hr g p.1 p.2 (mem_Ioc.mp hg).1.ne'
      ((Nat.le_floor_iff (Real.exp_pos _).le).mp (mem_Ioc.mp hg).2) hp.1 hp.2
    have ht := norm_add_le (BareEuler.ratio p.1 p.2 L g-1) (1:ℂ)
    rw [sub_add_cancel,norm_one] at ht
    linarith
  have hs := hsmall p.2 hp.2
  rw [dist_comm,Real.dist_eq,sub_zero,abs_of_nonneg (averageError_nonneg L θ θ G p.2 hL.le)] at hs
  rw [dist_comm,dist_eq_norm,sub_zero]
  apply (partner_error_bound L θ D G p.1 p.2 (Y L p.1 p.2) hL hD
    (hYL p.1 p.2 hp.1 hp.2) hr').trans_lt
  have ht := mul_le_mul_of_nonneg_left hs.le (show 0≤2*D by positivity)
  apply ht.trans_lt
  rw [← mul_div_assoc]
  exact (div_lt_iff₀ (by positivity : 0<2*D+1)).mpr (by nlinarith)

theorem product_sub_proxy_eq (X : Block) (L θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) :
    productSum X outsideBlock L θ P G A B-productSum X FengOutside.mainProxy L θ P G A B =
      partnerError L θ G A B
        (fun g => X (cutoff L (coordinate L θ g)) g L (coordinate L θ g) θ P A) := by
  unfold productSum partnerError
  rw [← sub_div,← sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intros
  dsimp [cutoff]
  ring

/-- A reusable block-level supplier, retaining the actual moving cutoff. -/
def EulerBound (X : Block) (P : Polynomial ℂ) (θ C : ℝ) : Prop :=
  ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ L : ℝ in atTop,
    ∀ A : ℂ, ‖A‖ ≤ C → ∀ g ∈ Ioc 0 (cutoff L θ),
      ‖X (cutoff L (coordinate L θ g)) g L (coordinate L θ g) θ P A‖ ≤
        D*SupportTail.eulerMass g 0

theorem block_sub_proxy_uniform (X : Block) (P G : Polynomial ℂ) (hG : G.eval 0 = 0)
    (θ C : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hCθ : C*θ ≤ 1)
    (hX : EulerBound X P θ C) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => productSum X outsideBlock L θ P G p.1 p.2-
        productSum X FengOutside.mainProxy L θ P G p.1 p.2)
      (fun _ => 0) atTop {p | ‖p.1‖ ≤ C ∧ ‖p.2‖ ≤ C} := by
  obtain ⟨D,hD,hX⟩ := hX
  have h := partner_error_uniform G hG θ C D hθ hC hCθ hD
    (fun L A _ g => X (cutoff L (coordinate L θ g)) g L (coordinate L θ g) θ P A)
    (by
      filter_upwards [hX] with L hXL
      intro A B hA hB
      exact hXL A hA)
  simpa only [product_sub_proxy_eq] using h

theorem outside_eulerBound (P : Polynomial ℂ) (hP : P.eval 0 = 0)
    (θ C : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) :
    EulerBound outsideBlock P θ C := by
  obtain ⟨D,hD,h⟩ := FengOutsideBounds.outsideBlock_euler_bound P hP θ C θ hθ hC hθ.le
  refine ⟨D,hD,?_⟩
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  intro A hA g hg
  have hg1 : (1:ℝ) ≤ g := by exact_mod_cast (mem_Ioc.mp hg).1
  have hgexp := (Nat.le_floor_iff (Real.exp_pos _).le).mp (mem_Ioc.mp hg).2
  exact h L hL g (mem_Ioc.mp hg).1.ne' _ (coordinate_mem L θ g hL ⟨hg1,hgexp⟩) A hA

theorem shared_eulerBound (P : Polynomial ℂ) (hP : P.eval 0 = 0)
    (θ C : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) :
    EulerBound sharedBlock P θ C := by
  obtain ⟨D,hD,h⟩ := FengSharedBounds.sharedBlock_euler_bound P hP θ C θ θ hθ hC hθ.le
  refine ⟨D,hD,?_⟩
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  intro A hA g hg
  have hg1 : (1:ℝ) ≤ g := by exact_mod_cast (mem_Ioc.mp hg).1
  have hgexp := (Nat.le_floor_iff (Real.exp_pos _).le).mp (mem_Ioc.mp hg).2
  have ht := ShiftWeights.normalized_log_mem (g:ℝ) L θ hg1 hL
    ((Real.log_le_iff_le_exp (by positivity)).mpr hgexp)
  exact h L hL g (mem_Ioc.mp hg).1.ne'
    (by rw [abs_of_nonneg ht.1]; exact ht.2) _
    (coordinate_mem L θ g hL ⟨hg1,hgexp⟩) A hA

#print axioms outside_error_weight_factor
#print axioms partner_error_bound
#print axioms partner_error_uniform
#print axioms block_sub_proxy_uniform
#print axioms outside_eulerBound
#print axioms shared_eulerBound

theorem proxy_eulerBound (P : Polynomial ℂ) (hP : P.eval 0 = 0)
    (θ C : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) :
    EulerBound FengOutside.mainProxy P θ C := by
  let D := FengInverseProfile.inverseCap P θ C θ+1
  have hD : 0 ≤ D := by
    dsimp [D]; have := FengInverseProfile.inverseCap_nonneg P θ C θ hθ hθ.le; positivity
  refine ⟨D,hD,?_⟩
  filter_upwards [eventually_gt_atTop (0:ℝ),
    (FengOutsidePrime.errorEnvelope_tendsto θ C θ P).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))]
    with L hL herr
  intro A hA g hg
  have hg0 : g ≠ 0 := (mem_Ioc.mp hg).1.ne'
  have hg1 : (1:ℝ) ≤ g := by exact_mod_cast (mem_Ioc.mp hg).1
  have hgexp := (Nat.le_floor_iff (Real.exp_pos _).le).mp (mem_Ioc.mp hg).2
  have hu := coordinate_mem L θ g hL ⟨hg1,hgexp⟩
  have hE := euler_nonneg g hg0
  have hi := FengInverseProfile.inverse_bound P A θ C θ _ hθ hA hu
  have he := FengOutsidePrime.restrictedTransform_bound L _ θ C θ g P hP A hL hθ hC hu hg0
    ((Real.log_le_iff_le_exp (by positivity)).mpr hgexp) hA
  have hb : ‖FengOutsidePrime.restrictedTransform L (coordinate L θ g) θ g P A‖ ≤ D := by
    have ht := norm_sub_le_norm_sub_add_norm_sub
      (FengOutsidePrime.restrictedTransform L (coordinate L θ g) θ g P A)
      (BetaKernel.D (-1) A θ (coordinate L θ g) P) 0
    rw [sub_zero,sub_zero] at ht
    dsimp [D]
    linarith
  rw [cutoff,FengOutsidePrime.mainProxy_eq,norm_mul,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hE]
  have hm := mul_le_mul_of_nonneg_right (FengMixedInterior.moebius_norm g) hE
  simp only [one_mul] at hm
  simpa only [mul_comm] using mul_le_mul hm hb (norm_nonneg _) hE

theorem block_sub_proxy_twoBidiscs (X : Block) (P G : Polynomial ℂ) (hG : G.eval 0 = 0)
    (hX : EulerBound X P PRZZAsymptotic.theta (5*PRZZAsymptotic.R/4)) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => productSum X outsideBlock L PRZZAsymptotic.theta P G p.1 p.2-
        productSum X FengOutside.mainProxy L PRZZAsymptotic.theta P G p.1 p.2)
      (fun _ => 0) atTop ElementaryGcd.twoBidiscs :=
  (block_sub_proxy_uniform X P G hG _ _ (by norm_num [PRZZAsymptotic.theta])
    (by have := PRZZAsymptotic.radius_pos; positivity) ShiftedEulerUniform.witness_size hX).mono
    (fun p hp => ShiftedMobius.twoBidiscs_norm p hp)

theorem shared_outside_sub_proxy (P G : Polynomial ℂ) (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => productSum sharedBlock outsideBlock L PRZZAsymptotic.theta P G p.1 p.2-
        productSum sharedBlock FengOutside.mainProxy L PRZZAsymptotic.theta P G p.1 p.2)
      (fun _ => 0) atTop ElementaryGcd.twoBidiscs :=
  block_sub_proxy_twoBidiscs sharedBlock P G hG (shared_eulerBound P hP _ _
    (by norm_num [PRZZAsymptotic.theta]) (by have := PRZZAsymptotic.radius_pos; positivity))

/-- Transposition acts on an arbitrary uniformly vanishing difference. -/
theorem error_transpose (f : ℝ → ℂ → ℂ → ℂ)
    (h : TendstoUniformlyOn (fun L (p : ℂ × ℂ) => f L p.1 p.2) (fun _ => 0)
      atTop ElementaryGcd.twoBidiscs) :
    TendstoUniformlyOn (fun L (p : ℂ × ℂ) => f L p.2 p.1) (fun _ => 0)
      atTop ElementaryGcd.twoBidiscs := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h eps heps] with L hL
  intro p hp
  apply hL (p.2,p.1)
  rcases hp with hp | hp
  · exact Or.inl ⟨hp.2,hp.1⟩
  · apply Or.inr
    rw [ElementaryGcd.reflectedBidisc_center] at hp ⊢
    exact ⟨hp.2,hp.1⟩

theorem outside_shared_sub_proxy (P G : Polynomial ℂ) (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => productSum outsideBlock sharedBlock L PRZZAsymptotic.theta P G p.1 p.2-
        productSum FengOutside.mainProxy sharedBlock L PRZZAsymptotic.theta P G p.1 p.2)
      (fun _ => 0) atTop ElementaryGcd.twoBidiscs := by
  have h := error_transpose (fun L A B =>
    productSum sharedBlock outsideBlock L PRZZAsymptotic.theta G P A B-
      productSum sharedBlock FengOutside.mainProxy L PRZZAsymptotic.theta G P A B)
    (shared_outside_sub_proxy G P hG hP)
  simpa only [productSum_swap sharedBlock outsideBlock,
    productSum_swap sharedBlock FengOutside.mainProxy] using h

/-- Both actual outside factors are replaced; the second replacement uses
the proxy itself as the Euler-dominated partner. -/
theorem outside_outside_sub_proxy (P G : Polynomial ℂ) (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => productSum outsideBlock outsideBlock L PRZZAsymptotic.theta P G p.1 p.2-
        productSum FengOutside.mainProxy FengOutside.mainProxy L PRZZAsymptotic.theta P G p.1 p.2)
      (fun _ => 0) atTop ElementaryGcd.twoBidiscs := by
  have hθ : 0 < PRZZAsymptotic.theta := by norm_num [PRZZAsymptotic.theta]
  have hC : 0 ≤ 5*PRZZAsymptotic.R/4 := by have := PRZZAsymptotic.radius_pos; positivity
  have h1 := block_sub_proxy_twoBidiscs outsideBlock P G hG (outside_eulerBound P hP _ _ hθ hC)
  have h2 := error_transpose (fun L A B =>
    productSum FengOutside.mainProxy outsideBlock L PRZZAsymptotic.theta G P A B-
      productSum FengOutside.mainProxy FengOutside.mainProxy L PRZZAsymptotic.theta G P A B)
    (block_sub_proxy_twoBidiscs FengOutside.mainProxy G P hP
    (proxy_eulerBound G hG _ _ hθ hC))
  have h2' : TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => productSum outsideBlock FengOutside.mainProxy L PRZZAsymptotic.theta P G p.1 p.2-
        productSum FengOutside.mainProxy FengOutside.mainProxy L PRZZAsymptotic.theta P G p.1 p.2)
      (fun _ => 0) atTop ElementaryGcd.twoBidiscs := by
    simpa only [productSum_swap FengOutside.mainProxy outsideBlock,
      productSum_swap FengOutside.mainProxy FengOutside.mainProxy] using h2
  simpa only [Pi.add_def,sub_add_sub_cancel,add_zero] using h1.add h2'

#print axioms product_sub_proxy_eq
#print axioms proxy_eulerBound
#print axioms block_sub_proxy_twoBidiscs
#print axioms shared_outside_sub_proxy
#print axioms error_transpose
#print axioms outside_shared_sub_proxy
#print axioms outside_outside_sub_proxy

end XiPrime8845.FengOutsidePartner

