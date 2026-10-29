import FengMixedProduct
import BareEulerUniform

/-! Shift-dependent outer weights for the actual Conrey/shared product.
The raw weight contains no mu^2. The ratio identity below is for a product
containing the Conrey mu(g) factor, not for arbitrary shared/shared products.
This proves one component, not the full K20 or K02 asymptotic. -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Finset Filter Topology
namespace XiPrime8845.FengMixedShift
open FengAtG FengMixedInterior LogProfileSum CoprimeEndpoint
open FengSharedLimit (zeroWeight zeroWeight_norm)
set_option maxHeartbeats 1000000

def rawWeight (a b : ℂ) (g : ℕ) : ℂ :=
  ElementaryGcd.generalizedTotient (1+a+b) g / (g:ℂ)^(2+a+b)

theorem rawWeight_zero (g : ℕ) : rawWeight 0 0 g = zeroWeight g := by
  simp [rawWeight,zeroWeight,ShiftedTotient.generalizedTotient_one,Complex.cpow_ofNat]

/-- Exact transfer after multiplying by the actual Conrey factor. At a
non-squarefree g that factor vanishes; the shared factor is never altered. -/
theorem mixed_weight_factor (L u θ : ℝ) (g : ℕ) (P : Polynomial ℂ) (A B Y : ℂ) :
    rawWeight (A/L) (B/L) g * conrey L g u θ P A * Y =
      zeroWeight g * (conrey L g u θ P A * Y) * BareEuler.ratio A B L g := by
  by_cases hm : (μ g:ℂ) = 0
  · simp [conrey,hm]
  · have he : rawWeight (A/L) (B/L) g = rawWeight 0 0 g * BareEuler.ratio A B L g := by
      apply mul_left_cancel₀ (pow_ne_zero 2 hm)
      convert BareEuler.weight_factor A B L g using 1 <;> unfold rawWeight BareEuler.weight <;> ring
    rw [he,rawWeight_zero]
    ring

def actualSum (L U θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) : ℂ :=
  (∑ g ∈ Ioc 0 (cutoff L U), rawWeight (A/L) (B/L) g *
    conrey L g (coordinate L U g) θ P A *
    sharedBlock ⌊Real.exp (L*coordinate L U g)⌋₊ g L (coordinate L U g) θ G B)/(L:ℂ)

theorem mixed_euler_bound (P G : Polynomial ℂ) (hP : P.eval 0 = 0) (hG : G.eval 0 = 0)
    (θ C U : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hU : 0 ≤ U) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ L : ℝ, 0 < L → ∀ g ∈ Ioc 0 (cutoff L U),
      ∀ A B : ℂ, ‖A‖ ≤ C → ‖B‖ ≤ C →
      ‖conrey L g (coordinate L U g) θ P A *
        sharedBlock ⌊Real.exp (L*coordinate L U g)⌋₊ g L (coordinate L U g) θ G B‖ ≤
        D*SupportTail.eulerMass g 0^2 := by
  obtain ⟨BP,hBP,hp⟩ := FengSharedInterior.actual_coprime_bound P hP θ C U hθ hC hU
  obtain ⟨BG,hBG,hg⟩ := FengSharedBounds.sharedBlock_euler_bound G hG θ C U U hθ hC hU
  refine ⟨BP*BG,mul_nonneg hBP hBG,?_⟩
  intro L hL g hmem A B hA hB
  have hg0 : g ≠ 0 := (mem_Ioc.mp hmem).1.ne'
  have hg1 : (1:ℝ) ≤ g := by exact_mod_cast (mem_Ioc.mp hmem).1
  have hgexp : (g:ℝ) ≤ Real.exp (L*U) :=
    (Nat.le_floor_iff (Real.exp_pos _).le).mp (mem_Ioc.mp hmem).2
  have hu := coordinate_mem L U g hL ⟨hg1,hgexp⟩
  have ht := ShiftWeights.normalized_log_mem (g:ℝ) L U hg1 hL
    ((Real.log_le_iff_le_exp (by positivity)).mpr hgexp)
  have hx : ‖conrey L g (coordinate L U g) θ P A‖ ≤ BP*SupportTail.eulerMass g 0 := by
    rw [conrey,norm_mul]
    simpa only [one_mul] using mul_le_mul (moebius_norm g)
      (hp L hL g hg0 _ hu A hA) (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  have hy := hg L hL g hg0 (by rw [abs_of_nonneg ht.1]; exact ht.2) _ hu B hB
  rw [norm_mul]
  have hh := mul_le_mul hx hy (norm_nonneg _)
    ((norm_nonneg _).trans hx)
  calc
    _ ≤ (BP*SupportTail.eulerMass g 0)*(BG*SupportTail.eulerMass g 0) := hh
    _ = _ := by ring

/-- Endpoint-safe quantitative shift replacement with an explicit ratio bound. -/
theorem shift_error_bound (L U θ D η : ℝ) (P G : Polynomial ℂ) (A B : ℂ)
    (hL : 0 < L) (hD : 0 ≤ D) (hη : 0 ≤ η)
    (hprod : ∀ g ∈ Ioc 0 (cutoff L U),
      ‖conrey L g (coordinate L U g) θ P A *
        sharedBlock ⌊Real.exp (L*coordinate L U g)⌋₊ g L (coordinate L U g) θ G B‖ ≤
        D*SupportTail.eulerMass g 0^2)
    (hratio : ∀ g ∈ Ioc 0 (cutoff L U), ‖BareEuler.ratio A B L g-1‖ ≤ η) :
    ‖actualSum L U θ P G A B-FengMixedProduct.actualSum L U θ P G A B‖ ≤
      η*D*(SupportTail.harmonic (cutoff L U)/L)*(1+2*SupportProductTail.productConstant) := by
  rw [actualSum,FengMixedProduct.actualSum,← sub_div,← sum_sub_distrib,norm_div,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
  have hb : (∑ g ∈ Ioc 0 (cutoff L U), ‖rawWeight (A/L) (B/L) g *
      conrey L g (coordinate L U g) θ P A *
      sharedBlock ⌊Real.exp (L*coordinate L U g)⌋₊ g L (coordinate L U g) θ G B -
      zeroWeight g * conrey L g (coordinate L U g) θ P A *
      sharedBlock ⌊Real.exp (L*coordinate L U g)⌋₊ g L (coordinate L U g) θ G B‖) ≤
      η*D*∑ g ∈ Ioc 0 (cutoff L U), (1/(g:ℝ))*SupportTail.eulerMass g 0^2 := by
    rw [mul_sum]
    apply sum_le_sum
    intro g hg
    have hid (x y z r : ℂ) : x*(y*z)*r-x*y*z = (x*(y*z))*(r-1) := by ring
    rw [mixed_weight_factor,hid,norm_mul,norm_mul]
    have hx := mul_le_mul (zeroWeight_norm g (mem_Ioc.mp hg).1.ne') (hprod g hg)
      (norm_nonneg _) (by positivity : (0:ℝ) ≤ 1/(g:ℝ))
    have hy := mul_le_mul hx (hratio g hg) (norm_nonneg _) (by positivity)
    convert hy using 1; ring
  have hh := mul_le_mul_of_nonneg_left (FengSharedInterior.euler_square_average (cutoff L U))
    (mul_nonneg hη hD)
  apply (div_le_div_of_nonneg_right ((norm_sum_le _ _).trans (hb.trans hh)) hL.le).trans_eq
  ring

theorem shift_error_uniform (P G : Polynomial ℂ) (hP : P.eval 0 = 0) (hG : G.eval 0 = 0)
    (θ C U : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hU : 0 < U) (hCU : C*U ≤ 1) :
    TendstoUniformlyOn (fun L (p : ℂ × ℂ) => actualSum L U θ P G p.1 p.2 -
      FengMixedProduct.actualSum L U θ P G p.1 p.2) (fun _ => 0)
      atTop {p | ‖p.1‖ ≤ C ∧ ‖p.2‖ ≤ C} := by
  obtain ⟨D,hD,hprod⟩ := mixed_euler_bound P G hP hG θ C U hθ hC hU.le
  let K := D*(U+1)*(1+2*SupportProductTail.productConstant)
  have hK : 0 ≤ K := by dsimp [K,SupportProductTail.productConstant]; positivity
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  have hη : 0 < eps/(K+1) := by positivity
  filter_upwards [eventually_gt_atTop (0:ℝ),
    (harmonic_normalized U hU.le).eventually (gt_mem_nhds (show U<U+1 by linarith)),
    BareEulerUniform.ratio_uniform C U hCU _ hη] with L hL hH hr
  intro p hp
  have hb := shift_error_bound L U θ D (eps/(K+1)) P G p.1 p.2 hL hD hη.le
    (fun g hg => hprod L hL g hg p.1 p.2 hp.1 hp.2)
    (fun g hg => (hr g p.1 p.2 (mem_Ioc.mp hg).1.ne'
      ((Nat.le_floor_iff (Real.exp_pos _).le).mp (mem_Ioc.mp hg).2) hp.1 hp.2).le)
  have hcap : (eps/(K+1))*D*(SupportTail.harmonic (cutoff L U)/L)*
      (1+2*SupportProductTail.productConstant) ≤ (eps/(K+1))*K := by
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hH.le (mul_nonneg hη.le hD))
      (show 0 ≤ 1+2*SupportProductTail.productConstant by unfold SupportProductTail.productConstant; positivity)
    calc
      _ ≤ (eps/(K+1))*D*(U+1)*(1+2*SupportProductTail.productConstant) := hh
      _ = _ := by dsimp [K]; ring
  rw [dist_comm,dist_eq_norm,sub_zero]
  apply (hb.trans hcap).trans_lt
  rw [div_mul_eq_mul_div]
  exact (div_lt_iff₀ (by positivity : 0<K+1)).mpr (by nlinarith)

theorem actualSum_twoBidiscs (P G : Polynomial ℂ) (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => actualSum L PRZZAsymptotic.theta PRZZAsymptotic.theta P G p.1 p.2)
      (fun p => -BetaKernel.monomialIntegral p.1 p.2 PRZZAsymptotic.theta P G 1 1 3)
      atTop ElementaryGcd.twoBidiscs := by
  have hθ : 0 < PRZZAsymptotic.theta := by norm_num [PRZZAsymptotic.theta]
  have hC : 0 ≤ 5*PRZZAsymptotic.R/4 := by have := PRZZAsymptotic.radius_pos; positivity
  have he := (shift_error_uniform P G hP hG _ _ _ hθ hC hθ ShiftedEulerUniform.witness_size).mono
    (fun p hp => ShiftedMobius.twoBidiscs_norm p hp)
  have hm := FengMixedProduct.actualSum_twoBidiscs P G hP hG
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp he (eps/2) (by positivity),
    Metric.tendstoUniformlyOn_iff.mp hm (eps/2) (by positivity)] with L heL hmL
  intro p hp
  have hx := heL p hp
  have hy := hmL p hp
  rw [dist_comm,dist_eq_norm,sub_zero] at hx
  rw [dist_comm,dist_eq_norm] at hy ⊢
  exact (norm_sub_le_norm_sub_add_norm_sub _ (FengMixedProduct.actualSum L
    PRZZAsymptotic.theta PRZZAsymptotic.theta P G p.1 p.2) _).trans_lt (by linarith)

theorem actualSum_reflected (P G : Polynomial ℂ) (hP : P.eval 0 = 0) (hG : G.eval 0 = 0) :
    TendstoUniformlyOn
      (fun L (p : ℂ × ℂ) => actualSum L PRZZAsymptotic.theta PRZZAsymptotic.theta P G (-p.2) (-p.1))
      (fun p => -BetaKernel.monomialIntegral (-p.2) (-p.1) PRZZAsymptotic.theta P G 1 1 3)
      atTop PRZZAsymptotic.witnessBidisc :=
  ElementaryGcd.uniform_reflected (actualSum_twoBidiscs P G hP hG)

/-- Algebraic target only: the other blocks must supply the expression in
parentheses. No logBlock/outsideBlock asymptotic is inferred from this identity. -/
theorem kernel20_target (E : ℤ → ℤ → ℕ → ℂ) :
    -E 1 1 3 + (2*E 1 1 3-2*E 0 1 2+E (-1) 1 1) = BetaKernel.poleSum 2 0 E := by
  rw [BetaKernel.assemble20]
  ring

theorem kernel02_target (E : ℤ → ℤ → ℕ → ℂ) :
    -E 1 1 3 + (2*E 1 1 3-2*E 1 0 2+E 1 (-1) 1) = BetaKernel.poleSum 0 2 E := by
  rw [BetaKernel.assemble02]
  ring

#print axioms rawWeight_zero
#print axioms mixed_weight_factor
#print axioms mixed_euler_bound
#print axioms shift_error_bound
#print axioms shift_error_uniform
#print axioms actualSum_twoBidiscs
#print axioms actualSum_reflected
#print axioms kernel20_target
#print axioms kernel02_target
end XiPrime8845.FengMixedShift
