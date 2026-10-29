import CoprimeEulerCompletion
import EndpointAverage

/-! Endpoint-safe domination by the full Euler mass and its localized second
moment. No pointwise main-term convergence at u=0 is asserted. -/
noncomputable section
open scoped BigOperators
open Finset Filter Topology
namespace XiPrime8845.CoprimeEndpoint
open CoprimeEulerCompletion CoprimeApproximation ShiftedEndpoint
open ShiftedMobius WeightDerivatives SupportProductTail
set_option maxHeartbeats 1000000

theorem euler_nonneg (g : ℕ) (hg : g ≠ 0) : 0 ≤ SupportTail.eulerMass g 0 :=
  (EulerHead.mass_nonneg 0 g).trans (EulerHead.mass_le 0 g hg)

theorem full_window (M N Q : ℕ) (hMN : M ≤ N) (hQ : 0 < Q) :
    (∑ g ∈ Ioc M N, (1/(g:ℝ))*SupportTail.eulerMass g 0 ^ 2) ≤
      SupportTail.harmonic Q ^ 2*(SupportTail.harmonic N-SupportTail.harmonic M)+
        2*SupportTail.harmonic N*((Q:ℝ)^(-1/4:ℝ)*productConstant) := by
  have hlim : Tendsto (fun K => ∑ g ∈ Ioc M N, (1/(g:ℝ))*EulerHead.mass K g ^ 2)
      atTop (nhds (∑ g ∈ Ioc M N, (1/(g:ℝ))*SupportTail.eulerMass g 0 ^ 2)) := by
    apply tendsto_finsetSum
    intro g hg
    have hg0 : g ≠ 0 := by have := (mem_Ioc.mp hg).1; omega
    exact ((EulerHead.mass_tendsto g hg0).pow 2).const_mul _
  apply le_of_tendsto hlim
  exact Filter.Eventually.of_forall (fun K => EndpointAverage.window_second_moment M N K Q hMN hQ)

def productError (L : ℝ) (g : ℕ) (u v θ : ℝ) (P G : Polynomial ℂ) (A B : ℂ) : ℝ :=
  ‖actual L g u θ P A*actual L g v θ G B-
    zeroEulerMain g u θ P A*zeroEulerMain g v θ G B‖

/-- One constant controls the ACTUAL product error on the entire cutoff
interval, including zero. The Euler mass is not uniformly bounded in g. -/
theorem product_error_dominated (P G : Polynomial ℂ) (hP : P.eval 0 = 0) (hG : G.eval 0 = 0)
    (θ C U : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C) (hU : 0 ≤ U) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ L : ℝ, 0 < L → ∀ (g : ℕ), g ≠ 0 →
      ∀ u ∈ Set.Icc 0 U, ∀ v ∈ Set.Icc 0 U, ∀ A B : ℂ,
      ‖A‖ ≤ C → ‖B‖ ≤ C → productError L g u v θ P G A B ≤ D*SupportTail.eulerMass g 0 ^ 2 := by
  obtain ⟨K,hK,hbound⟩ := absoluteError_bounded
  let CP := coprimeCap P θ C U K
  let CG := coprimeCap G θ C U K
  let FP := firstCap P θ C U
  let FG := firstCap G θ C U
  have hCP : 0 ≤ CP := mul_nonneg (Real.exp_pos _).le (scaledCap_nonneg P θ C U K hθ hC hU hK)
  have hCG : 0 ≤ CG := mul_nonneg (Real.exp_pos _).le (scaledCap_nonneg G θ C U K hθ hC hU hK)
  have hFP := firstCap_nonneg P θ C U hθ hC hU
  have hFG := firstCap_nonneg G θ C U hθ hC hU
  refine ⟨CP*CG+FP*FG, add_nonneg (mul_nonneg hCP hCG) (mul_nonneg hFP hFG), ?_⟩
  intro L hL g hg u hu v hv A B hA hB
  have hE := euler_nonneg g hg
  have hx : ‖actual L g u θ P A‖ ≤ CP*SupportTail.eulerMass g 0 :=
    (scaled_coprime_common_bound P hP A g L u θ C U K hL hθ hA hu hK hbound).trans
      (mul_le_mul_of_nonneg_left (EulerHead.mass_le _ g hg) hCP)
  have hy : ‖actual L g v θ G B‖ ≤ CG*SupportTail.eulerMass g 0 :=
    (scaled_coprime_common_bound G hG B g L v θ C U K hL hθ hB hv hK hbound).trans
      (mul_le_mul_of_nonneg_left (EulerHead.mass_le _ g hg) hCG)
  have hzP : ‖zeroEulerMain g u θ P A‖ ≤ SupportTail.eulerMass g 0*FP := by
    rw [zeroEulerMain,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hE]
    exact mul_le_mul_of_nonneg_left (mainTerm_bound P A u θ C U hθ hA hu) hE
  have hzG : ‖zeroEulerMain g v θ G B‖ ≤ SupportTail.eulerMass g 0*FG := by
    rw [zeroEulerMain,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hE]
    exact mul_le_mul_of_nonneg_left (mainTerm_bound G B v θ C U hθ hB hv) hE
  unfold productError
  apply (norm_sub_le _ _).trans
  rw [norm_mul,norm_mul]
  have hxy := mul_le_mul hx hy (norm_nonneg _) (mul_nonneg hCP hE)
  have hz := mul_le_mul hzP hzG (norm_nonneg _) (mul_nonneg hE hFP)
  nlinarith [hxy,hz]

def cutoff (L U : ℝ) : ℕ := ⌊Real.exp (L*U)⌋₊

theorem harmonic_normalized (U : ℝ) (hU : 0 ≤ U) :
    Tendsto (fun L : ℝ => SupportTail.harmonic (cutoff L U)/L) atTop (nhds U) := by
  let K := |Real.eulerMascheroniConstant|+2
  have hi : Tendsto (fun L : ℝ => K/L) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using tendsto_inv_atTop_zero.const_mul K
  apply Metric.tendsto_atTop.mpr
  intro eps heps
  obtain ⟨X,hX⟩ := Metric.tendsto_atTop.mp hi eps heps
  refine ⟨max X 1, fun L hL => ?_⟩
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hL)
  have hx : 1 ≤ Real.exp (L*U) := Real.one_le_exp_iff.mpr (mul_nonneg hL0.le hU)
  have h := MobiusHarmonic.harmonicError_bound (Real.exp (L*U)) hx
  have hb : 2/Real.exp (L*U) ≤ 2 := by simpa using div_le_self (by norm_num : (0:ℝ) ≤ 2) hx
  have hr : |SupportTail.harmonic (cutoff L U)-L*U| ≤ K := by
    have he : SupportTail.harmonic (cutoff L U)-L*U =
        MobiusHarmonic.harmonicError (Real.exp (L*U))+Real.eulerMascheroniConstant := by
      simp only [MobiusHarmonic.harmonicError,Real.log_exp,cutoff,EndpointAverage.harmonic_eq_mobius]
      ring
    rw [he]
    exact (abs_add_le _ _).trans (by dsimp [K]; linarith)
  have hs := hX L ((le_max_left _ _).trans hL)
  rw [Real.dist_eq,sub_zero] at hs
  rw [Real.dist_eq]
  have he : SupportTail.harmonic (cutoff L U)/L-U =
      (SupportTail.harmonic (cutoff L U)-L*U)/L := by field_simp
  rw [he,abs_div,abs_of_pos hL0]
  exact (div_le_div_of_nonneg_right hr hL0.le).trans_lt ((le_abs_self _).trans_lt hs)

def windowEnvelope (L U delta : ℝ) (Q : ℕ) : ℝ :=
  SupportTail.harmonic Q ^ 2*(delta+4/L)+
    2*(SupportTail.harmonic (cutoff L U)/L)*((Q:ℝ)^(-1/4:ℝ)*productConstant)

theorem windowEnvelope_tendsto (U delta : ℝ) (Q : ℕ) (hU : 0 ≤ U) :
    Tendsto (fun L => windowEnvelope L U delta Q) atTop
      (nhds (SupportTail.harmonic Q ^ 2*delta+2*U*((Q:ℝ)^(-1/4:ℝ)*productConstant))) := by
  have hi : Tendsto (fun L : ℝ => 4/L) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using tendsto_inv_atTop_zero.const_mul (4:ℝ)
  simpa only [windowEnvelope,add_zero] using
    ((hi.const_add delta).const_mul (SupportTail.harmonic Q ^ 2)).add
      (((harmonic_normalized U hU).const_mul 2).mul_const ((Q:ℝ)^(-1/4:ℝ)*productConstant))

theorem endpoint_error_bound (P G : Polynomial ℂ) (θ C U D : ℝ)
    (hD : 0 ≤ D)
    (hdom : ∀ L : ℝ, 0 < L → ∀ g : ℕ, g ≠ 0 → ∀ u ∈ Set.Icc 0 U,
      ∀ v ∈ Set.Icc 0 U, ∀ A B : ℂ, ‖A‖ ≤ C → ‖B‖ ≤ C →
        productError L g u v θ P G A B ≤ D*SupportTail.eulerMass g 0 ^ 2)
    (L delta : ℝ) (Q : ℕ) (hL : 0 < L) (hd : 0 ≤ delta) (hdU : delta ≤ U)
    (hQ : 0 < Q) (A B : ℂ) (hA : ‖A‖ ≤ C) (hB : ‖B‖ ≤ C) :
    (∑ g ∈ Ioc (cutoff L (U-delta)) (cutoff L U), (1/(g:ℝ))*
      productError L g (LogProfileSum.coordinate L U g) (LogProfileSum.coordinate L U g) θ P G A B)/L ≤
        D*windowEnvelope L U delta Q := by
  have hMN : cutoff L (U-delta) ≤ cutoff L U := Nat.floor_mono
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) hL.le))
  have hw := full_window _ _ Q hMN hQ
  have hh := EndpointAverage.harmonic_log_window_bound L U delta hL.le hd hdU
  have hs : (∑ g ∈ Ioc (cutoff L (U-delta)) (cutoff L U), (1/(g:ℝ))*
      productError L g (LogProfileSum.coordinate L U g) (LogProfileSum.coordinate L U g) θ P G A B) ≤
      D*(SupportTail.harmonic Q ^ 2*(L*delta+4)+
        2*SupportTail.harmonic (cutoff L U)*((Q:ℝ)^(-1/4:ℝ)*productConstant)) := by
    calc
      _ ≤ D*∑ g ∈ Ioc (cutoff L (U-delta)) (cutoff L U), (1/(g:ℝ))*SupportTail.eulerMass g 0 ^ 2 := by
        rw [Finset.mul_sum]
        apply sum_le_sum
        intro g hg
        have hg0 : g ≠ 0 := by have := (mem_Ioc.mp hg).1; omega
        have hu := EndpointAverage.endpoint_cutoff_mem L U delta hL g hg
        have hc : LogProfileSum.coordinate L U g ∈ Set.Icc 0 U := ⟨hu.1,hu.2.trans hdU⟩
        have := mul_le_mul_of_nonneg_left (hdom L hL g hg0 _ hc _ hc A B hA hB)
          (by positivity : (0:ℝ) ≤ 1/(g:ℝ))
        nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_left (hw.trans (by
        exact add_le_add (mul_le_mul_of_nonneg_left hh (sq_nonneg _)) le_rfl)) hD
  apply (div_le_div_of_nonneg_right hs hL.le).trans_eq
  unfold windowEnvelope
  field_simp

/-- Choose the finite head first, the endpoint width second, and L last. -/
theorem endpoint_small (P G : Polynomial ℂ) (θ C U D : ℝ) (hU : 0 < U) (hD : 0 ≤ D)
    (hdom : ∀ L : ℝ, 0 < L → ∀ g : ℕ, g ≠ 0 → ∀ u ∈ Set.Icc 0 U,
      ∀ v ∈ Set.Icc 0 U, ∀ A B : ℂ, ‖A‖ ≤ C → ‖B‖ ≤ C →
        productError L g u v θ P G A B ≤ D*SupportTail.eulerMass g 0 ^ 2)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ U ∧
      ∀ᶠ L : ℝ in atTop, ∀ A B : ℂ, ‖A‖ ≤ C → ‖B‖ ≤ C →
        (∑ g ∈ Ioc (cutoff L (U-delta)) (cutoff L U), (1/(g:ℝ))*
          productError L g (LogProfileSum.coordinate L U g) (LogProfileSum.coordinate L U g) θ P G A B)/L < eps := by
  have hp : Tendsto (fun Q : ℕ => (Q:ℝ)^(-1/4:ℝ)) atTop (nhds 0) := by
    simpa only [neg_div,Function.comp_def] using
      (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/4)).comp tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun Q : ℕ => D*(2*U*((Q:ℝ)^(-1/4:ℝ)*productConstant))) atTop (nhds 0) := by
    simpa using ((hp.mul_const productConstant).const_mul (2*U)).const_mul D
  obtain ⟨Q,hQ,htail⟩ := ((eventually_gt_atTop (0:ℕ)).and
    (ht.eventually (gt_mem_nhds (show (0:ℝ) < eps/2 by positivity)))).exists
  let a := D*SupportTail.harmonic Q ^ 2+1
  have ha : 0 < a := by dsimp [a]; positivity
  let delta := min U (eps/(4*a))
  have hd : 0 < delta := lt_min hU (by positivity)
  have hdU : delta ≤ U := min_le_left _ _
  have hda : a*delta ≤ eps/4 := by
    have := mul_le_mul_of_nonneg_left (min_le_right U (eps/(4*a))) ha.le
    have he : a*(eps/(4*a)) = eps/4 := by field_simp
    exact this.trans_eq he
  have hlim : D*(SupportTail.harmonic Q ^ 2*delta+
      2*U*((Q:ℝ)^(-1/4:ℝ)*productConstant)) < eps := by
    dsimp [a] at hda
    nlinarith
  refine ⟨delta,hd,hdU,?_⟩
  filter_upwards [eventually_gt_atTop (0:ℝ),
    ((windowEnvelope_tendsto U delta Q hU.le).const_mul D).eventually (gt_mem_nhds hlim)] with L hL hsmall
  intro A B hA hB
  exact (endpoint_error_bound P G θ C U D hD hdom L delta Q hL hd.le hdU hQ A B hA hB).trans_lt hsmall

#print axioms endpoint_small
#print axioms full_window
#print axioms product_error_dominated
#print axioms harmonic_normalized
#print axioms endpoint_error_bound
end XiPrime8845.CoprimeEndpoint
